module

public import MLIR.Semantics.Effectful.Memory.Operations
public import MLIR.Memory.Range
public import MLIR.Run.Tactic.Util
public import MLIR.Run.Memory
public meta import Lean.Elab.Tactic

namespace MLIR.Tactic

open Lean Elab Tactic Meta

public meta section

/-- The conjuncts of `h : ty`, `(proof, type)` each: `h : a ∧ b ∧ c` into
`#[(h.1, a), (h.2.1, b), (h.2.2, c)]`. -/
partial def conjuncts (h ty : Expr) : MetaM (Array (Expr × Expr)) := do
  match_expr ← whnfR ty with
  | And a b =>
    return (← conjuncts (mkApp3 (mkConst ``And.left) a b h) a) ++
        (← conjuncts (mkApp3 (mkConst ``And.right) a b h) b)
  | _ =>
    return #[(h, ty)]

/-- The context's facts, conjunctions split (`conjuncts`). -/
def splitConjunctedFacts : MetaM (Array (Expr × Expr)) := do
  let mut out := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail || !(← isProp d.type) then
      continue
    out := out ++ (← conjuncts (mkFVar d.fvarId) (← instantiateMVars d.type))
  return out

/-- The context's facts by (instantiated) type. -/
def contextFactMap : MetaM (Std.HashMap Expr Expr) := do
  let mut facts : Std.HashMap Expr Expr := {}
  for d in ← getLCtx do
    if !d.isImplementationDetail then
      facts := facts.insert (← instantiateMVars d.type) d.toExpr
  return facts

/-- The type of the sides of `a = b`, `a ≠ b` or `¬a = b`. -/
def eqSideType? (p : Expr) : Option Expr :=
  let p := p.cleanupAnnotations
  match p.ne? with
  | some (α, _, _) => some α
  | none => ((p.not?.getD p).eq?).map (·.1)

def findFact? (facts : Array (Expr × Expr)) (goal : Expr) : MetaM (Option Expr) := do
  let α? := eqSideType? goal
  for (pf, ty) in facts do
    -- an equation over another type is skipped first: `isDefEq` compares the sides before their
    -- type, and would unfold `x.uaddOverflow 512#64` one by one against a `BlockId`
    if let (some α, some β) := (α?, eqSideType? ty) then
      unless ← withNewMCtxDepth (withReducible (isDefEq α β)) do
        continue
    if ← withNewMCtxDepth (withTransparency .default (isDefEq ty goal)) then
      return some pf
  return none

/-- The widths in `e` as literals (`(Ty.vec 8 64).width` is `512`), so facts and goals compare
syntactically and read lemmas unify with reducible transparency, which never unfolds the memory. -/
def normWidths (e : Expr) : MetaM Expr := do
  let thms ← ({} : SimpTheorems).addDeclToUnfold ``Ty.width
  return (←
        dsimp e (← Simp.mkContext (simpTheorems := #[thms])) (simprocs := #[← Simp.getSimprocs])).1

/-- Prove a closed fact by `decide`, pointers' offsets first replaced by their facts
(`x.offset = 0`, a stack slot's): an offset sum's `¬uaddOverflow`, a width bound. -/
def decideWithOffsets? (facts : Array (Expr × Expr)) (goal : Expr) : MetaM (Option Expr) := do
  let goal ← instantiateMVars goal
  let mut eqs : Array (Expr × Expr × Expr) := #[]
  for (pf, ty) in facts do
    let some (_, l, r) := ty.eq? | continue
    if
        l.isAppOfArity ``Pointer.offset 1 && !r.hasFVar && (goal.find? (· == l)).isSome &&
          !eqs.any (·.2.1 == l) then
      eqs := eqs.push (pf, l, r)
  -- `subst k e`: `e` with the offsets from the `k`-th on replaced by their values
  let subst (k : Nat) (e : Expr) : Expr :=
    (eqs.extract k).foldl (fun e (_, l, r) => e.replace fun t => if t == l then some r else none) e
  let goal' := subst 0 goal
  if goal'.hasFVar || goal'.hasMVar then
    return none
  let some pf ← decideProof? goal' | return none
  -- back from the values to the offsets, one at a time
  let mut pf := pf
  for k in [0:eqs.size] do
    let (h, l, _) := eqs[k]!
    let motive ← motiveOver (subst (k + 1) goal) l (← inferType l)
    pf ← mkEqNDRec motive pf (← mkEqSymm h)
  return some (mkExpectedPropHint pf goal)

/-- `¬q.offset.uaddOverflow off` from a fact `¬q.offset.uaddOverflow c` for a literal `c` at least
`off`. -/
def noOverflowOfFact? (facts : Array (Expr × Expr)) (q off : Expr) : MetaM (Option Expr) := do
  let qo ← mkAppM ``Pointer.offset #[q]
  for (pf, ty) in facts do
    let some (_, l, r) := ty.cleanupAnnotations.not? >>= (·.eq?) | continue
    let_expr BitVec.uaddOverflow _ x c := l | continue
    unless r.isConstOf ``Bool.true && x == qo do
      continue
    let hle ← mkAppM ``LE.le #[← mkAppM ``BitVec.toNat #[off], ← mkAppM ``BitVec.toNat #[c]]
    let some hle ← decideWithOffsets? facts hle | continue
    return some (← mkAppM ``BitVec.not_uaddOverflow_of_le #[pf, hle])
  return none

/-- `¬q.offset.uaddOverflow off = true`. -/
def noOverflowGoal (q off : Expr) : MetaM Expr := do
  return mkNot
      (←
        mkEq (← mkAppM ``BitVec.uaddOverflow #[← mkAppM ``Pointer.offset #[q], off])
            (mkConst ``Bool.true))

/-- `w` bits at `q.add off` inside `v` bits at `q`: the offset does not wrap (by the offsets'
values, or a no-overflow fact for a larger offset), and `off.toNat * 8 + w ≤ v`. -/
def addWithin? (facts : Array (Expr × Expr)) (q off w v : Expr) : MetaM (Option (Expr × Expr)) := do
  let hov? ←
    match ← decideWithOffsets? facts (← noOverflowGoal q off) with
    | some h =>
      pure (some h)
    | none =>
      noOverflowOfFact? facts q off
  let some hov := hov? | return none
  let off8 ← mkAppM ``HMul.hMul #[← mkAppM ``BitVec.toNat #[off], mkNatLit 8]
  let some hw ←
    decideWithOffsets? facts (← mkAppM ``LE.le #[← mkAppM ``HAdd.hAdd #[off8, w], v]) | return none
  return some (hov, hw)

/-- Prove `Fits m p w`: a fact with the same `m` and `p`, and the same width as a literal
(`(Ty.vec 8 64).width` is `512`); not `isDefEq` on `Fits` itself, which unfolds the memory. An
offset `q.add off` fits inside a fact for `q` (`Fits.add_of_le`) if `q.offset + off` does not wrap:
by `q.offset`'s value, or a no-overflow fact for a larger offset. -/
partial def fitsProof? (facts : Array (Expr × Expr)) (m p w : Expr) : MetaM (Option Expr) := do
  let w₁ ← normWidths w
  for (pf, ty) in facts do
    let_expr Fits m' p' w' := ty | continue
    unless m' == m && p' == p do
      continue
    if w' == w || w' == w₁ || (← normWidths w') == w₁ then
      return some (mkExpectedPropHint pf (← mkAppM ``Fits #[m, p, w]))
  -- a wider fact, both widths literals
  if let some n := w₁.nat? then
    for (pf, ty) in facts do
      let_expr Fits m' p' w' := ty | continue
      unless m' == m && p' == p do
        continue
      let w' ← normWidths w'
      let some n' := w'.nat? | continue
      if n ≤ n' then
        let hw ← mkDecideProof (← mkAppM ``LE.le #[w₁, w'])
        return some
            (mkExpectedPropHint (← mkAppM ``Fits.mono #[hw, pf]) (← mkAppM ``Fits #[m, p, w]))
  if let some (q, off) := p.app2? ``Pointer.add then
    for (pf, ty) in facts do
      let_expr Fits m' q' v := ty | continue
      unless m' == m && q' == q do
        continue
      let some (hov, hw) ← addWithin? facts q off w₁ (← normWidths v) | continue
      return some (← mkAppOptM ``Fits.add_of_le #[none, none, none, none, off, hov, hw, pf])
  -- If not found directly, go through `Fits.storeAt`
  let_expr MemoryState.storeAt m' q _ x := m | return none
  let some h ← fitsProof? facts m' p w | return none
  return some (← mkAppOptM ``Fits.storeAt #[m', p, w, q, none, x, h])

/-- Prove `p = q` by the `lem ..prems` -/
def proveEqBy? (lem : Name) (p q : Expr) (prems : List Expr) : MetaM (Option Expr) :=
  withTransparency .default do
    let c ← mkConstWithFreshMVarLevels lem
    let (args, bis, ty) ← forallMetaTelescopeReducing (← inferType c)
    unless ← isDefEq ty (← mkEq p q) do
      return none -- Lemma does not match `p` and `q`
    let explicit := (args.zip bis).filter (·.2.isExplicit) |>.map (·.1) -- Only explicit arguments
    for (a, pr) in explicit.toList.zip prems do
      unless ← isDefEq a pr do
        return none -- Premise does not match
    let r ← instantiateMVars (mkAppN c args)
    return if r.hasExprMVar then none /-Did not unify :(-/ else some r

/-- Close with omega -/
def omegaFromFacts (facts : Array (Expr × Expr)) (g : MVarId) : MetaM Unit := do
  -- Evaluate numerals, omega needs that
  let norm ← Simp.mkContext
  let facts' ←
    facts.toList.mapM fun (pf, ty) => do
        let (r, _) ← simp ty norm (simprocs := #[← Simp.getSimprocs])
        match r.proof? with
        | some h =>
          mkEqMP h pf
        | none =>
          pure pf
  -- as the `omega` tactic does: prove `False` from the negated goal
  let some g3 ← g.falseOrByContra | return
  g3.withContext do
      Lean.Elab.Tactic.Omega.omega (facts' ++ (← getLocalHyps).toList) g3

/-- `(b, k)` for a state whose counter is the local `b`'s plus `k`: `b` after `alloca`s, or a state
literal over `b`'s counter (`⟨b.alloc.nextFreeBlock + 1 + 1⟩`, `b.alloc`). -/
partial def counterBase? (s : Expr) : Option (Expr × Nat) :=
  if s.isFVar then some (s, 0)
  else
    if s.isAppOfArity ``GlobalState.alloca 2 then
      (counterBase? s.appFn!.appArg!).map fun (b, k) => (b, k + 1)
    else if s.isAppOfArity ``GlobalState.mk 2 then allocBase? s.appFn!.appArg! else none
where
  /-- An `AllocState`: `⟨n⟩`, or a state's `alloc`. -/
  allocBase? (a : Expr) : Option (Expr × Nat) :=
    if a.isAppOfArity ``AllocState.mk 1 then natBase? a.appArg!
    else if a.isAppOfArity ``GlobalState.alloc 1 then counterBase? a.appArg! else none
  /-- A counter: `a.nextFreeBlock` plus literals. -/
  natBase? (n : Expr) : Option (Expr × Nat) := do
    if n.isAppOfArity ``AllocState.nextFreeBlock 1 then
      allocBase? n.appArg!
    else
      guard (n.isAppOfArity ``HAdd.hAdd 6)
      let (b, k) ← natBase? n.appFn!.appArg!
      let j ← n.appArg!.nat? <|> n.appArg!.rawNatLit?
      return (b, k + j)

/-- `s.allocaPtr` as `b.slot k` (`counterBase?`), equal by `rfl`. -/
def slotPtr? (p : Expr) : Option Expr := do
  guard (p.isAppOfArity ``GlobalState.allocaPtr 1)
  let (b, k) ← counterBase? p.appArg!
  return mkApp2 (mkConst ``GlobalState.slot) b (mkNatLit k)

/-- `a ≠ b` from the facts: either way round, by a `[…].Nodup`, or by `decide` for closed terms
(on locals it would only unfold them). -/
partial def neProof? (facts : Array (Expr × Expr)) (a b : Expr) : MetaM (Option Expr) := do
  -- `(p.add k).id` is `p.id`: an offset stays in its block
  let rec strip (e : Expr) : Expr :=
    match e.app1? ``Pointer.id with
    | some p =>
      match p.app2? ``Pointer.add with
      | some (q, _) => strip (mkApp (mkConst ``Pointer.id) q)
      | none => e
    | none => e
  let (a', b') := (strip a, strip b)
  if a' != a || b' != b then
    if let some pf← neProof? facts a' b' then
      return some (mkExpectedPropHint pf (← mkAppM ``Ne #[a, b]))
    return none
  let ne ← mkAppM ``Ne #[a, b]
  if let some h← findFact? facts ne then
    return some h
  if let some h← findFact? facts (← mkAppM ``Ne #[b, a]) then
    return some (← mkAppM ``Ne.symm #[h])
  for (h, ty) in facts do
    if let some h← nodupNe? h ty a b then
      return some h
  if ne.hasFVar then
    return none
  decideProof? ne

/-- `(Range.of p v).Disjoint (Range.of q w)`; by offsets in one block (`omega`) only if
`offsets`. -/
def disjointProof? (facts : Array (Expr × Expr)) (p v q w : Expr) (offsets := true) :
    MetaM (Option Expr) := do
  let goal ← mkAppM ``Range.Disjoint #[← mkAppM ``Range.of #[p, v], ← mkAppM ``Range.of #[q, w]]
  -- different blocks
  let pid ← mkAppM ``Pointer.id #[p]
  let qid ← mkAppM ``Pointer.id #[q]
  if let some h← neProof? facts pid qid then
    return some (mkAppN (mkConst ``Range.disjoint_of_id_ne) #[p, q, v, w, h])
  -- the same block: offsets, by `omega`
  unless offsets do
    return none
  let g ← mkFreshExprMVar goal
  try
    -- simp with these facts and extract the remaining goal if there is one left over.
    -- Otherwise just return the closed goal.
    let some g' ←
      (do
          let mut thms : SimpTheorems := {}
          for n in [``Range.Disjoint, ``Range.of, ``Pointer.offsetInBits, ``Pointer.add] do
            thms ← thms.addDeclToUnfold n
          for n in [``BitVec.toNat_add, ``BitVec.toNat_ofNat] do
            thms ← thms.addConst n
          let ctx ← Simp.mkContext (simpTheorems := #[thms])
          let (r, _) ← simpGoal g.mvarId! ctx (simprocs := #[← Simp.getSimprocs])
          pure (r.map (·.2))) | return some (← instantiateMVars g)
    let [g''] ←
      g'.apply
          (mkConst
            ``Or.inr) | return none -- `right` tactic, we want to show the same block side of `Disjoint`
    omegaFromFacts facts g''
    return some (← instantiateMVars g)
  catch _ =>
    return none

simproc_decl readThroughStore (MemoryState.readAt (MemoryState.storeAt _ _ _) _ _) := fun e => do
  let_expr MemoryState.readAt mm q w := e | return .continue
  let_expr MemoryState.storeAt m p v x := mm | return .continue
  let facts ← splitConjunctedFacts
  -- read back from write
  if ← isDefEq p q <&&> isDefEq v w then
    if let some hf← fitsProof? facts m p w then
      if let some pf← proveEqBy? ``MemoryState.readAt_storeAt_self e x [hf] then
        return .visit { expr := x, proof? := some pf }
  -- Disjoint writes
  if let some hd← disjointProof? facts p v q w then
    let r ← mkAppM ``MemoryState.readAt #[m, q, w]
    if let some pf← proveEqBy? ``MemoryState.readAt_storeAt_disjoint e r [hd] then
      return .visit { expr := r, proof? := pf }
  return .continue

/-- `¬p.offset.uaddOverflow off`: unfold `uaddOverflow`, then `omega` from the facts. -/
def noOverflowProof? (facts : Array (Expr × Expr)) (p off : Expr) : MetaM (Option Expr) := do
  let g ← mkFreshExprMVar (← noOverflowGoal p off)
  try
    -- `Pointer.add` too, so `omega` sees a moved pointer's offset through its base's
    let thms ← (← getSimpTheorems).addDeclToUnfold ``BitVec.uaddOverflow
    let thms ← thms.addDeclToUnfold ``Pointer.add
    let thms ← thms.addConst ``BitVec.toNat_add
    let ctx ← Simp.mkContext (simpTheorems := #[← thms.addConst ``BitVec.toNat_ofNat])
    let (r, _) ← simpGoal g.mvarId! ctx (simprocs := #[← Simp.getSimprocs])
    if let some (_, g') := r then
      omegaFromFacts facts g'
    return some (← instantiateMVars g)
  catch _ =>
    return none

/-- `gep` of a pointer and an offset that does not wrap is `.value (p.add off)`. -/
simproc_decl gepValue (Operation.gep (.value _) (.value _)) := fun e => do
  let_expr Operation.gep bo pp := e | return .continue
  let_expr PoisonOr.value _ off := bo | return .continue
  let_expr PoisonOr.value _ p := pp | return .continue
  let facts ← splitConjunctedFacts
  -- a stack slot's offset by its fact, a bound for a larger offset, else bounds by `omega`
  let some h ←
    (do
        if let some h← decideWithOffsets? facts (← noOverflowGoal p off) then
          return some h
        if let some h← noOverflowOfFact? facts p off then
          return some h
        noOverflowProof? facts p off) | return .continue
  return .visit
      { expr := ← mkAppM ``PoisonOr.value #[← mkAppM ``Pointer.add #[p, off]],
        proof? := ← mkAppM ``gep_value #[h] }

/-- The new state with its projections reduced -/
def dsimpState (e : Expr) : MetaM Expr := do
  return (← dsimp e (← Simp.mkContext)).1

/-- `transportDischarge`'s search, with the context's facts by (instantiated) type. -/
partial def transportWith (facts : Std.HashMap Expr Expr) (lemmas : Array Name) (fuel : Nat)
    (p : Expr) : MetaM (Option Expr) := do
  if let some h := facts[p]? then
    return some h
  if fuel = 0 then
    return none
  for n in lemmas do
    let saved ← saveState
    let m ← mkFreshExprMVar p
    let pf? ←
      (do
            let gs ← withReducible (m.mvarId!.apply (← mkConstWithFreshMVarLevels n))
            for g in gs do
              if ← g.isAssigned then
                continue
              let some pf ←
                transportWith facts lemmas (fuel - 1)
                    (← instantiateMVars (← g.getType)) | return none
              g.assign pf
            return some (← instantiateMVars m)) <|>
          pure none
    if pf?.isSome then
      return pf?
    restoreState saved
  -- a fact equal only up to reducible unfolding
  return (← withReducible (findLocalDeclWithType? p)).map mkFVar

/-- An `mlir_read` lemma: its name, the read it rewrites (the left side's head) and the write it
reads through (the head of the left side's application argument). -/
structure ReadLemma where
  name : Name
  read : Name
  write : Name
  /-- The left side, its arguments open: a key for the read. -/
  lhs : Expr

/-- The `mlir_read` lemmas, each telescoped once. -/
def readLemmas : MetaM (Array ReadLemma) := do
  let mut ls := #[]
  for n in ← labelled `mlir_read do
    let (_, _, concl) ← forallMetaTelescopeReducing (← inferType (← mkConstWithFreshMVarLevels n))
    let some (_, l, _) := concl.eq? | continue
    let some read := l.getAppFn.constName? | continue
    let some w := l.getAppArgs.find? (·.isApp) | continue
    let some write := w.getAppFn.constName? | continue
    ls := ls.push { name := n, read, write, lhs := l }
  return ls

/-- The read functions of the lemmas `ls`, each once. -/
def ReadLemma.heads (ls : Array ReadLemma) : Array Name :=
  ls.foldl (fun hs l => if hs.contains l.read then hs else hs.push l.read) #[]

/-- The read functions of the `mlir_read` lemmas. -/
def readHeads : MetaM (Array Name) := do
  return ReadLemma.heads (← readLemmas)

/-- A read fact `read (s.mem) … = x` of the state `s`: a registered read with `s.mem` an
argument. -/
def memReadFact? (heads : Array Name) (s ty : Expr) : Option (Expr × Expr) := do
  let (_, l, x) ← ty.eq?
  let h ← l.getAppFn.constName?
  guard (heads.contains h)
  guard (l.getAppArgs.any fun a => a.isAppOfArity ``GlobalState.mem 1 && a.appArg! == s)
  return (l, x)

/-- What reading through memory needs, gathered once (per step, per `simp` call): the read and
transport lemmas, the context's facts (split, and by type), its read facts by their left side,
widths as literals, and its named slots. -/
structure MemCtx where
  lemmas : Array ReadLemma
  heads : Array Name
  transport : Array Name
  facts : Array (Expr × Expr)
  factMap : Std.HashMap Expr Expr
  /-- `read (S.mem) … ↦ (x, h : read (S.mem) … = x)`, for the locals `S`. -/
  reads : Std.HashMap Expr (Expr × Expr)
  /-- `b.slot k ↦ (x, hx : x = b.slot k)`, for the named slots `x`. -/
  slots : Std.HashMap Expr (Expr × Expr)
  /-- `S.mem ↦ (hS, s.mem)` for `hS : S = s`, filled by `readThroughState`. -/
  mems : IO.Ref (Std.HashMap Expr (Option (FVarId × Expr)))

def MemCtx.build : MetaM MemCtx := do
  let lemmas ← readLemmas
  let heads := ReadLemma.heads lemmas
  let mut reads := {}
  let mut slots := {}
  for e in ← localEqs do
    if e.lhs.isFVar && e.rhs.isAppOfArity ``GlobalState.slot 2 then
      unless slots.contains e.rhs do
        slots := slots.insert e.rhs (e.lhs, ← mkExpectedTypeHint e.decl.toExpr e.type)
      continue
    unless heads.any e.lhs.isAppOf do
      continue
    unless e.lhs.getAppArgs.any fun a => a.isAppOfArity ``GlobalState.mem 1 && a.appArg!.isFVar do
      continue
    reads := reads.insert (← normWidths e.lhs) (e.rhs, e.decl.toExpr)
  return { lemmas, heads, transport := ← labelled `mlir_transport, facts := ← splitConjunctedFacts,
           factMap := ← contextFactMap, reads, slots, mems := ← IO.mkRef {} }

/-- `a ≠ b` for block ids `p.id` of slots spelled by their state (`(S.alloca n).allocaPtr`): by the
facts about the named slots `x` they are. -/
def neBySlots? (c : MemCtx) (a b : Expr) : MetaM (Option Expr) := do
  let side (e : Expr) : Option (Expr × Expr) := do
    let p ← e.app1? ``Pointer.id
    guard !p.isFVar
    c.slots[← slotPtr? p]?
  let sa := side a
  let sb := side b
  if sa.isNone && sb.isNone then
    return none
  let a' := sa.elim a fun (x, _) => mkApp (mkConst ``Pointer.id) x
  let b' := sb.elim b fun (x, _) => mkApp (mkConst ``Pointer.id) x
  let some pf ← neProof? c.facts a' b' | return none
  -- back along each `hx : x = s`, `s` the slot as `p` is, up to `rfl`
  let slotId (h : Expr) : MetaM Expr := do
    let some (_, _, s) := (← inferType h).eq? | throwError "not an equation"
    return mkApp (mkConst ``Pointer.id) s
  let rewrite (pf hx : Expr) (side : Expr → Expr) : MetaM Expr := do
    let motive ←
      withLocalDeclD `y (mkConst ``Pointer) fun y => do
          mkLambdaFVars #[y] (mkNot (side (mkApp (mkConst ``Pointer.id) y)))
    mkEqNDRec motive pf hx
  let mut pf := pf
  let mut a'' := a'
  if let some (_, hx) := sa then
    pf ← rewrite pf hx fun y => mkApp3 (mkConst ``Eq [1]) (mkConst ``BlockId) y b'
    a'' ← slotId hx
  if let some (_, hx) := sb then
    pf ← rewrite pf hx fun y => mkApp3 (mkConst ``Eq [1]) (mkConst ``BlockId) a'' y
  return some (← mkExpectedTypeHint pf (mkNot (← mkEq a b)))

/-- A read lemma's side condition from the facts: `Fits` and separation directly, others (limbs
fitting) through `mlir_transport` lemmas. -/
def dischargeRead (c : MemCtx) (goal : Expr) : MetaM (Option Expr) := do
  let goal ← instantiateMVars goal
  if let some pf := c.factMap[goal]? then
    return some pf
  match_expr goal with
  | Fits m p w =>
    if let some pf← fitsProof? c.facts m p w then
      return some pf
    -- a width only this premise mentions (`readAt_alloca`'s), bound by a fact
    transportWith c.factMap c.transport 4 goal
  | Range.Disjoint a b =>
    let_expr Range.of p v := a | return none
    let_expr Range.of q w := b | return none
    disjointProof? c.facts p v q w (offsets := false)
  | Ne _ a b =>
    if let some pf← neProof? c.facts a b then
      return some pf
    neBySlots? c a b
  | _ =>
    -- closed side conditions: an offset's `¬uaddOverflow`, a width bound
    if let some pf← decideWithOffsets? c.facts goal then
      return some pf
    transportWith c.factMap c.transport 4 goal

/-- One `mlir_read` lemma on the read `e`: a stored value (`true`), or the read past a write, with
the proof of `e = _`. Only lemmas for `e`'s read and write are tried. -/
def readStep (c : MemCtx) (e : Expr) : MetaM (Option (Bool × Expr × Expr)) := do
  let writes := e.getAppArgs.filterMap (·.getAppFn.constName?)
  for l in c.lemmas do
    unless e.isAppOf l.read && writes.contains l.write do
      continue
    let saved ← saveState
    let lem ← mkConstWithFreshMVarLevels l.name
    let (ms, _, concl) ← forallMetaTelescopeReducing (← inferType lem)
    let some (_, lhs, rhs) := concl.eq? | continue
    if ← withReducible (isDefEq lhs e) then
      let mut ok := true
      -- the premises; a value only they mention (`readAt_alloca`'s fitting width) bound by them
      for m in ms do
        if ← m.mvarId!.isAssigned then
          continue
        let ty ← instantiateMVars (← inferType m)
        unless ← isProp ty do
          continue
        let some pf ← dischargeRead c ty |
          ok := false;
          break
        m.mvarId!.assign pf
      if ok then
        ok ← ms.allM (·.mvarId!.isAssigned)
      if ok then
        -- past a write when the right side reads again
        return some
            (!rhs.isAppOf l.read, ← instantiateMVars rhs, ← instantiateMVars (mkAppN lem ms))
    restoreState saved
  return none

/-- `e = r` for a read `e`, through the writes the read lemmas pass: `r` a stored value, or the
read below the writes. -/
partial def readThrough (c : MemCtx) (e : Expr) : MetaM (Expr × Expr) := do
  match ← readStep c e with
  | some (true, v, pf) =>
    return (v, pf)
  | some (false, e', pf) =>
    let (v, pf') ← readThrough c e'
    return (v, ← mkEqTrans pf pf')
  | none =>
    return (e, ← mkEqRefl e)

/-- The writes of the memory `m`, outermost first: each with the memory it writes over (its first
`MemoryState` argument). -/
partial def writesOf (m : Expr) (acc : Array Expr := #[]) : MetaM (Array Expr) := do
  for a in m.getAppArgs do
    if (← inferType a).isConstOf ``MemoryState then
      return ← writesOf a (acc.push m)
  return acc

/-- `fun s => e` with the memory `m` as `s.mem`: a fact about a state's memory, as a motive over
the state. -/
def memMotive (e m : Expr) : MetaM Expr :=
  motiveOver e m (mkConst ``GlobalState) (mkApp (mkConst ``GlobalState.mem))

/-- The `S.mem` argument of a registered read, `S` a local. -/
def stateMemArg? (c : MemCtx) (e : Expr) : Option Expr := do
  guard (c.heads.any e.isAppOf)
  e.getAppArgs.find? fun a => a.isAppOfArity ``GlobalState.mem 1 && a.appArg!.isFVar

/-- A registered read of `S.mem` by its read fact, widths compared as literals: before `hS`
unfolds `S`. -/
def readMemFact (c : MemCtx) : Simp.Simproc := fun e => do
  if (stateMemArg? c e).isNone then
    return .continue
  let e' ← normWidths e
  if let some (x, h) := c.reads[e']? then
    return .visit { expr := x, proof? := some (mkExpectedPropHint h (← mkEq e x)) }
  -- inside a known read: `S.mem.readAt (q.add off) w` from `S.mem.readAt q v = x`
  let_expr MemoryState.readAt m p w := e' | return .continue
  let some (q, off) := p.app2? ``Pointer.add | return .continue
  for (l, x, h) in c.reads.toArray.map fun (l, (x, h)) => (l, x, h) do
    let_expr MemoryState.readAt m' q' v := l | continue
    unless m' == m && q' == q do
      continue
    let some hfits ← fitsProof? c.facts m q v | continue
    let some (hov, hw) ← addWithin? c.facts q off w v | continue
    let pf ← mkAppM ``MemoryState.readAt_add_of_readAt #[hfits, hov, hw, h]
    let some (_, _, r) := (← inferType pf).eq? | continue
    return .visit { expr := r, proof? := some (mkExpectedPropHint pf (← mkEq e r)) }
  return .continue

/-- A registered read of `S.mem` without a fact, through the writes of `S`'s equation `hS : S = s`
by the `mlir_read` lemmas: kept when it resolves, to a stored value or a read below every write.
`S`'s equation and memory are looked up once per `S` (`c.mems`). -/
def readThroughState (c : MemCtx) : Simp.Simproc := fun e => do
  let some m := stateMemArg? c e | return .continue
  let mem? ←
    match (← c.mems.get)[m]? with
    | some mem? =>
      pure mem?
    | none =>
      let mem? ←
        do
          let some hS ← findLocalEq? m.appArg! m!"" | pure none
          pure
              (some
                (hS.decl.fvarId,
                  ← normWidths (← dsimpState (← mkAppM ``GlobalState.mem #[hS.rhs]))))
      c.mems.modify (·.insert m mem?)
      pure mem?
  let some (hS, sMem) := mem? | return .continue
  let e' := e.replace fun t => if t == m then some sMem else none
  let (v, pf) ← readThrough c e'
  if v == e' || (v.find? (· == sMem)).isSome then
    return .continue
  -- `e = e'` by `hS`, `e'`'s memory `s.mem` up to `dsimp` and widths
  let h₁ := mkExpectedPropHint (← mkCongrArg (← memMotive e m) (.fvar hS)) (← mkEq e e')
  return .visit { expr := v, proof? := some (← mkEqTrans h₁ pf) }

/-- `readMemFact` and `readThroughState` for one `simp` call, keyed on the registered reads. -/
def memSimprocs (c : MemCtx) : MetaM Simp.Simprocs := do
  let mut procs : Simp.Simprocs := {}
  for h in c.heads do
    let some l := c.lemmas.find? (·.read == h) | continue
    -- `read _ … _`: the lemma's left side with its arguments open
    let args ←
      l.lhs.getAppArgs.mapM fun a => do
          mkFreshExprMVar (← inferType a)
    let keys ← DiscrTree.mkPath (mkAppN l.lhs.getAppFn args)
    procs := procs.addCore keys `readMemFact false (.inl (readMemFact c))
    procs := procs.addCore keys `readThroughState true (.inl (readThroughState c))
  return procs

end

end MLIR.Tactic
