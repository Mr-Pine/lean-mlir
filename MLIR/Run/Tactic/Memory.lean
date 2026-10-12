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
  -- a new block's pointers: offset `0` by `rfl`
  let zero := mkApp2 (mkConst ``BitVec.ofNat) (mkNatLit 64) (mkNatLit 0)
  let slots ← IO.mkRef (#[] : Array Expr)
  goal.forEachWhere
      (fun e =>
        e.isAppOfArity ``Pointer.offset 1 &&
          (e.appArg!.isAppOf ``GlobalState.allocaPtr || e.appArg!.isAppOf ``GlobalState.slot))
      fun e => slots.modify fun a => if a.contains e then a else a.push e
  for l in (← slots.get).filter fun l => !eqs.any (·.2.1 == l) do
    eqs := eqs.push (mkExpectedPropHint (← mkEqRefl zero) (← mkEq l zero), l, zero)
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

/-- Whether `ty` relates two naturals: `≤`, `<`, `=` or `≠`. -/
def isNatRel (ty : Expr) : Bool :=
  let ty := ty.cleanupAnnotations
  let nat (α : Expr) := α.isConstOf ``Nat
  if ty.isAppOfArity ``LE.le 4 || ty.isAppOfArity ``LT.lt 4 then nat (ty.getArg! 0)
  else
    match ty.ne? with
    | some (α, _, _) => nat α
    | none => ((ty.not?.getD ty).eq?).any (nat ·.1)

/-- A relation of naturals (`isNatRel`): by `decide` when closed, else by `omega` from `extra` and
the facts of that kind about its locals and theirs (`j < 256` for `2 * j ≤ 512`), literals' `toNat`
evaluated. -/
def natArith? (facts : Array (Expr × Expr)) (goal : Expr) (extra : Array Expr := #[]) :
    MetaM (Option Expr) := do
  let goal ← instantiateMVars goal
  unless isNatRel goal && !goal.hasMVar do
    return none
  if !goal.hasFVar then
    return ← decideProof? goal
  -- the facts about its locals, then about theirs (`8 * k ≤ len.toNat` brings `len`'s bound)
  let mut fvs := (collectFVars {} goal).fvarIds
  let mut hyps : Array Expr := #[]
  let mut used : Array Nat := #[]
  for _ in [0:2] do
    let mut more := #[]
    for h : j in [0:facts.size] do
      let (pf, ty) := facts[j]
      if !used.contains j && isNatRel ty && ty.hasAnyFVar fvs.contains then
        used := used.push j
        hyps := hyps.push pf
        more := more.push ty
    fvs := more.foldl (fun fvs ty => fvs ++ (collectFVars {} ty).fvarIds) fvs
  -- nothing bounds its locals: no proof
  if hyps.isEmpty && extra.isEmpty then
    return none
  let ctx ←
    Simp.mkContext
      (simpTheorems := #[← ({} : SimpTheorems).addConst ``BitVec.toNat_ofNat])
  let simprocs := #[← Simp.getSimprocs]
  let g ← mkFreshExprMVar goal
  try
    -- no progress is an error of `simpGoal`: the goal as it is
    let r ←
      try
        pure (← simpGoal g.mvarId! ctx (simprocs := simprocs)).1
      catch _ =>
        pure (some (#[], g.mvarId!))
    if let some (_, g') := r then
      let hs ←
        (extra ++ hyps).mapM fun h => do
            let (r, _) ← simp (← inferType h) ctx (simprocs := simprocs)
            return ← r.proof?.elim (pure h) (mkEqMP · h)
      let omegaOn (g : MVarId) : MetaM Unit := do
        let some g' ← g.falseOrByContra | throwError "no goal"
        g'.withContext do
            let neg := (← getLCtx).lastDecl.map (·.toExpr)
            Lean.Elab.Tactic.Omega.omega (hs.toList ++ neg.toList) g'
      -- `t % 2 ^ 64` as `t` where `omega` shows `t < 2 ^ 64`: with the `%` left in, `omega`
      -- (no dark shadows) misses `2 * i % 2 ^ 64 * 8 ≤ 4080` for `i < 256`
      let modCtx ←
        Simp.mkContext (simpTheorems := #[← ({} : SimpTheorems).addConst ``Nat.mod_eq_of_lt])
      let disch : Simp.Discharge := fun p => do
        let m ← mkFreshExprMVar p
        try
          omegaOn m.mvarId!
          let pf ← instantiateMVars m
          return if pf.hasMVar then none else some pf
        catch _ =>
          return none
      let g' ←
        try
          match (← simpGoal g' modCtx (discharge? := disch)).1 with
          | some (_, g'') => pure (some g'')
          | none => pure none
        catch _ =>
          pure (some g')
      if let some g' := g' then
        omegaOn g'
    let pf ← instantiateMVars g
    return if pf.hasMVar then none else some pf
  catch _ =>
    return none

/-- `¬q.offset.uaddOverflow off` from a fact `¬q.offset.uaddOverflow c` for a literal `c` at least
`off` (`off ≤ c` by `decide`, else `natArith?`). -/
def noOverflowOfFact? (facts : Array (Expr × Expr)) (q off : Expr) : MetaM (Option Expr) := do
  let qo ← mkAppM ``Pointer.offset #[q]
  for (pf, ty) in facts do
    -- `¬x.uaddOverflow c = true`, or as `simp` leaves it, `x.uaddOverflow c = false`
    let ty := ty.cleanupAnnotations
    let some (pf, l, r) :=
        (do
            let (_, l, r) ← ty.not? >>= (·.eq?)
            guard (r.isConstOf ``Bool.true)
            return (pf, l, r)) <|>
          (do
            let (_, l, r) ← ty.eq?
            guard (r.isConstOf ``Bool.false)
            return (mkApp2 (mkConst ``Bool.ne_true_of_eq_false) l pf, l, r)) | continue
    let _ := r
    let_expr BitVec.uaddOverflow _ x c := l | continue
    unless x == qo do
      continue
    let hle ← mkAppM ``LE.le #[← mkAppM ``BitVec.toNat #[off], ← mkAppM ``BitVec.toNat #[c]]
    let some hle ←
      (do
          if let some h← decideWithOffsets? facts hle then
            return some h
          natArith? facts hle) | continue
    return some (← mkAppM ``BitVec.not_uaddOverflow_of_le #[pf, hle])
  return none

/-- `¬q.offset.uaddOverflow off = true`. -/
def noOverflowGoal (q off : Expr) : MetaM Expr := do
  return mkNot
      (←
        mkEq (← mkAppM ``BitVec.uaddOverflow #[← mkAppM ``Pointer.offset #[q], off])
            (mkConst ``Bool.true))

/-- `¬q.offset.uaddOverflow off` for a variable `off` from `q`'s offset `c` (a fact `q.offset = c`,
or `0` for a new block's pointer): `c.toNat + off.toNat < 2 ^ 64` by `natArith?`. -/
def noOverflowOfOffset? (facts : Array (Expr × Expr)) (q off : Expr) : MetaM (Option Expr) := do
  let qo ← mkAppM ``Pointer.offset #[q]
  let zero := mkApp2 (mkConst ``BitVec.ofNat) (mkNatLit 64) (mkNatLit 0)
  let known? : Option (Option Expr × Expr) :=
    if q.isAppOf ``GlobalState.allocaPtr || q.isAppOfArity ``GlobalState.slot 2 then
      some (none, zero)
    else
      facts.findSome? fun (pf, ty) =>
        (ty.eq?).bind fun (_, l, r) => if l == qo && !r.hasFVar then some (some pf, r) else none
  let some (pf?, c) := known? | return none
  let pf ← pf?.getDM (return mkExpectedPropHint (← mkEqRefl zero) (← mkEq qo zero))
  let lt ← mkAppM ``LT.lt #[← mkAppM ``HAdd.hAdd #[← mkAppM ``BitVec.toNat #[c],
    ← mkAppM ``BitVec.toNat #[off]], mkNatLit (2 ^ 64)]
  let some hlt ← natArith? facts lt | return none
  return some (← mkAppM ``Pointer.not_uaddOverflow_of_offset_eq #[pf, hlt])

/-- `w` bits at `q.add off` inside `v` bits at `q`: the offset does not wrap (by the offsets'
values, or a no-overflow fact for a larger offset), and `off.toNat * 8 + w ≤ v` (by `decide`, else
`natArith?`: a variable offset `2 * j` with `j < 256`). -/
def addWithin? (facts : Array (Expr × Expr)) (q off w v : Expr) : MetaM (Option (Expr × Expr)) := do
  let hov? ←
    match ← decideWithOffsets? facts (← noOverflowGoal q off) with
    | some h =>
      pure (some h)
    | none =>
      match ← noOverflowOfFact? facts q off with
      | some h => pure (some h)
      | none => noOverflowOfOffset? facts q off
  let some hov := hov? | return none
  let off8 ← mkAppM ``HMul.hMul #[← mkAppM ``BitVec.toNat #[off], mkNatLit 8]
  let hwTy ← mkAppM ``LE.le #[← mkAppM ``HAdd.hAdd #[off8, w], v]
  let some hw ←
    (do
        if let some h← decideWithOffsets? facts hwTy then
          return some h
        natArith? facts hwTy) | return none
  return some (hov, hw)

/-- `goal` by the lemma `lem`, its explicit premises `prems` (the rest by unifying with `goal`). -/
def proveBy? (lem : Name) (goal : Expr) (prems : Array Expr) : MetaM (Option Expr) := do
  let c ← mkConstWithFreshMVarLevels lem
  let (ms, bis, ty) ← forallMetaTelescopeReducing (← inferType c)
  unless ← withReducible (isDefEq ty goal) do
    return none
  let explicit := (ms.zip bis).filter (·.2.isExplicit) |>.map (·.1)
  for (m, p) in explicit.zip prems do
    unless ← isDefEq m p do
      return none
  let pf ← instantiateMVars (mkAppN c ms)
  return if pf.hasMVar then none else some pf

/-- Prove `s.WF`: a fact, or below `alloca`s and new blocks (`addressof`) from one (`WF.alloca`,
`WF.addBlock`), one lemma per layer instead of a search. -/
partial def wfProof? (facts : Array (Expr × Expr)) (s : Expr) : MetaM (Option Expr) := do
  for (pf, ty) in facts do
    let_expr GlobalState.WF s' := ty | continue
    if s' == s then
      return some pf
  let goal ← mkAppM ``GlobalState.WF #[s]
  match_expr s with
  | GlobalState.alloca t _ _ =>
    let some h ← wfProof? facts t | return none
    proveBy? ``GlobalState.WF.alloca goal #[h]
  | GlobalState.mk _ m =>
    let_expr MemoryState.addBlock m' _ _ _ _ := m | return none
    let_expr GlobalState.mem t := m' | return none
    let some h ← wfProof? facts t | return none
    proveBy? ``GlobalState.WF.addBlock goal #[h]
  | _ =>
    return none

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
    if s.isAppOfArity ``GlobalState.alloca 3 then
      (counterBase? s.appFn!.appFn!.appArg!).map fun (b, k) => (b, k + 1)
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

/-- The memory predicates, weakest first: `InBounds`, `Room`, `Fits`; a stronger fact gives the
weaker ones. -/
def memPreds : Array Name :=
  #[``InBounds, ``Room, ``Fits]

/-- `(kind, m, p, w)` of a memory predicate `P m p w`, `kind` its index in `memPreds`. -/
def memPred? (ty : Expr) : Option (Nat × Expr × Expr × Expr) := do
  let k ← memPreds.findIdx? (ty.isAppOfArity · 3)
  return (k, ty.getArg! 0, ty.getArg! 1, ty.getArg! 2)

/-- `pf`, a memory predicate of kind `k`, weakened to kind `j ≤ k`. -/
def weakenMemPred (pf : Expr) (k j : Nat) : MetaM Expr := do
  let mut pf := pf
  let mut k := k
  while j < k do
    pf ← mkAppM (if k == 2 then ``Fits.room else ``Room.inBounds) #[pf]
    k := k - 1
  return pf

/-- `p` without its `.add` offsets: the same block. -/
partial def stripAdds (p : Expr) : Expr :=
  match p.app2? ``Pointer.add with
  | some (q, _) => stripAdds q
  | none => p

/-- `p.id.id < s.alloc.nextFreeBlock`: `p` into a `WF` state `s`'s memory, by a memory fact. -/
def idBelowWF? (facts : Array (Expr × Expr)) (p s : Expr) : MetaM (Option Expr) := do
  let some hwf ← wfProof? facts s | return none
  let mem ← mkAppM ``GlobalState.mem #[s]
  for (pf, ty) in facts do
    let some (k, m, p', _) := memPred? ty | continue
    unless m == mem && stripAdds p' == p do
      continue
    let lt ← mkAppM ``GlobalState.WF.id_lt_of_inBounds #[hwf, ← weakenMemPred pf k 0]
    -- `(p'.id).id` is `p.id.id`: an offset stays in its block
    let cnt ← mkAppM ``AllocState.nextFreeBlock #[← mkAppM ``GlobalState.alloc #[s]]
    let ty ← mkAppM ``LT.lt #[mkApp (mkConst ``BlockId.id) (mkApp (mkConst ``Pointer.id) p), cnt]
    return some (mkExpectedPropHint lt ty)
  return none

/-- The bounds `p.id.id < s.alloc.nextFreeBlock` (`idBelowWF?`) for the block numbers and counters
`goal` mentions. -/
def wfBounds (facts : Array (Expr × Expr)) (goal : Expr) : MetaM (Array Expr) := do
  let ptrs ← IO.mkRef (#[] : Array Expr)
  let states ← IO.mkRef (#[] : Array Expr)
  goal.forEachWhere (fun e => e.isAppOfArity ``BlockId.id 1 || e.isAppOfArity ``GlobalState.alloc 1)
    fun e => do
      if e.isAppOfArity ``GlobalState.alloc 1 then
        states.modify fun a => if a.contains e.appArg! then a else a.push e.appArg!
      else if let some p := e.appArg!.app1? ``Pointer.id then
        ptrs.modify fun a => if a.contains (stripAdds p) then a else a.push (stripAdds p)
  let mut out := #[]
  for s in ← states.get do
    for p in ← ptrs.get do
      if let some h← idBelowWF? facts p s then
        out := out.push h
  return out

/-- `p.id ≠ q.id` by the blocks' numbers, `omega` over the facts bounding them (`r.id.id < b`,
`b ≤ z.id.id`) and a slot's number (`s.slot k`, `s.allocaPtr`, a named `x = s.slot k`). Only tried
when facts bound both, or one and the other is a slot (two slots: `neSlots?`, a smaller proof; a
pointer and a slot: `step_alloca`'s facts). -/
def idOrderNe? (facts : Array (Expr × Expr)) (a b : Expr) : MetaM (Option Expr) := do
  let some p := a.app1? ``Pointer.id | return none
  let some q := b.app1? ``Pointer.id | return none
  let num (e : Expr) := mkApp (mkConst ``BlockId.id) e
  let (na, nb) := (num a, num b)
  -- one pass over the facts: the order facts about either number, the named slots `x = s.slot k`
  let mut bp := #[]
  let mut bq := #[]
  let mut named : Array (Expr × Expr × Expr) := #[]
  for (pf, ty) in facts do
    if isNatRel ty then
      if !ty.isEq then
        if (ty.find? (· == na)).isSome then
          bp := bp.push pf
        if (ty.find? (· == nb)).isSome then
          bq := bq.push pf
    else if let some (_, l, r) := ty.consumeMData.eq? then
      if (l == p || l == q) &&
          (r.isAppOfArity ``GlobalState.slot 2 || r.isAppOf ``GlobalState.allocaPtr) then
        named := named.push (l, pf, r)
  -- a slot's number over its base state's counter: `(s.slot k).id.id = b.alloc.nextFreeBlock + j`
  let slotNum? (p : Expr) : MetaM (Option (Expr × Expr)) := do
    let named? := named.findSome? fun (l, pf, r) => if l == p then some (pf, r) else none
    let (hx?, s) := named?.elim (none, p) fun (pf, r) => (some pf, r)
    let slot? :=
      if s.isAppOfArity ``GlobalState.slot 2 then
        (s.appArg!.nat?).bind fun k => (counterBase? s.appFn!.appArg!).map fun (b, j) => (b, j + k)
      else if s.isAppOfArity ``GlobalState.allocaPtr 1 then counterBase? s.appArg!
      else none
    let some (base, k) := slot? | return none
    let lhs := num (mkApp (mkConst ``Pointer.id) p)
    let cnt ← mkAppM ``AllocState.nextFreeBlock #[← mkAppM ``GlobalState.alloc #[base]]
    let rhs ← mkAppM ``HAdd.hAdd #[cnt, mkNatLit k]
    let ty ← mkEq lhs rhs
    -- by `rfl` from the slot; through `hx` for a named one
    let pf ←
      match hx? with
      | none => pure (mkExpectedPropHint (← mkEqRefl lhs) ty)
      | some hx =>
        do
          let f ←
            withLocalDeclD `x (mkConst ``Pointer) fun x => do
                mkLambdaFVars #[x] (num (mkApp (mkConst ``Pointer.id) x))
          let h ← mkCongrArg f hx
          let some (_, _, r) := (← inferType h).eq? | return none
          let hr := mkExpectedPropHint (← mkEqRefl r) (← mkEq r rhs)
          pure (mkExpectedPropHint (← mkEqTrans h hr) ty)
    return some (base, pf)
  let sp ← slotNum? p
  let sq ← slotNum? q
  -- tied: a slot and a bounded number, or both bounded (two slots: `neSlots?`, a smaller proof)
  let mut extra := bp ++ bq
  let mut tied := !bp.isEmpty && !bq.isEmpty
  for (s?, bo) in [(sp, bq), (sq, bp)] do
    let some (_, pf) := s? | continue
    if !bo.isEmpty then
      extra := extra.push pf
      tied := true
  unless tied do
    return none
  -- `omega` on the bounds alone: no other fact, nothing to normalize
  let goal ← mkAppM ``Ne #[na, nb]
  let g ← mkFreshExprMVar goal
  try
    let some g' ← g.mvarId!.falseOrByContra | return none
    g'.withContext do
        let neg := (← getLCtx).lastDecl.map (·.toExpr)
        Lean.Elab.Tactic.Omega.omega (extra.toList ++ neg.toList) g'
    return some (← mkAppM ``BlockId.ne_of_id_ne #[← instantiateMVars g])
  catch _ =>
    return none

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
  if let some h← idOrderNe? facts a b then
    return some h
  if ne.hasFVar then
    return none
  decideProof? ne

/-- The lemma `memPreds[j].suffix`: `Fits.mono`, `Room.alloca`, … -/
def memPredLemma (j : Nat) (suffix : Name) : Name :=
  memPreds[j]! ++ suffix

/-- Prove `memPreds[j] m p w` (`InBounds`, `Room` or `Fits`): a fact of that kind or a stronger
one, with the same `m` and `p`, and the same width as a literal (`(Ty.vec 8 64).width` is `512`), a
wider literal, or any width for an open `w`; not `isDefEq` on the predicate itself, which unfolds the memory. An offset
`q.add off` is inside a fact for `q` (`add_of_le`) if `q.offset + off` does not wrap: by
`q.offset`'s value, or a no-overflow fact for a larger offset; a variable `off` by `natArith?`.
Then through the writes of `m`: a store's or a masked store's known range, a new block's, an
object's write by its transport lemma. -/
partial def memPredProof? (facts : Array (Expr × Expr)) (j : Nat) (m p w : Expr) :
    MetaM (Option Expr) := do
  let goal ← mkAppM memPreds[j]! #[m, p, w]
  -- an open width (a lemma's premise only fixes): a fact's
  if w.isMVar then
    for (pf, ty) in facts do
      let some (k, m', p', w') := memPred? ty | continue
      if j ≤ k && m' == m && p' == p && (← isDefEq w w') then
        return some (← weakenMemPred pf k j)
  let w₁ ← normWidths w
  for (pf, ty) in facts do
    let some (k, m', p', w') := memPred? ty | continue
    unless j ≤ k && m' == m && p' == p do
      continue
    if w' == w || w' == w₁ || (← normWidths w') == w₁ then
      return some (mkExpectedPropHint (← weakenMemPred pf k j) goal)
  -- a wider fact, both widths literals
  if let some n := w₁.nat? then
    for (pf, ty) in facts do
      let some (k, m', p', w') := memPred? ty | continue
      unless j ≤ k && m' == m && p' == p do
        continue
      let w' ← normWidths w'
      let some n' := w'.nat? | continue
      if n ≤ n' then
        let hw ← mkDecideProof (← mkAppM ``LE.le #[w₁, w'])
        let pf ← mkAppM (memPredLemma j `mono) #[hw, ← weakenMemPred pf k j]
        return some (mkExpectedPropHint pf goal)
  if let some (q, off) := p.app2? ``Pointer.add then
    for (pf, ty) in facts do
      let some (k, m', q', v) := memPred? ty | continue
      unless j ≤ k && m' == m && q' == q do
        continue
      let some (hov, hw) ← addWithin? facts q off w₁ (← normWidths v) | continue
      return some
          (←
            mkAppOptM (memPredLemma j `add_of_le)
                #[none, none, none, none, off, hov, hw, ← weakenMemPred pf k j])
  -- a state literal's memory
  if let some t := m.app1? ``GlobalState.mem then
    if t.isAppOfArity ``GlobalState.mk 2 then
      let some h ← memPredProof? facts j t.appArg! p w | return none
      return some (mkExpectedPropHint h goal)
  -- an abbreviation's state (`withT … S`): its memory
  if let some t := m.app1? ``GlobalState.mem then
    if let some c := t.getAppFn.constName? then
      if (← isReducible c) && !(← isProjectionFn c) then
        let m' ← whnfR m
        if m' != m then
          let some h ← memPredProof? facts j m' p w | return none
          return some (mkExpectedPropHint h goal)
  -- the new block of an `alloca`, at its start or inside it: its bounds, room if live
  if let some t := m.app1? ``GlobalState.mem then
    if let some h← allocaPtrPred? facts j t p w₁ goal then
      return some h
  -- below an `alloca` or a new block: `alloca`, `addBlock`, the state's `WF` by `wfProof?` (not the
  -- transport search: a read below six `alloca`s needs twelve lemmas)
  if let some t := m.app1? ``GlobalState.mem then
    let_expr GlobalState.alloca s _ _ := t | return none
    let some hwf ← wfProof? facts s | return none
    let some h ← memPredProof? facts j (← mkAppM ``GlobalState.mem #[s]) p w | return none
    return ← proveBy? (memPredLemma j `alloca) goal #[hwf, h]
  if let some (m', s) :=
      (do
        let_expr MemoryState.addBlock m' _ _ _ _ := m | none
        let_expr GlobalState.mem s := m' | none
        return (m', s)) then
    let some hwf ← wfProof? facts s | return none
    let some h ← memPredProof? facts j m' p w | return none
    return ← proveBy? (memPredLemma j `addBlock) goal #[hwf, h]
  -- through a write
  match_expr m with
  | MemoryState.storeAt m' q v x =>
    -- the stored bits, known: from room for them, at the store or inside it
    if j == 2 then
      let v ← normWidths v
      if q == p then
        if v == w₁ then
          if let some h← memPredProof? facts 1 m' p w then
            if let some pf← proveBy? ``Fits.storeAt_self goal #[h] then
              return some pf
        -- a range from its start, the widths checked before the search below
        else if let some hw← natArith? facts (← mkAppM ``LE.le #[w₁, v]) then
          if let some h← memPredProof? facts 1 m' p v then
            if let some pf← proveBy? ``Fits.storeAt_self_of_le goal #[h, hw] then
              return some pf
      if let some (q', off) := p.app2? ``Pointer.add then
        if q' == q then
          if let some (hov, hw)← addWithin? facts q off w₁ v then
            if let some h← memPredProof? facts 1 m' q v then
              if let some pf← proveBy? ``Fits.storeAt_add_self goal #[h, hov, hw] then
                return some pf
    let some h ← memPredProof? facts j m' p w | return none
    return some (← mkAppOptM (memPredLemma j `storeAt) #[m', p, w, q, none, x, h])
  | MemoryState.storeDef m' q v _ d =>
    -- known where the mask defines it: a copy's (`memcpy`, the source's definedness) or a literal
    if j == 2 then
      return ← storeDefFits? `storeDef facts goal m' q (← normWidths v) d p w₁
    let some h ← memPredProof? facts j m' p w | return none
    proveBy? (memPredLemma j `storeDef) goal #[h]
  | MemoryState.overlay m' q v _ d =>
    if j == 2 then
      return ← storeDefFits? `overlay facts goal m' q (← normWidths v) d p w₁
    let some h ← memPredProof? facts j m' p w | return none
    proveBy? (memPredLemma j `overlay) goal #[h]
  | MemoryState.lifetimeStart m' q =>
    -- the started object: room in its bounds
    if j == 1 && q == p then
      if let some h← memPredProof? facts 0 m' p w then
        if let some pf← proveBy? ``Room.lifetimeStart_self goal #[h] then
          return some pf
    let some h ← memPredProof? facts j m' p w | return none
    if j == 0 then
      return ← proveBy? ``InBounds.lifetimeStart goal #[h]
    let some hne ←
      neProof? facts (← mkAppM ``Pointer.id #[p]) (← mkAppM ``Pointer.id #[q]) | return none
    proveBy? (memPredLemma j `lifetimeStart) goal #[h, hne]
  | MemoryState.lifetimeEnd m' q =>
    let some h ← memPredProof? facts j m' p w | return none
    if j == 0 then
      return ← proveBy? ``InBounds.lifetimeEnd goal #[h]
    let some hne ←
      neProof? facts (← mkAppM ``Pointer.id #[p]) (← mkAppM ``Pointer.id #[q]) | return none
    proveBy? (memPredLemma j `lifetimeEnd) goal #[h, hne]
  | _ =>
    objectWrite? facts j m p w goal

where
  /-- Through an object's write `m = f m' …` (`storeVec`, `hashMem`): by its transport lemma
  `P.f` (`InBounds.storeVec`) from the predicate below, one layer at a time, not a search; its other
  premises a `≠` or disjointness of blocks. -/
  objectWrite? (facts : Array (Expr × Expr)) (j : Nat) (m p w goal : Expr) :
      MetaM (Option Expr) := do
    let some f := m.getAppFn.constName? | return none
    let some last := f.componentsRev.head? | return none
    let some m' ← m.getAppArgs.findM? fun a => return (← inferType a).isConstOf ``MemoryState
      | return none
    let suffix := memPreds[j]!.componentsRev.head!
    let lems := (← labelled `mlir_transport).filter fun n =>
      match n.componentsRev with
      | l :: pre :: _ => l == last && pre == suffix
      | _ => false
    if lems.isEmpty then
      return none
    let some h ← memPredProof? facts j m' p w | return none
    for lem in lems do
      let saved ← saveState
      let c ← mkConstWithFreshMVarLevels lem
      let (ms, _, ty) ← forallMetaTelescopeReducing (← inferType c)
      if ← withReducible (isDefEq ty goal) then
        let mut ok := true
        for mv in ms do
          let mv := mv.mvarId!
          if ← mv.isAssigned then
            continue
          let pty ← instantiateMVars (← mv.getType)
          unless ← isProp pty do
            continue
          -- the predicate below, then block distinctness
          let pf? ←
            if ← isDefEq pty (← inferType h) then pure (some h)
            else
              match pty.cleanupAnnotations with
              | .app (.app (.app (.const ``Ne _) _) a) b => neProof? facts a b
              | _ =>
                match neSides? pty with
                | some (a, b) => neProof? facts a b
                | none =>
                  match_expr pty with
                  | Range.Disjoint ra rb =>
                    let_expr Range.of p₁ v₁ := ra | pure none
                    let_expr Range.of p₂ v₂ := rb | pure none
                    let some hne ←
                      neProof? facts (← mkAppM ``Pointer.id #[p₁]) (← mkAppM ``Pointer.id #[p₂])
                      | pure none
                    pure (some (mkAppN (mkConst ``Range.disjoint_of_id_ne) #[p₁, p₂, v₁, v₂, hne]))
                  | _ => pure none
          match pf? with
          | some pf =>
            mv.assign pf
          | none =>
            ok := false
            break
        if ok then
          let pf ← instantiateMVars (mkAppN c ms)
          if !pf.hasMVar then
            return some pf
      saved.restore
    return none
  /-- `InBounds` or `Room` (`j`) of `(s.alloca n dead).mem` at `p`, `s.allocaPtr` or inside it. -/
  allocaPtrPred? (facts : Array (Expr × Expr)) (j : Nat) (t p w goal : Expr) :
      MetaM (Option Expr) := do
    let_expr GlobalState.alloca s n dead := t | return none
    if j == 2 || (j == 1 && !dead.isConstOf ``Bool.false) then
      return none
    let q := mkApp (mkConst ``GlobalState.allocaPtr) s
    -- the new block's pointer as `s.allocaPtr` or as a slot `b.slot k` of the same block
    let isNew (e : Expr) : Bool :=
      e == q || (slotPtr? q == some e) ||
        (e.isAppOfArity ``GlobalState.slot 2 && (do
          let (b, k) ← counterBase? s
          let k' ← e.appArg!.nat?
          guard (e.appFn!.appArg! == b && k == k')) == some ())
    let (base, off?) :=
      if isNew p then (some p, none)
      else
        match p.app2? ``Pointer.add with
        | some (q', off) => if isNew q' then (some q', some off) else (none, none)
        | none => (none, none)
    let some _ := base |
      -- a named slot `x = b.slot k`: as the slot, then back along `hx`
      let x := stripAdds p
      unless x.isFVar do
        return none
      let some (hx, r) := facts.findSome? fun (pf, ty) =>
          (ty.consumeMData.eq?).bind fun (_, l, r) =>
            if l == x && isNew r then some (pf, r) else none
        | return none
      let rep (e : Expr) := e.replace fun t => if t == x then some r else none
      let some h ← allocaPtrPred? facts j t (rep p) w (rep goal) | return none
      let motive ← motiveOver goal x (mkConst ``Pointer)
      return some (← mkEqNDRec motive h (← mkEqSymm hx))
    let goal' := goal.replace fun e => if base == some e then some q else none
    let v ← normWidths (← mkAppM ``HMul.hMul #[mkNatLit 8, n])
    let lem := if j == 0 then ``InBounds.allocaPtr else ``Room.allocaPtr
    -- about `s.allocaPtr`, the goal's slot by `rfl`
    let pf? ←
      match off? with
      | none =>
        let some hw ← natArith? facts (← mkAppM ``LE.le #[w, v]) | return none
        proveBy? lem goal' #[hw]
      | some off =>
        let some (hov, hw) ← addWithin? facts q off w v | return none
        let whole ← mkAppM memPreds[j]! #[← mkAppM ``GlobalState.mem #[t], q, v]
        let some h ← proveBy? lem whole #[← mkAppM ``Nat.le_refl #[v]] | return none
        pure (some (← mkAppOptM (memPredLemma j `add_of_le)
          #[none, none, none, none, off, hov, hw, h]))
    return pf?.map (mkExpectedPropHint · goal)
  /-- `Fits (m.storeDef q x d) p w` (the `goal`; `m.overlay` for `kind := overlay`) for `p` at `q`
  or inside it, `v` bits stored with room for them: from the source's `Fits` for a copy's mask
  `m.definedAt src v`, by the kernel's `decide` for a literal mask (no
  `exponentiation.threshold`). -/
  storeDefFits? (kind : Name) (facts : Array (Expr × Expr)) (goal m q v d p w : Expr) :
      MetaM (Option Expr) := do
    let lemma (suffix : String) : Name := .str ``Fits s!"{kind}{suffix}"
    let off? := if p == q then none else (p.app2? ``Pointer.add).bind fun (q', off) =>
      if q' == q then some off else none
    if p != q && off?.isNone then
      return none
    let src? : Option Expr := do
      let_expr MemoryState.definedAt m'' src _ := d | none
      guard (m'' == m)
      return src
    -- the cheap checks first, then the searches below the store
    match src?, off? with
    | some src, none =>
      let some hw ← natArith? facts (← mkAppM ``LE.le #[w, v]) | return none
      let some hs ← memPredProof? facts 2 m src w | return none
      let some hr ← memPredProof? facts 1 m q v | return none
      proveBy? (lemma "_definedAt_self") goal #[hr, hs, hw]
    | some src, some off =>
      let some (hov, hw) ← addWithin? facts q off w v | return none
      let some (hovq, _) ← addWithin? facts src off w v | return none
      let some hs ← memPredProof? facts 2 m (← mkAppM ``Pointer.add #[src, off]) w | return none
      let some hr ← memPredProof? facts 1 m q v | return none
      proveBy? (lemma "_definedAt") goal #[hr, hs, hov, hovq, hw]
    | none, _ =>
      -- a literal mask: its bits there all set
      if (← getBitVecValue? d).isNone then
        return none
      let start ←
        match off? with
        | none => pure (mkNatLit 0)
        | some off => mkAppM ``HMul.hMul #[← mkAppM ``BitVec.toNat #[off], mkNatLit 8]
      let hdTy ←
        mkEq (← mkAppM ``BitVec.extractLsb' #[start, w, d]) (← mkAppM ``BitVec.allOnes #[w])
      let some hd ← kernelDecide? hdTy | return none
      match off? with
      | none =>
        let some hw ← natArith? facts (← mkAppM ``LE.le #[w, v]) | return none
        let some hr ← memPredProof? facts 1 m q v | return none
        proveBy? (lemma "_of_mask_self") goal #[hr, hw, hd]
      | some off =>
        let some (hov, hw) ← addWithin? facts q off w v | return none
        let some hr ← memPredProof? facts 1 m q v | return none
        proveBy? (lemma "_of_mask") goal #[hr, hov, hw, hd]

/-- Prove `Fits m p w` by `memPredProof?`. -/
def fitsProof? (facts : Array (Expr × Expr)) (m p w : Expr) : MetaM (Option Expr) :=
  memPredProof? facts 2 m p w

/-- `(Range.of p v).Disjoint (Range.of q w)`: distinct blocks by `ne?` (`neProof?` by default), else
by offsets in one block (`omega`) if `offsets`. -/
def disjointProof? (facts : Array (Expr × Expr)) (p v q w : Expr) (offsets := true)
    (ne? : Expr → Expr → MetaM (Option Expr) := neProof? facts) : MetaM (Option Expr) := do
  let goal ← mkAppM ``Range.Disjoint #[← mkAppM ``Range.of #[p, v], ← mkAppM ``Range.of #[q, w]]
  -- different blocks
  let pid ← mkAppM ``Pointer.id #[p]
  let qid ← mkAppM ``Pointer.id #[q]
  if let some h← ne? pid qid then
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

/-- A read past one store, by the facts: for `simp only` outside the steps, which read through
writes with `readPastWrites`. -/
simproc_decl readThroughStore (MemoryState.readAt (MemoryState.storeAt _ _ _) _ _) := fun e => do
  let_expr MemoryState.readAt mm q w := e | return .continue
  let_expr MemoryState.storeAt m p v x := mm | return .continue
  let facts ← splitConjunctedFacts
  -- read back from write
  if ← isDefEq p q <&&> isDefEq v w then
    if let some hf← memPredProof? facts 0 m p w then
      if let some pf← proveEqBy? ``MemoryState.readAt_storeAt_self e x [hf] then
        return .visit { expr := x, proof? := some pf }
  -- Disjoint writes
  if let some hd← disjointProof? facts p v q w then
    let r ← mkAppM ``MemoryState.readAt #[m, q, w]
    if let some pf← proveEqBy? ``MemoryState.readAt_storeAt_disjoint e r [hd] then
      return .visit { expr := r, proof? := pf }
  return .continue

/-- `goal` about offsets: unfold `uaddOverflow`, the offsets' values (`x.offset = 0`) in, then
`omega` from the facts. -/
def offsetProof? (facts : Array (Expr × Expr)) (goal : Expr) : MetaM (Option Expr) := do
  let g ← mkFreshExprMVar goal
  try
    -- `Pointer.add` too, so `omega` sees a moved pointer's offset through its base's
    let mut thms ← (← getSimpTheorems).addDeclToUnfold ``BitVec.uaddOverflow
    thms ← thms.addDeclToUnfold ``Pointer.add
    for (pf, ty) in facts do
      let some (_, l, r) := ty.eq? | continue
      if l.isAppOfArity ``Pointer.offset 1 && !r.hasFVar && !r.hasMVar then
        thms ← thms.add (.other `offsetFact) #[] pf
    thms ← thms.addConst ``BitVec.toNat_add
    let ctx ← Simp.mkContext (simpTheorems := #[← thms.addConst ``BitVec.toNat_ofNat])
    let (r, _) ← simpGoal g.mvarId! ctx (simprocs := #[← Simp.getSimprocs])
    if let some (_, g') := r then
      -- `t % 2 ^ 64` as `t` where `omega` shows `t < 2 ^ 64`: with the `%` left in, `omega` (no
      -- dark shadows) misses `192 * k % 2 ^ 64` for `k < 8`
      let modCtx ←
        Simp.mkContext (simpTheorems := #[← ({} : SimpTheorems).addConst ``Nat.mod_eq_of_lt])
      let disch : Simp.Discharge := fun p => do
        let m ← mkFreshExprMVar p
        try
          omegaFromFacts facts m.mvarId!
          let pf ← instantiateMVars m
          return if pf.hasMVar then none else some pf
        catch _ =>
          return none
      let saved ← saveState
      try
        let (r', _) ← simpGoal g' modCtx (discharge? := disch)
        if let some (_, g'') := r' then
          omegaFromFacts facts g''
      catch _ =>
        saved.restore
        omegaFromFacts facts g'
    return some (← instantiateMVars g)
  catch _ =>
    return none

/-- `¬p.offset.uaddOverflow off`, by `offsetProof?`. -/
def noOverflowProof? (facts : Array (Expr × Expr)) (p off : Expr) : MetaM (Option Expr) := do
  offsetProof? facts (← noOverflowGoal p off)

/-- A `GepFlags` literal's `nusw` and `nuw`. -/
def gepFlagBits? (f : Expr) : MetaM (Option (Bool × Bool)) := do
  let_expr GepFlags.mk a b := ← whnfR (← instantiateMVars f) | return none
  let bool? (e : Expr) : Option Bool :=
    if e.isConstOf ``Bool.true then some true
    else if e.isConstOf ``Bool.false then some false
    else none
  return (bool? a).bind fun a => (bool? b).map (a, ·)

/-- `f.<field> = b` for a flags literal, by `rfl`. -/
def gepFlagEq (f : Expr) (field : Name) (b : Bool) : MetaM Expr := do
  let bE := toExpr b
  return mkExpectedPropHint (← mkEqRefl bE) (← mkEq (mkApp (mkConst (``GepFlags ++ field)) f) bE)

/-- `lem` instantiated to rewrite `e`, its explicit hypotheses proved by `prove`: the result and the
proof. -/
def rewriteBy? (lem : Name) (e : Expr) (prove : Expr → MetaM (Option Expr)) :
    MetaM (Option (Expr × Expr)) := do
  let c ← mkConstWithFreshMVarLevels lem
  let (xs, bis, ty) ← forallMetaTelescopeReducing (← inferType c)
  let some (_, lhs, rhs) := ty.eq? | return none
  unless ← isDefEq lhs e do
    return none
  for x in xs, bi in bis do
    if bi.isExplicit then
      let some h ← prove (← instantiateMVars (← inferType x)) | return none
      unless ← isDefEq x h do
        return none
  let pf ← instantiateMVars (mkAppN c xs)
  if pf.hasMVar then
    return none
  return some (← instantiateMVars rhs, pf)

/-- A side condition of a `gep` lemma about offsets: by `decide` (a flag, a literal), the offsets'
facts, or `omega` from them. -/
def gepSideProof? (facts : Array (Expr × Expr)) (goal : Expr) : MetaM (Option Expr) := do
  if !goal.hasFVar && !goal.hasMVar then
    if let some h ← decideProof? goal then
      return some h
  if let some h ← decideWithOffsets? facts goal then
    return some h
  if let some h ← natArith? facts goal then
    return some h
  offsetProof? facts goal

/-- `gep` of a pointer: `.value (p.add off)` without flags; for `nuw`, where the address provably
does not wrap (and for `nusw` the offset is below `2 ^ 63`), else poison where it provably does. -/
simproc_decl gepValue (Operation.gep _ (.value _) (.value _)) := fun e => do
  let_expr Operation.gep f bo pp := e | return .continue
  let_expr PoisonOr.value _ off := bo | return .continue
  let_expr PoisonOr.value _ p := pp | return .continue
  let some (nusw, nuw) ← gepFlagBits? f | return .continue
  let value ← mkAppM ``PoisonOr.value #[← mkAppM ``Pointer.add #[p, off]]
  if !nusw && !nuw then
    return .visit { expr := value, proof? := ← mkAppOptM ``gep_none #[off, p] }
  let facts ← splitConjunctedFacts
  -- `off.toNat < 2 ^ 63`, the `nusw` reading's
  let small ← mkAppM ``LT.lt #[← mkAppM ``BitVec.toNat #[off], mkNatLit (2 ^ 63)]
  let nuswEq ← mkEq (mkApp (mkConst ``GepFlags.nusw) f) (toExpr false)
  let hs? : Option Expr ←
    if !nusw then
      pure (some (← mkAppOptM ``Or.inl #[nuswEq, small, ← gepFlagEq f `nusw false]))
    else
      (← gepSideProof? facts small).mapM fun h => mkAppOptM ``Or.inr #[nuswEq, small, h]
  -- a stack slot's offset by its fact, a bound for a larger offset, else bounds by `omega`
  let h? ←
    (do
        if let some h← decideWithOffsets? facts (← noOverflowGoal p off) then
          return some h
        if let some h← noOverflowOfFact? facts p off then
          return some h
        noOverflowProof? facts p off)
  if let (some h, some hs) := (h?, hs?) then
    return .visit { expr := value, proof? := ← mkAppOptM ``gep_value #[off, f, p, h, hs] }
  -- an offset known to wrap: poison (a negative index's unsigned reading)
  let ov ← mkEq (← mkAppM ``BitVec.uaddOverflow #[← mkAppM ``Pointer.offset #[p], off])
    (mkConst ``Bool.true)
  let some h ← decideWithOffsets? facts ov | return .continue
  let nuwEq ← mkEq (mkApp (mkConst ``GepFlags.nuw) f) (toExpr true)
  let nuswT ← mkEq (mkApp (mkConst ``GepFlags.nusw) f) (toExpr true)
  let hf ←
    if nuw then
      mkAppOptM ``Or.inl #[nuwEq, mkAnd nuswT small, ← gepFlagEq f `nuw true]
    else
      let some hsm ← gepSideProof? facts small | return .continue
      mkAppOptM ``Or.inr
        #[nuwEq, mkAnd nuswT small, ← mkAppM ``And.intro #[← gepFlagEq f `nusw true, hsm]]
  return .visit { expr := ← mkAppOptM ``PoisonOr.poison #[mkConst ``Pointer],
                  proof? := ← mkAppOptM ``gep_overflow #[off, f, p, h, hf] }

/-- `gepDyn` by a value index. Without `nusw`: the offset read unsigned (the `gep` by the index
itself for bytes), as the steps' old `gepDyn` unfolded. With `nusw`: the unsigned `gep` where the
offset is provably below `2 ^ 63`, else the signed reading (`gepSigned`) where the unsigned `gep`
simplifies to poison; else it is left, for a later pass. Terms built unchecked: `ptr`'s type may be
a register type not yet reduced. -/
simproc_decl gepDynValue (Operation.gepDyn _ _ _ _ (.value _)) := fun e => do
  let_expr Operation.gepDyn f byteOff stride ptr idx := e | return .continue
  let_expr PoisonOr.value _ i := idx | return .continue
  let some (nusw, _) ← gepFlagBits? f | return .continue
  let bytes := (← (evalNat byteOff).run) == some 0 && (← (evalNat stride).run) == some 1
  let rhsOf (pf : Expr) : MetaM Expr := do
    let some (_, _, r) := (← inferType pf).eq? | throwError "not an equation"
    return r
  if !nusw then
    let hf ← gepFlagEq f `nusw false
    let pf :=
      if bytes then mkAppN (mkConst ``gepDyn_zero_one_of_not_nusw) #[f, ptr, i, hf]
      else mkAppN (mkConst ``gepDyn_of_not_nusw) #[f, byteOff, stride, ptr, i, hf]
    return .visit { expr := ← rhsOf pf, proof? := pf }
  let hf ← gepFlagEq f `nusw true
  let facts ← splitConjunctedFacts
  let iNat ← mkAppM ``BitVec.toNat #[i]
  let off ←
    if bytes then pure iNat
    else mkAppM ``HAdd.hAdd #[byteOff, ← mkAppM ``HMul.hMul #[iNat, stride]]
  let lt ← mkAppM ``LT.lt #[off, mkNatLit (2 ^ 63)]
  let hlt? ←
    (do
        -- a byte index masked below `2 ^ 63`
        if bytes then
          if i.isAppOfArity ``HAnd.hAnd 6 then
            let c := i.appArg!
            let hc ← mkAppM ``LT.lt #[← mkAppM ``BitVec.toNat #[c], mkNatLit (2 ^ 63)]
            if let some h ← decideProof? hc then
              return some (mkApp3 (mkConst ``toNat_and_lt) i.appFn!.appArg! c h)
        if let some h ← gepSideProof? facts lt then
          return some h
        -- by the step's `simp` arguments
        let r ← Simp.simp lt
        if r.expr.isConstOf ``True then
          return some (← mkOfEqTrue (← r.getProof))
        return none)
  if let some hlt := hlt? then
    let pf :=
      if bytes then mkAppN (mkConst ``gepDyn_zero_one_of_lt) #[f, ptr, i, hf, hlt]
      else mkAppN (mkConst ``gepDyn_of_lt) #[byteOff, stride, f, ptr, i, hf, hlt]
    return .visit { expr := ← rhsOf pf, proof? := pf }
  -- the unsigned `gep`, poison: the signed reading
  let offBv ←
    if bytes then pure i else pure (mkApp2 (mkConst ``BitVec.ofNat) (mkNatLit 64) off)
  let nuwOnly := mkApp2 (mkConst ``GepFlags.mk) (toExpr false) (toExpr true)
  let u := mkApp3 (mkConst ``Operation.gep) nuwOnly
    (mkApp2 (mkConst ``PoisonOr.value) (← inferType i) offBv) ptr
  let r ← Simp.simp u
  unless r.expr.isAppOf ``PoisonOr.poison do
    return .continue
  let h := mkExpectedPropHint (← r.getProof) (← mkEq u r.expr)
  let pf :=
    if bytes then mkAppN (mkConst ``gepDyn_zero_one_of_unsigned_poison) #[ptr, f, i, hf, h]
    else mkAppN (mkConst ``gepDyn_of_unsigned_poison) #[byteOff, stride, ptr, f, i, hf, h]
  return .visit { expr := ← rhsOf pf, proof? := pf }

/-- `gepSigned` of a pointer whose offset and addresses provably stay in range, by the offsets'
facts: `.value (p.add (BitVec.ofInt 64 off))`. -/
simproc_decl gepSignedValue (Operation.gepSigned _ _ _ _ (.value _)) := fun e => do
  let facts ← splitConjunctedFacts
  let some (r, pf) ← rewriteBy? ``gepSigned_value e (gepSideProof? facts) | return .continue
  return .visit { expr := r, proof? := pf }

/-- `gepBack n` of a pointer: `.value (p.add (-n))` without flags, or for `nusw` (no `nuw`) at
least `n` bytes into its block. -/
simproc_decl gepBackValue (Operation.gepBack _ _ (.value _)) := fun e => do
  let_expr Operation.gepBack f _ _ := e | return .continue
  let some (nusw, nuw) ← gepFlagBits? f | return .continue
  let facts ← splitConjunctedFacts
  let some (r, pf) ←
      if !nusw && !nuw then rewriteBy? ``gepBack_none e fun _ => pure none
      else rewriteBy? ``gepBack_value e (gepSideProof? facts) | return .continue
  return .visit { expr := r, proof? := pf }

/-- The new state with its projections reduced -/
def dsimpState (e : Expr) : MetaM Expr := do
  return (← dsimp e (← Simp.mkContext)).1

/-- `p` from the facts `facts` (by instantiated type), the searches `side`, the `mlir_transport`
lemmas `lemmas` and the local implications `locals`, at reducible transparency, `fuel` lemmas
deep. -/
partial def transportWith (facts : Std.HashMap Expr Expr) (lemmas : Array Name) (fuel : Nat)
    (p : Expr) (locals : Array Expr := #[])
    (side : Expr → MetaM (Option Expr) := fun _ => pure none) : MetaM (Option Expr) := do
  if let some h := facts[p]? then
    return some h
  if let some h← side p then
    return some h
  if fuel = 0 then
    return none
  for lem in lemmas.map (mkConstWithFreshMVarLevels ·) ++ locals.map pure do
    let saved ← saveState
    let m ← mkFreshExprMVar p
    let pf? ←
      (do
            let gs ← withReducible (m.mvarId!.apply (← lem))
            for g in gs do
              if ← g.isAssigned then
                continue
              let some pf ←
                transportWith facts lemmas (fuel - 1) (← instantiateMVars (← g.getType)) locals
                    side | return none
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

/-- The context's implications, as lemmas for `transportWith` (`hpost : ∀ s, s.WF → (post s).WF`, a
callee's). -/
def localImplications : MetaM (Array Expr) := do
  (← getLCtx).foldlM (init := #[]) fun acc d => do
      if d.isImplementationDetail then
        return acc
      let ty ← instantiateMVars d.type
      return if ty.isForall && (← isProp ty) then acc.push d.toExpr else acc

/-- What a side condition is discharged from (`factDischarge`), gathered once: the transport
lemmas, the context's facts (split, and by type), and its named slots. -/
structure FactCtx where
  transport : Array Name
  facts : Array (Expr × Expr)
  factMap : Std.HashMap Expr Expr
  /-- `x ↦ (b.slot k, hx : x = b.slot k)`, for the named slots `x`. -/
  slots : Std.HashMap Expr (Expr × Expr)

/-- The named slots `hx : x = b.slot k` among `eqs`, by name. -/
def namedSlots (eqs : Array LocalEq) : MetaM (Std.HashMap Expr (Expr × Expr)) := do
  let mut slots := {}
  for e in eqs do
    if e.lhs.isFVar && e.rhs.isAppOfArity ``GlobalState.slot 2 && !slots.contains e.lhs then
      slots := slots.insert e.lhs (e.rhs, ← mkExpectedTypeHint e.decl.toExpr e.type)
  return slots

def FactCtx.build : MetaM FactCtx := do
  return { transport := ← labelled `mlir_transport, facts := ← splitConjunctedFacts,
           factMap := ← contextFactMap, slots := ← namedSlots (← localEqs) }

/-- What reading through memory needs, gathered once (per step, per `simp` call): the facts, the
read lemmas, and the context's read facts by their left side, widths as literals. -/
structure MemCtx extends FactCtx where
  lemmas : Array ReadLemma
  heads : Array Name
  /-- `read (S.mem) … ↦ (x, h : read (S.mem) … = x)`, for the locals `S`. -/
  reads : Std.HashMap Expr (Expr × Expr)
  /-- `S.mem ↦ (hS, s.mem)` for `hS : S = s`, filled by `readThroughState`. -/
  mems : IO.Ref (Std.HashMap Expr (Option (FVarId × Expr)))

def MemCtx.build : MetaM MemCtx := do
  let lemmas ← readLemmas
  let heads := ReadLemma.heads lemmas
  let eqs ← localEqs
  let mut reads := {}
  for e in eqs do
    unless heads.any e.lhs.isAppOf do
      continue
    unless e.lhs.getAppArgs.any fun a => a.isAppOfArity ``GlobalState.mem 1 && a.appArg!.isFVar do
      continue
    reads := reads.insert (← normWidths e.lhs) (e.rhs, e.decl.toExpr)
  return { lemmas, heads, transport := ← labelled `mlir_transport, facts := ← splitConjunctedFacts,
           factMap := ← contextFactMap, slots := ← namedSlots eqs, reads, mems := ← IO.mkRef {} }

/-- The slot `s.slot k` whose block id `e` (`p.id`) is: `p` spelled as one, as an `allocaPtr`
(`slotPtr?`), or a named slot, with its `hx : x = s.slot k`. -/
def slotOfId? (c : FactCtx) (e : Expr) : Option (Expr × Option Expr) := do
  let p := stripAdds (← e.app1? ``Pointer.id)
  if let some (s, hx) := c.slots[p]? then
    return (s, some hx)
  if p.isAppOfArity ``GlobalState.slot 2 then
    return (p, none)
  return (← slotPtr? p, none)

/-- `a ≠ b` for block ids of which one is a slot (`slotOfId?`): two slots of one state at distinct
literal indices, else by the facts about the named slot a slot is (`q.id ≠ x.id`). -/
def neSlots? (c : FactCtx) (a b : Expr) : MetaM (Option Expr) := do
  let sa? := slotOfId? c a
  let sb? := slotOfId? c b
  if sa?.isNone && sb?.isNone then
    return none
  let idOf (p : Expr) := mkApp (mkConst ``Pointer.id) p
  let sides (hx : Expr) : MetaM (Expr × Expr) := do
    let some (_, x, s) := (← inferType hx).eq? | throwError "not an equation"
    return (x, s)
  -- `pf : ¬l = r`, its left (or right) pointer moved along `h : y = y'`
  let move (pf h : Expr) (left : Bool) (l r : Expr) : MetaM Expr := do
    let motive ←
      withLocalDeclD `y (mkConst ``Pointer) fun y => do
          mkLambdaFVars #[y]
              (mkNot
                (←
                  if left then
                    mkEq (idOf y) r
                  else
                    mkEq l (idOf y)))
    mkEqNDRec motive pf h
  -- one state's slots at distinct literal indices, then back to the named slots
  if let (some (sa, ha), some (sb, hb)) := (sa?, sb?) then
    if let (some i, some j) := (sa.appArg!.nat?, sb.appArg!.nat?) then
      if sa.appFn!.appArg! == sb.appFn!.appArg! && i != j then
        let hij ← mkDecideProof (← mkAppM ``Ne #[sa.appArg!, sb.appArg!])
        let mut pf ←
          mkAppOptM ``GlobalState.slot_id_ne #[sa.appFn!.appArg!, sa.appArg!, sb.appArg!, hij]
        let mut l := idOf sa
        if let some hx := ha then
          pf ← move pf (← mkEqSymm hx) true l (idOf sb)
          l := idOf (← sides hx).1
        if let some hx := hb then
          pf ← move pf (← mkEqSymm hx) false l (idOf sb)
        return some (← mkExpectedTypeHint pf (mkNot (← mkEq a b)))
  -- a slot spelled by its state as the named slot `x` it is, by the facts `q.id ≠ x.id`
  let named (s? : Option (Expr × Option Expr)) : Option Expr := do
    let (s, none) ← s? | none
    c.slots.fold (init := none) fun acc _ (s', hx) => acc <|> if s' == s then some hx else none
  let na := named sa?
  let nb := named sb?
  if na.isNone && nb.isNone then
    return none
  let la ← na.elim (pure a) fun hx => return idOf (← sides hx).1
  let lb ← nb.elim (pure b) fun hx => return idOf (← sides hx).1
  let some pf ← neProof? c.facts la lb | return none
  let mut pf := pf
  let mut l := la
  if let some hx := na then
    pf ← move pf hx true l lb
    l := idOf (← sides hx).2
  if let some hx := nb then
    pf ← move pf hx false l lb
  return some (← mkExpectedTypeHint pf (mkNot (← mkEq a b)))

/-- A transport lemma's premise by the searches needing no lemma: a memory predicate
(`memPredProof?`), a relation of naturals (`natArith?`), `≠` of block ids (facts, either way round,
`List.Nodup`, distinct slots, their order) and the disjointness of distinct blocks. -/
def premiseSearch? (c : FactCtx) (goal : Expr) : MetaM (Option Expr) := do
  let ne? (a b : Expr) : MetaM (Option Expr) := do
    if let some h← neProof? c.facts a b then
      return some h
    neSlots? c a b
  if let some (j, m, p, w) := memPred? goal then
    return ← memPredProof? c.facts j m p w
  -- a width or offset bound (`37 ≤ 41`), a block number below a counter
  if isNatRel goal then
    return ← natArith? c.facts goal (← wfBounds c.facts goal)
  match_expr goal with
  | Range.Disjoint a b =>
    let_expr Range.of p v := a | return none
    let_expr Range.of q w := b | return none
    disjointProof? c.facts p v q w (offsets := false) (ne? := ne?)
  | _ =>
    let some (a, b) := neSides? goal | return none
    if (← inferType a).isConstOf ``Bool then
      return none
    let some pf ← ne? a b | return none
    return some (mkExpectedPropHint pf goal)

/-- A side condition from the facts `c`, cheapest first: a fact; `decide`, the offsets replaced by
their facts (an offset's `¬uaddOverflow`, a width bound); `InBounds`, `Room`, `Fits`, disjointness
and `≠` by their searches; then `mlir_transport` lemmas `fuel` deep, or with no `fuel` a local up
to reducible unfolding. -/
def factDischarge (c : FactCtx) (fuel : Nat) (goal : Expr) : MetaM (Option Expr) := do
  let goal ← instantiateMVars goal
  if let some pf := c.factMap[goal]? then
    return some pf
  if let some pf← decideWithOffsets? c.facts goal then
    return some pf
  let local? := do
    return (← withReducible (findLocalDeclWithType? goal)).map mkFVar
  match_expr goal with
  | InBounds m p w =>
    if let some pf← memPredProof? c.facts 0 m p w then
      return some pf
  | Room m p w =>
    if let some pf← memPredProof? c.facts 1 m p w then
      return some pf
  | Fits m p w =>
    if let some pf← fitsProof? c.facts m p w then
      return some pf
  | GlobalState.WF s =>
    if let some pf← wfProof? c.facts s then
      return some pf
  | Range.Disjoint a b =>
    let_expr Range.of p v := a | return none
    let_expr Range.of q w := b | return none
    -- distinct blocks also as slots
    let ne? (a b : Expr) : MetaM (Option Expr) := do
      if let some h← neProof? c.facts a b then
        return some h
      neSlots? c a b
    return ← disjointProof? c.facts p v q w (ne? := ne?)
  | _ =>
    -- no lemma concludes `≠`: its searches, or a local `h : b ≠ a` for `simp`; not for flags
    -- (`¬x.uaddOverflow k = true`), which `neProof?` would unfold against each flag fact
    if let some (a, b) := neSides? goal then
      unless (← inferType a).isConstOf ``Bool do
        if let some pf← neProof? c.facts a b then
          return some (mkExpectedPropHint pf goal)
        if let some pf← neSlots? c a b then
          return some pf
        if fuel = 0 then
          return ← local?
        return none
  if fuel = 0 then
    return ← local?
  transportWith c.factMap c.transport fuel goal (side := premiseSearch? c)

/-- The writes of the memory `m`, outermost first: each with the memory it writes over (its first
`MemoryState` argument). -/
partial def writesOf (m : Expr) (acc : Array Expr := #[]) : MetaM (Array Expr) := do
  for a in m.getAppArgs do
    if (← inferType a).isConstOf ``MemoryState then
      return ← writesOf a (acc.push m)
  return acc

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
        let some pf ← factDischarge c.toFactCtx 4 ty |
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
    -- an abbreviation of writes no lemma reads through (`storeOut m …`): its writes
    for i in [0:e.getAppNumArgs] do
      let a := e.getArg! i
      let some n := a.getAppFn.constName? | continue
      unless (← inferType a).isConstOf ``MemoryState do
        continue
      unless (← isReducible n) && !(← isProjectionFn n) do
        continue
      let some a' ← withReducible (unfoldDefinition? a) | continue
      let e' := mkAppN e.getAppFn (e.getAppArgs.set! i a'.headBeta)
      let (v, pf) ← readThrough c e'
      if v == e' then
        break
      return (v, mkExpectedPropHint pf (← mkEq e v))
    return (e, ← mkEqRefl e)

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
  -- at its start: `S.mem.readAt q w` for literal `w ≤ v`
  if !p.isAppOf ``Pointer.add then
    let some wn := w.nat? | return .continue
    for (l, h) in c.reads.toArray.map fun (l, (_, h)) => (l, h) do
      let_expr MemoryState.readAt m' q' v := l | continue
      unless m' == m && q' == p do
        continue
      let some vn := v.nat? | continue
      unless wn < vn do
        continue
      let hw ← mkDecideProof (← mkAppM ``LE.le #[w, v])
      let pf ← mkAppM ``MemoryState.readAt_of_readAt_le #[hw, h]
      let some (_, _, r) := (← inferType pf).eq? | continue
      return .visit { expr := r, proof? := some (mkExpectedPropHint pf (← mkEq e r)) }
    return .continue
  let some (q, off) := p.app2? ``Pointer.add | return .continue
  for (l, h) in c.reads.toArray.map fun (l, (_, h)) => (l, h) do
    let_expr MemoryState.readAt m' q' v := l | continue
    unless m' == m && q' == q do
      continue
    let some hfits ← memPredProof? c.facts 0 m q v | continue
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
          let some hS ← findLocalEq? m.appArg! | pure none
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

/-- A registered read of a written memory: through the writes by the `mlir_read` lemmas, as far as
they go. -/
def readPastWrites (c : MemCtx) : Simp.Simproc := fun e => do
  unless e.getAppArgs.any fun a => c.lemmas.any (a.isAppOf ·.write) do
    return .continue
  let (v, pf) ← readThrough c e
  if v == e then
    return .continue
  return .visit { expr := v, proof? := some pf }

/-- `readMemFact`, `readThroughState` and `readPastWrites` for one `simp` call, keyed on the
registered reads. -/
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
    procs := procs.addCore keys `readPastWrites true (.inl (readPastWrites c))
  return procs

end

end MLIR.Tactic
