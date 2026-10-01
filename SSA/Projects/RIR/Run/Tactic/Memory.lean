module

public import SSA.Projects.RIR.Semantics.Effectful.Memory.Operations
public import SSA.Projects.RIR.Memory.Range
public import SSA.Projects.RIR.Run.Tactic.Util
public import SSA.Projects.RIR.Run.Memory
public meta import Lean.Elab.Tactic

namespace LeanMLIR.RIR.Tactic

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

def findFact? (facts : Array (Expr × Expr)) (goal : Expr) : MetaM (Option Expr) := do
  for (pf, ty) in facts do
    if ← withNewMCtxDepth (withTransparency .default (isDefEq ty goal)) then
      return some pf
  return none

/-- The widths in `e` as literals (`(Ty.vec 8 64).width` is `512`), so facts and goals compare
syntactically and read lemmas unify with reducible transparency, which never unfolds the memory. -/
def normWidths (e : Expr) : MetaM Expr := do
  let thms ← ({} : SimpTheorems).addDeclToUnfold ``Ty.width
  return (←
        dsimp e (← Simp.mkContext (simpTheorems := #[thms])) (simprocs := #[← Simp.getSimprocs])).1

/-- Prove `Fits m p w`: a fact with the same `m` and `p`, and the same width as a literal
(`(Ty.vec 8 64).width` is `512`); not `isDefEq` on `Fits` itself, which unfolds the memory. -/
partial def fitsProof? (facts : Array (Expr × Expr)) (m p w : Expr) : MetaM (Option Expr) := do
  let w₁ ← normWidths w
  for (pf, ty) in facts do
    let_expr Fits m' p' w' := ty | continue
    if m' == m && p' == p && (w' == w || w' == w₁ || (← normWidths w') == w₁) then
      return some (mkExpectedPropHint pf (← mkAppM ``Fits #[m, p, w]))
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

/-- `a ≠ b` from the facts: either way round, by a `[…].Nodup`, or by `decide` for closed terms
(on locals it would only unfold them). -/
def neProof? (facts : Array (Expr × Expr)) (a b : Expr) : MetaM (Option Expr) := do
  let ne ← mkAppM ``Ne #[a, b]
  if let some h← findFact? facts ne then
    return some h
  if let some h← findFact? facts (← mkAppM ``Ne #[b, a]) then
    return some (← mkAppM ``Ne.symm #[h])
  for (h, ty) in facts do
    if let some h← nodupNe? h ty a b then
      return some h
  if !ne.hasFVar && (← withDefault (whnfD (← mkDecide ne))).isConstOf ``Bool.true then
    return some (← mkDecideProof ne)
  return none

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
          let ctx ←
            Simp.mkContext (simpTheorems :=
                #[← ({} : SimpTheorems).addDeclToUnfold ``Range.Disjoint,
                  ← ({} : SimpTheorems).addDeclToUnfold ``Range.of,
                  ← ({} : SimpTheorems).addDeclToUnfold ``Pointer.offsetInBits,
                  ← ({} : SimpTheorems).addDeclToUnfold ``Pointer.add,
                  ← ({} : SimpTheorems).addConst ``BitVec.toNat_add,
                  ← ({} : SimpTheorems).addConst ``BitVec.toNat_ofNat])
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
  if (← isDefEq p q) ∧ (← isDefEq v w) then
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
  let overflow ← mkAppM ``BitVec.uaddOverflow #[← mkAppM ``Pointer.offset #[p], off]
  let g ← mkFreshExprMVar (mkNot (← mkEq overflow (mkConst ``Bool.true)))
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
  let some h ← noOverflowProof? (← splitConjunctedFacts) p off | return .continue
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
  for d in ← getLCtx do
    if !d.isImplementationDetail && (← withReducible (isDefEq d.type p)) then
      return some d.toExpr
  return none

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

/-- The read functions of the `mlir_read` lemmas. -/
def readHeads : MetaM (Array Name) := do
  return (← readLemmas).foldl (fun hs l => if hs.contains l.read then hs else hs.push l.read) #[]

/-- A read fact `read (s.mem) … = x` of the state `s`: a registered read with `s.mem` an
argument. -/
def memReadFact? (heads : Array Name) (s ty : Expr) : Option (Expr × Expr) := do
  let (_, l, x) ← ty.eq?
  let h ← l.getAppFn.constName?
  guard (heads.contains h)
  guard (l.getAppArgs.any fun a => a.isAppOfArity ``GlobalState.mem 1 && a.appArg! == s)
  return (l, x)

/-- What reading through memory needs, gathered once (per step, per `simp` call): the read lemmas,
the context's facts (split, and by type), and its read facts by their left side, widths as
literals. -/
structure MemCtx where
  lemmas : Array ReadLemma
  heads : Array Name
  facts : Array (Expr × Expr)
  factMap : Std.HashMap Expr Expr
  /-- `read (S.mem) … ↦ (x, h : read (S.mem) … = x)`, for the locals `S`. -/
  reads : Std.HashMap Expr (Expr × Expr)

def MemCtx.build : MetaM MemCtx := do
  let lemmas ← readLemmas
  let heads := lemmas.foldl (fun hs l => if hs.contains l.read then hs else hs.push l.read) #[]
  let mut reads := {}
  for d in ← getLCtx do
    if d.isImplementationDetail then
      continue
    let some (_, l, x) := (← instantiateMVars d.type).eq? | continue
    unless heads.any l.isAppOf do
      continue
    unless l.getAppArgs.any fun a => a.isAppOfArity ``GlobalState.mem 1 && a.appArg!.isFVar do
      continue
    reads := reads.insert (← normWidths l) (x, d.toExpr)
  return { lemmas, heads, facts := ← splitConjunctedFacts, factMap := ← contextFactMap, reads }

/-- A read lemma's side condition from the facts: `Fits` and separation directly, others (limbs
fitting) through `mlir_transport` lemmas. -/
def dischargeRead (c : MemCtx) (goal : Expr) : MetaM (Option Expr) := do
  let goal ← instantiateMVars goal
  if let some pf := c.factMap[goal]? then
    return some pf
  match_expr goal with
  | Fits m p w =>
    fitsProof? c.facts m p w
  | Range.Disjoint a b =>
    let_expr Range.of p v := a | return none
    let_expr Range.of q w := b | return none
    disjointProof? c.facts p v q w (offsets := false)
  | Ne _ a b =>
    neProof? c.facts a b
  | _ =>
    transportWith c.factMap (← labelled `mlir_transport) 4 goal

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
      for m in ms do
        if ← m.mvarId!.isAssigned then
          continue
        let ty ← instantiateMVars (← inferType m)
        unless ← isProp ty do
          ok := false
          break
        let some pf ← dischargeRead c ty |
          ok := false;
          break
        m.mvarId!.assign pf
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

/-- `fun s => k (e with the memory m as s.mem)`: a fact about a state's memory, as a motive over
the state. -/
def memMotive (e m : Expr) (k : Expr → MetaM Expr := pure) : MetaM Expr :=
  withLocalDeclD `s (mkConst ``GlobalState) fun x => do
    mkLambdaFVars #[x]
        (←
          k
              (e.replace fun t =>
                if t == m then some (mkApp (mkConst ``GlobalState.mem) x) else none))

/-- The `S.mem` argument of a registered read, `S` a local. -/
def stateMemArg? (c : MemCtx) (e : Expr) : Option Expr := do
  guard (c.heads.any e.isAppOf)
  e.getAppArgs.find? fun a => a.isAppOfArity ``GlobalState.mem 1 && a.appArg!.isFVar

/-- A registered read of `S.mem` by its read fact, widths compared as literals: before `hS`
unfolds `S`. -/
def readMemFact (c : MemCtx) : Simp.Simproc := fun e => do
  if (stateMemArg? c e).isNone then
    return .continue
  let some (x, h) := c.reads[← normWidths e]? | return .continue
  return .visit { expr := x, proof? := some (mkExpectedPropHint h (← mkEq e x)) }

/-- A registered read of `S.mem` without a fact, through the writes of `S`'s equation `hS : S = s`
by the `mlir_read` lemmas: kept when it resolves, to a stored value or a read below every write.
`S`'s equation and memory are looked up once per `S` (`mems`). -/
def readThroughState (c : MemCtx) (mems : IO.Ref (Std.HashMap Expr (Option (FVarId × Expr)))) :
    Simp.Simproc := fun e => do
  let some m := stateMemArg? c e | return .continue
  let mem? ←
    match (← mems.get)[m]? with
    | some mem? =>
      pure mem?
    | none =>
      let mem? ←
        do
          let some hS ← findEqWithLhs? m.appArg! m!"" | pure none
          let some (_, _, s) := (← instantiateMVars (← hS.getType)).eq? | pure none
          pure (some (hS, ← normWidths (← dsimpState (← mkAppM ``GlobalState.mem #[s]))))
      mems.modify (·.insert m mem?)
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
def memSimprocs : MetaM Simp.Simprocs := do
  let c ← MemCtx.build
  let mems ← IO.mkRef {}
  let mut procs : Simp.Simprocs := {}
  let mut done : Array Name := #[]
  for l in c.lemmas do
    if done.contains l.read then
      continue
    done := done.push l.read
    -- `read _ … _`: the lemma's left side with its arguments open
    let args ←
      l.lhs.getAppArgs.mapM fun a => do
          mkFreshExprMVar (← inferType a)
    let keys ← DiscrTree.mkPath (mkAppN l.lhs.getAppFn args)
    procs := procs.addCore keys `readMemFact false (.inl (readMemFact c))
    procs := procs.addCore keys `readThroughState true (.inl (readThroughState c mems))
  return procs

end

end LeanMLIR.RIR.Tactic
