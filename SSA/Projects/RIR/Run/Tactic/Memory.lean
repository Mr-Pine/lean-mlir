module

public import SSA.Projects.RIR.Semantics.Effectful.Memory.Operations
public import SSA.Projects.RIR.Memory.Range
public import SSA.Projects.RIR.Run.Tactic.Util
public import SSA.Projects.RIR.Run.Memory
public meta import Lean.Elab.Tactic

namespace LeanMLIR.RIR.Tactic

open Lean Elab Tactic Meta

public meta section

/-- Splits all conjuncted facts `h : a ∧ b ∧ c ∧ ...` into `#[(h.1, a), (h.2.1, b), (h.2.2.1, c), ...]` -/
partial def splitConjunctedFacts : MetaM (Array (Expr × Expr)) := do
  let mut out := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail || !(← isProp d.type) then
      continue
    out ← go (mkFVar d.fvarId) (← instantiateMVars d.type) out
  return out
where go (pf ty : Expr) (acc : Array (Expr × Expr)) : MetaM (Array (Expr × Expr)) := do
    let ty' ← whnfR ty
    match_expr ty' with
    | And a b =>
      do
        let acc ← go (mkApp3 (mkConst ``And.left) a b pf) a acc
        go (mkApp3 (mkConst ``And.right) a b pf) b acc
    | _ =>
      return acc.push (pf, ty)

def findFact? (facts : Array (Expr × Expr)) (goal : Expr) : MetaM (Option Expr) := do
  for (pf, ty) in facts do
    if ← withNewMCtxDepth (withTransparency .default (isDefEq ty goal)) then
      return some pf
  return none

/-- Prove `Fits m p w` -/
partial def fitsProof? (facts : Array (Expr × Expr)) (m p w : Expr) : MetaM (Option Expr) := do
  let goal ← mkAppM ``Fits #[m, p, w]
  if let some h← findFact? facts goal then
    return some h
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

/-- `(Range.of p v).Disjoint (Range.of q w)` -/
def disjointProof? (facts : Array (Expr × Expr)) (p v q w : Expr) : MetaM (Option Expr) := do
  let goal ← mkAppM ``Range.Disjoint #[← mkAppM ``Range.of #[p, v], ← mkAppM ``Range.of #[q, w]]
  -- different blocks
  let pid ← mkAppM ``Pointer.id #[p]
  let qid ← mkAppM ``Pointer.id #[q]
  if let some h← findFact? facts (← mkAppM ``Ne #[pid, qid]) then
    return some (mkAppN (mkConst ``Range.disjoint_of_id_ne) #[p, q, v, w, h])
  if let some h← findFact? facts (← mkAppM ``Ne #[qid, pid]) then
    return some (mkAppN (mkConst ``Range.disjoint_of_id_ne) #[v, w, p, q, ← mkAppM ``Ne.symm #[h]])
  -- different blocks, decidably (literal ids): `decide`, evaluated first since
  -- `mkDecideProof` does not check
  let ne ← mkAppM ``Ne #[pid, qid]
  if
      ←
        withTransparency .default do
            return (← whnfD (← mkDecide ne)).isConstOf ``Bool.true then
    return some (mkAppN (mkConst ``Range.disjoint_of_id_ne) #[v, w, p, q, ← mkDecideProof ne])
  -- the same block: offsets, by `omega`
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
    let ctx ←
      Simp.mkContext (simpTheorems :=
          #[← (← getSimpTheorems).addDeclToUnfold ``BitVec.uaddOverflow])
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

end

end LeanMLIR.RIR.Tactic
