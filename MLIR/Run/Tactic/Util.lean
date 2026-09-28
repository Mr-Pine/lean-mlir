module

public import MLIR.Semantics.Func
public import MLIR.Run.Tactic.Parse
public meta import Lean.Elab.Tactic

namespace MLIR.Tactic

open Lean Elab Tactic Meta

public meta section

structure GeneralizeFact where
  /-- Name of the fact -/
  name : Name
  /-- Generate the fact's statement from the abstracted variable -/
  mkType : Expr → MetaM Expr
  /-- Proof of `mkType (generalized expression)` -/
  proof : Expr

/-- Generalize `e` in the goal `g` and hyps `hyps` to a fresh opaque local `xName`.
`facts` specifies the hypotheses to generate from the generalization.
`occs` specifies what occurences to generalize. -/
def generalizeOpaque (g : MVarId) (hyps : Array FVarId := #[]) (e : Expr) (xName : Name)
    (facts : Array GeneralizeFact) (occs : Occurrences := Occurrences.all) :
    MetaM (Array FVarId × MVarId) := do
  let (reverted, g) ← g.revert (preserveOrder := true) hyps
  g.withContext do
      let ty ← inferType e -- Type of the expression to generalize
      -- reducible: `e` occurs verbatim, and default transparency unfolds every `Env.write`
      let tgtAbstract ←
        withReducible <| kabstract (← instantiateMVars (← g.getType)) e
            occs -- e abstracted as a loose bound variable
      let tyNew ←
        withLocalDeclD xName ty
            (fun x => do
              let mut expr := tgtAbstract.instantiate1 x
              for ⟨name, mk, _⟩ in facts.reverse do -- reverse to get nesting order correct
                let factTy ← mk x
                let abstracted ←
                  withLocalDeclD name factTy
                      (fun h =>
                        mkForallFVars #[h]
                          expr -- Binds `h` (with name `name`) as universally quantified
                        )
                expr := abstracted
              mkForallFVars #[x] expr)
      unless ← isTypeCorrect tyNew do
        throwTacticEx `generalizeOpaque g m!"result is not type correct{indentExpr tyNew}"
      let gNew ← mkFreshExprSyntheticOpaqueMVar tyNew (tag := ← g.getTag)
      g.assign
          (mkAppN gNew
            (#[e] ++
              facts.map
                (GeneralizeFact.proof))) -- Close the old goal by the new goal closed with the abstracted expression and the fact proof
      let (fvs, g) ← gNew.mvarId!.introNP (1 + facts.size) -- Intro the new variable and facts
      let (_, g) ← g.introNP reverted.size -- Revert reverting
      return (fvs, g)

/-- The `Nat` behind a `Dst`'s index, when it is a literal. -/
def dstIndex? (d : Expr) : MetaM (Option Nat) := do
  let i ← whnf (← mkAppM ``Dst.i #[d])
  (Meta.evalNat (← whnf (← mkAppM ``Fin.val #[i]))).run

/-- Replace the body index by its `Nat` literal: `0 + 1 + 1` becomes `2`. -/
def reduceIndex (g : MVarId) : MetaM MVarId :=
  g.withContext do
    let goal ← instantiateMVars (← g.getType)
    let idx := (← getRunBodyFrom goal).idx
    let some literal ← (Meta.evalNat idx).run | return g
    let lit := mkNatLit literal
    if lit == idx then
      return g
    let body ← kabstract goal idx
    let motive := Expr.lam `pos (mkConst ``Nat) body .default
    let proof := mkExpectedPropHint (← mkEqRefl idx) (← mkEq idx lit)
    g.replaceTargetEq (body.instantiate1 lit) (← mkCongrArg motive proof)

def finNLit? (n : Expr) : MetaM (Option Nat) := do
  if let some k← (Meta.evalNat (← mkAppM ``Fin.val #[n])).run then
    return k
  let_expr OfNat.ofNat _ n _ := n | return none
  return n.rawNatLit?

/-- Replace `e` in `m`'s target by `r.expr`, using the proof `e = r.expr` from `r`. -/
def replaceBySimp (m : MVarId) (e : Expr) (r : Simp.Result) : MetaM MVarId := do
  let body ←
    kabstract (← instantiateMVars (← m.getType)) e -- Abstract the expression value in the mvar
  let motive := Expr.lam `val (← inferType e) body .default -- As a lambda
  let simpProof ← r.getProof' e
  let mvarProof ← mkCongrArg motive simpProof
  let newMVar := body.instantiate1 r.expr
  m.replaceTargetEq newMVar mvarProof -- Using congruence, get proof over goal

/-- The hypotheses whose statement mentions `e`, except `except`. -/
def hypsMentioning (e : Expr) (except : Array FVarId := #[]) : MetaM (Array FVarId) := do
  (← getLCtx).foldlM (init := #[]) fun acc d => do
      if d.isImplementationDetail || except.contains d.fvarId then
        return acc
      return if e.occurs (← instantiateMVars d.type) then acc.push d.fvarId else acc

private def findEqsWithLhs (lhs : Expr) : MetaM (Array FVarId) := do
  (← getLCtx).foldlM (init := #[])
      (fun acc d => do
        if d.isImplementationDetail then
          return acc
        let some (_, l, _) := (← instantiateMVars d.type).eq? | return acc
        return if l == lhs then acc.push d.fvarId else acc)

/-- The unique hypothesis `_ : lhs = _`, if there is one. -/
def findEqWithLhs? (lhs : Expr) (what : MessageData) : MetaM (Option FVarId) := do
  match ← findEqsWithLhs lhs with
  | #[] =>
    return none
  | #[h] =>
    return some h
  | hs =>
    throwError "ambiguous: {hs.size} hypotheses {what}"

/-- The unique hypothesis `_ : lhs = _`. -/
def findEqWithLhs (lhs : Expr) (what : MessageData) : MetaM FVarId := do
  let h ← findEqWithLhs? lhs what
  let some (h) := h | throwError "no hypothesis {what}"
  return h

end

end MLIR.Tactic
