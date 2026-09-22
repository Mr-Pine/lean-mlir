module

public import SSA.Projects.RIR.Semantics.Func
public meta import Lean.Elab.Tactic

namespace LeanMLIR.RIR.Tactic

open Lean Elab Tactic Meta

public meta section

structure GeneralizeFact where
  /-- Name of the fact -/
  name : Name
  /-- Generate the fact's statement from the abstracted variable -/
  mkType : Expr → MetaM Expr
  /-- Proof of `mkType (generalized expression)` -/
  proof : Expr

/-- Generalize `e` in the goal `g` to a fresh opaque local `xName`.
`facts` specifies the hypotheses to generate from the generalization.
`occs` specifies what occurences to generalize. -/
def generalizeOpaque (g : MVarId) (e : Expr) (xName : Name) (facts : Array GeneralizeFact)
    (occs : Occurrences := Occurrences.all) : MetaM (Array FVarId × MVarId) :=
  g.withContext do
    let ty ← inferType e -- Type of the expression to generalize
    let tgtAbstract ←
      kabstract (← instantiateMVars (← g.getType)) e occs -- e abstracted as a loose bound variable
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
    gNew.mvarId!.introNP (1 + facts.size) -- Intro the new variable and facts

end

end LeanMLIR.RIR.Tactic
