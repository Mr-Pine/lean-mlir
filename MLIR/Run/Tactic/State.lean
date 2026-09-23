module

public import MLIR.Semantics.Func
public import MLIR.Run.Tactic.Parse
public import MLIR.Run.Tactic.Util
public meta import Lean.Elab.Tactic

namespace MLIR.Tactic

open Lean Elab Tactic Meta

public meta section

section SealState

structure SealedState where
  S' : FVarId
  hS' : FVarId
  hS : FVarId

def sealState (S : Expr) : TacticM SealedState :=
  withMainContext do
    let (g, goal) ← getGoalType
    let runBodyFrom ← getRunBodyFrom goal
    let S' := runBodyFrom.state
    let hS ← findEqWithLhs S m!"of the form `{S} = _`"
    let some (_, _, S₀chain) :=
      (← instantiateMVars (← hS.getType)).eq? | throwError "expected an equation"
    -- new state as function of the old one
    let abstract := Expr.lam `s (← inferType S) (← kabstract S' S) .default
    let (fvs, g) ←
      generalizeOpaque g (hyps := #[]) S' `S'
          #[⟨`hS', (mkEq · (abstract.beta #[S₀chain])), ← mkCongrArg abstract (.fvar hS)⟩]
    replaceMainGoal [g]
    return ⟨fvs[0]!, fvs[1]!, hS⟩

end SealState

end

end MLIR.Tactic
