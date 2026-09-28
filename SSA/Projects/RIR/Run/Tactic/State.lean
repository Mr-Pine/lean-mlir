module

public import SSA.Projects.RIR.Semantics.Func
public import SSA.Projects.RIR.Run.Tactic.Parse
public import SSA.Projects.RIR.Run.Tactic.Util
public meta import Lean.Elab.Tactic

namespace LeanMLIR.RIR.Tactic

open Lean Elab Tactic Meta

public meta section

section SealState

structure SealedState where
  S' : FVarId
  hS' : FVarId
  hS : FVarId

/-- The new state with its projections reduced -/
def dsimpState (e : Expr) : MetaM Expr := do
  return (← dsimp e (← Simp.mkContext)).1

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
          #[⟨`hS', (mkEq · (← dsimpState (abstract.beta #[S₀chain]))),
              ← mkCongrArg abstract (.fvar hS)⟩]
    replaceMainGoal [g]
    return ⟨fvs[0]!, fvs[1]!, hS⟩

/-- Name the goal's state `S`, with `hS : S = s`, unless it has an equation already: a loop's
proof starts from a bare state `s`, whose facts should stay about `s`. -/
def ensureStateEq : TacticM Unit :=
  withMainContext do
    let (g, goal) ← getGoalType
    let s := (← getRunBodyFrom goal).state
    if (← findEqWithLhs? s m!"`{s} = _`").isSome then
      return
    let (_, g) ← generalizeOpaque g (hyps := #[]) s `S #[⟨`hS, (mkEq · s), ← mkEqRefl s⟩]
    replaceMainGoal [g]

end SealState

end

end LeanMLIR.RIR.Tactic
