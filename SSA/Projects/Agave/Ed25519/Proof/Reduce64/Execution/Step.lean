import SSA.Projects.RIR.Run.Tactic
import SSA.Projects.RIR.Run.Tactic.Step.Common
import SSA.Projects.RIR.Run.Tactic.Step.Syntax
import SSA.Projects.RIR.Run.Tactic.Env
import Lean.Elab.Tactic

/-! A state-reading GEP leaves the state unchanged but is not a pure instruction.
This small tactic uses the effectful stepping theorem and kernel-checked
simplification, then reuses the ordinary register-sealing machinery. -/
namespace Agave.Ed25519.Reduce64.Execution
open LeanMLIR.RIR
open Lean Elab Tactic Meta

meta section

syntax (name := stepReduceGep) "step_reduce_gep" LeanMLIR.RIR.stepSimpArgs : tactic

@[tactic stepReduceGep]
def evalStepReduceGep : Tactic := fun stx => withMainContext do
  let ⟨runGoal, main⟩ ← LeanMLIR.RIR.rewriteStep (← getMainGoal)
    ``LeanMLIR.RIR.BasicBlock.runBodyFrom_step_of_run
  let some runGoal ← LeanMLIR.RIR.dsimpMlirInstr? runGoal
    | throwError "Could not unfold the GEP instruction"
  -- GEP writes a possibly-poison pointer and leaves the state unchanged. Keep
  -- the environment opaque here so sealing retains its argument facts.
  runGoal.refl
  setGoals [main]
  let args := LeanMLIR.RIR.StepArgs.parse stx[1] mkNullNode mkNullNode mkNullNode
  LeanMLIR.RIR.finishStep .inline .inline false args.simpArgs true

/-- Resolve a staged interface through writes without simplifying the arithmetic
values. The resulting equalities are proved explicitly lane by lane. -/
private partial def closeReduceReads (g : MVarId) : TacticM (List MVarId) :=
  g.withContext do
    let ty ← whnfR (← instantiateMVars (← g.getType))
    if let some (a, b) := ty.and? then
      let ga ← mkFreshExprSyntheticOpaqueMVar a
      let gb ← mkFreshExprSyntheticOpaqueMVar b
      g.assign (mkApp4 (mkConst ``And.intro) a b ga gb)
      return (← closeReduceReads ga.mvarId!) ++ (← closeReduceReads gb.mvarId!)
    let some (_, lhs, rhs) := ty.eq? | return [g]
    unless lhs.isAppOfArity ``Env.read 4 do return [g]
    let some (v, pf) ← LeanMLIR.RIR.Tactic.walkRead (lhs.getArg! 2) (lhs.getArg! 3)
      | return [g]
    let rest ← mkFreshExprSyntheticOpaqueMVar (← mkEq v rhs)
    g.assign (← mkEqTrans pf rest)
    try
      rest.mvarId!.refl
      return []
    catch _ =>
      return [rest.mvarId!]

elab "reduce_env_reads" : tactic => do
  replaceMainGoal (← closeReduceReads (← getMainGoal))

end
end Agave.Ed25519.Reduce64.Execution
