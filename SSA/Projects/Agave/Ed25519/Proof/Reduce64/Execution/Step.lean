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

end
end Agave.Ed25519.Reduce64.Execution
