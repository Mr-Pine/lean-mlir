import SSA.Projects.Agave.Ed25519.Proof.Reduce64.Execution.StageTypes
import SSA.Projects.Agave.Ed25519.Proof.Reduce64.Execution.Step

namespace Agave.Ed25519.Reduce64.Execution
open LeanMLIR.RIR

attribute [local implicit_reducible] Ty.width
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- Execute only the literal/poison setup prefix, then invoke a continuation
whose interface contains the live constants and original argument facts. -/
theorem constants_cont {α : Type} (E : Env program.Γ) (s : GlobalState)
    (dst src : Pointer)
    (κ : Env program.Γ × GlobalState → PoisonOr α) (result : PoisonOr α)
    (hargs : E.args = (program.args (.value dst) (.value src)).get)
    (hnext : ∀ E', E'.args = (program.args (.value dst) (.value src)).get →
      KernelConstants E' →
      (program.entry.runBodyFrom E' 54 s >>= κ) = result) :
    (program.entry.runBodyFrom E 0 s >>= κ) = result := by
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  try subst S
  apply hnext E
  · assumption
  · unfold KernelConstants
    env_reads

end Agave.Ed25519.Reduce64.Execution
