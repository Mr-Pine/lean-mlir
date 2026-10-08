import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMAppendFinish

/-- info: The composed actual SLLVM append and finalizer use only standard Lean axioms. -/
#guard_msgs in
open Lean Elab Command in
run_cmd do
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  let endpoint :=
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.MessageExecution.append_finish_after_R_A
  for dependency in (← collectAxioms endpoint) do
    unless allowed.contains dependency do
      throwError "Unexpected axiom {dependency} in {endpoint}"
  logInfo "The composed actual SLLVM append and finalizer use only standard Lean axioms."
