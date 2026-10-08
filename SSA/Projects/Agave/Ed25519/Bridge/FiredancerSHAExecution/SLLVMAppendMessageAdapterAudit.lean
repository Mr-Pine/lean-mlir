import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMAppendMessageAdapter

/-- info: The exact reachable SLLVM message adapter uses only standard Lean axioms. -/
#guard_msgs in
open Lean Elab Command in
run_cmd do
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  let endpoints : List Name := [
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.MessageExecution.sourceRead_window_congr,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.MessageExecution.resultState_context_congr,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.MessageExecution.snapshot_bytes,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.MessageExecution.resultState_context_length,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.MessageExecution.reachable_message]
  for endpoint in endpoints do
    for dependency in (← collectAxioms endpoint) do
      unless allowed.contains dependency do
        throwError "Unexpected axiom {dependency} in {endpoint}"
  logInfo "The exact reachable SLLVM message adapter uses only standard Lean axioms."
