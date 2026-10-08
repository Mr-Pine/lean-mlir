import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMAppendMessageRepresents

/-- info: Actual arbitrary-message SLLVM append execution uses only standard Lean axioms. -/
#guard_msgs in
open Lean Elab Command in
run_cmd do
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  let endpoints : List Name := [
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.append_message_short_body,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.append_message_fill_body,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.append_message_fill_tail_body,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.append_message_direct_body,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.MessageExecution.Ready.buffered_core,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.MessageExecution.Ready.direct_core,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.MessageExecution.resultState,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.MessageExecution.resultState_other,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.MessageExecution.resultState_wf,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.MessageExecution.body,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.MessageExecution.call,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.MessageExecution.executes,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.MessageExecution.Ready.result,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.MessageExecution.executes_ready,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.MessageExecution.represents,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.MessageExecution.after_R_A]
  for endpoint in endpoints do
    for dependency in (← collectAxioms endpoint) do
      unless allowed.contains dependency do
        throwError "Unexpected axiom {dependency} in {endpoint}"
  logInfo "Actual arbitrary-message SLLVM append execution uses only standard Lean axioms."
