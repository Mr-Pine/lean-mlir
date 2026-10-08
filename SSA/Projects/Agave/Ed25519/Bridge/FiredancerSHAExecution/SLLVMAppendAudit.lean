import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMAppendReachable

/-- info: SLLVM append zero/32-byte execution and stream observations use only standard Lean axioms. -/
#guard_msgs in
open Lean Elab Command in
run_cmd do
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  let endpoints : List Name := [
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.sourceRead,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.sourceReadBytes,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.ContextRepresents,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.ContextRepresents.of_live_eq,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.append_zero_body,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.append_zero_call,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.append_zero_represents,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.append32_body,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.append32_call,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.append32_frame,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.append32_buffered_body,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.append32_buffered_call,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.append32_buffered_frame,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.append32Memory_block,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.append32BufferedMemory_block,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.append32Block_live,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.append32Block_count,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.initBlock_live,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.initBlock_count,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.append32_reachable,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.append32_buffered_reachable]
  for endpoint in endpoints do
    for dependency in (← collectAxioms endpoint) do
      unless allowed.contains dependency do
        throwError "Unexpected axiom {dependency} in {endpoint}"
  logInfo "SLLVM append zero/32-byte execution and stream observations use only standard Lean axioms."
