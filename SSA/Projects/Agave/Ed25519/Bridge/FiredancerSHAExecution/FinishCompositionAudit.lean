import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.FinishCompositionSource

#print axioms Agave.Ed25519.Bridge.FiredancerSHAExecution.Finish.call
#print axioms Agave.Ed25519.Bridge.FiredancerSHAExecution.Finish.call_digest_source

/-- info: Firedancer concrete finalization uses only standard Lean axioms. -/
#guard_msgs in
open Lean Elab Command in
run_cmd do
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  let endpoints : List Name := [
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Finish.compressionState_pack,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Finish.beforeOutput_fold,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Finish.finishState_chaining,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Finish.finishState_digest,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Finish.call_digest,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Finish.LastReady,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Finish.lastEntry,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Finish.params1,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Finish.params2,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Finish.entry_short,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Finish.entry_long,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Finish.entry_lastReady,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Finish.long_lastReady,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Finish.long_block,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Finish.last_block,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Finish.disjoint_subrange,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Finish.finishState_readAt_frame,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Finish.finishState_metadata,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Finish.ConstantsReady,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Finish.ConstantsReady.storeAt,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Finish.chainMemory_readState,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Finish.readState_of_chainMemory,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Finish.readState_store_buffer,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Finish.markerMemory_state,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Finish.longMemory_state,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Finish.lastMemory_state,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Finish.coreCallState_state,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Finish.core_call_context,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Finish.outputMemory_state,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Finish.run,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Finish.call,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Finish.constantsReady_source,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Finish.finishState_wf,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Finish.Result,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Finish.call_digest_source,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Finish.Ready,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Finish.Ready.storeAt,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Finish.markerState,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Finish.longState,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Finish.lastState,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Finish.compressionState,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Finish.finalOutputState,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Finish.beforeOutput,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Finish.finishState,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Finish.Ready.marker,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Finish.Ready.long,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Finish.Ready.last,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Finish.Ready.compression,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Finish.Ready.preOutput,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Finish.compression_call,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Finish.finishState_output,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Finish.finishState_alloc,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Finish.finishState_erase,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Finish.finishState_other_block]
  for endpoint in endpoints do
    for dependency in (← collectAxioms endpoint) do
      unless allowed.contains dependency do
        throwError "Unexpected axiom {dependency} in {endpoint}"
  logInfo "Firedancer concrete finalization uses only standard Lean axioms."
