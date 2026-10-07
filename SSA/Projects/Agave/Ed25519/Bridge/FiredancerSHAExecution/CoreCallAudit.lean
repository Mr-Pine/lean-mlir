import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.CoreConstants

#print axioms Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.coreEntry_body
#print axioms Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.coreEntry_block
#print axioms Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.outer_start
#print axioms Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.feedforward_body
#print axioms Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.core_run_one
#print axioms Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.core_call_one
#print axioms Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.core_call_one_packed
#print axioms Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.coreCallState_readAt_frame

/-- info: Firedancer core entry, eighty rounds, feedforward, return and caller frame use only standard Lean axioms. -/
#guard_msgs in
open Lean Elab Command in
run_cmd do
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  let endpoints : List Name := [
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.coreEntry_body,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.coreEntry_block,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.coreEntry_live,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.coreEntry_frame,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.outer_start,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.outer_decrement,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.feedforward_body,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.feedforward_last,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.core_return,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.feedforwardMemory_eq,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.core_one_from_outer,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.core_run_one,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.core_call_one,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.core_call_one_packed,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.coreCallState_wf,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.coreCallState_live,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.coreCallState_read,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.coreCallState_other_block,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.coreCallState_readAt_frame,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.constants_present_range,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.constants_present_word,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.core_call_one_source,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.coreCallState_constants]
  for endpoint in endpoints do
    for dependency in (← collectAxioms endpoint) do
      unless allowed.contains dependency do
        throwError "Unexpected axiom {dependency} in {endpoint}"
  logInfo "Firedancer core entry, eighty rounds, feedforward, return and caller frame use only standard Lean axioms."
