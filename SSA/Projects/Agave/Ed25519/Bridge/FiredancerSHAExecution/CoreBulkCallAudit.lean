import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.CoreBulkCall
import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.CoreCallAudit

#print axioms Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.core_call_blocks
#print axioms Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.core_call_blocks_source
#print axioms Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.coreBulkState_effect

/-- info: Arbitrary positive-block Firedancer core calls use only standard Lean axioms. -/
#guard_msgs in
open Lean Elab Command in
run_cmd do
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  let endpoints : List Name := [
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.core_call_blocks_succ,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.core_call_blocks,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.core_call_blocks_source,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.coreBulkState_effect,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.coreBulkState_wf,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.coreBulkState_live,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.coreBulkState_read,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.coreBulkState_readAt_frame,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.coreBulkState_constants]
  for endpoint in endpoints do
    for dependency in (← collectAxioms endpoint) do
      unless allowed.contains dependency do
        throwError "Unexpected axiom {dependency} in {endpoint}"
  logInfo "Arbitrary positive-block Firedancer core calls use only standard Lean axioms."
