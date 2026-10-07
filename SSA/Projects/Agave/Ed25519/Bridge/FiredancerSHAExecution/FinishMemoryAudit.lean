import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.FinishOutputMemory
import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.FinishPaddingMemory

#print axioms Agave.Ed25519.Bridge.FiredancerSHAExecution.Finish.outputMemory_bytes
#print axioms Agave.Ed25519.Bridge.FiredancerSHAExecution.Finish.onlyPaddingBlock_bytes
#print axioms Agave.Ed25519.Bridge.FiredancerSHAExecution.Finish.firstPaddingBlock_bytes
#print axioms Agave.Ed25519.Bridge.FiredancerSHAExecution.Finish.lastPaddingBlock_bytes

/-- info: Firedancer finalizer readback uses only standard Lean axioms. -/
#guard_msgs in
open Lean Elab Command in
run_cmd do
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  let endpoints : List Name := [
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Finish.swappedState,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Finish.pack_swappedState,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Finish.outputMemory_eq,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Finish.outputMemory_bytes,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Finish.storeSuffix_bytes,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Finish.markerMemory_bytes,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Finish.longMemory_bytes,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Finish.longPadding_bytes,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Finish.lastMemory_bytes,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Finish.splitLength_bytes,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Finish.lastMemory_lengthField,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Finish.firstPaddingBlock_bytes,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Finish.onlyPaddingBlock_bytes,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Finish.lastPaddingBlock_bytes]
  for endpoint in endpoints do
    for dependency in (← collectAxioms endpoint) do
      unless allowed.contains dependency do
        throwError "Unexpected axiom {dependency} in {endpoint}"
  logInfo "Firedancer finalizer readback uses only standard Lean axioms."
