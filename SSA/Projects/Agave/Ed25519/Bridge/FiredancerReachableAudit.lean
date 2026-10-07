import SSA.Projects.Agave.Ed25519.Bridge.FiredancerReachableSourceInit

/-- info: Reachable Firedancer verifier execution uses exactly the three standard foundations. -/
#guard_msgs in
open Lean Elab Command in
run_cmd do
  let expected : List Name := [`propext, `Classical.choice, `Quot.sound]
  let targets : List Name := [
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.reachableInit,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.reachableCalls,
    ``Agave.Ed25519.Bridge.firedancerReachableSource_conforms,
    ``Agave.Ed25519.Bridge.firedancerReachable_ready_executionRefines,
    ``Agave.Ed25519.Bridge.firedancerReachable_ready_success_iff,
    ``Agave.Ed25519.Bridge.agave_iff_firedancerReachable_ready_and_canonical]
  for target in targets do
    let actual := (← collectAxioms target).toList
    unless actual.length == expected.length && expected.all actual.contains do
      throwError "Unexpected reachable verifier axioms for {target}: {actual}"
  logInfo "Reachable Firedancer verifier execution uses exactly the three standard foundations."
