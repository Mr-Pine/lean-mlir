import SSA.Projects.Agave.Ed25519.Proof.Verifier.LinkedSerialBackendReady

/-! Every transport fact uses only the standard foundations. The final caller
adapter is also checked against its exact three-axiom inventory. -/
/-- info: Serial prefix transport and caller readiness retain only standard foundations. -/
#guard_msgs in
open Lean Elab Command in
run_cmd do
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  let targets : List Name := [
    ``Agave.Ed25519.Verifier.Execution.Dalek.AllocationShape.block,
    ``Agave.Ed25519.Verifier.Execution.Dalek.AllocationShape.blockAt,
    ``Agave.Ed25519.Verifier.Execution.Dalek.blackBox_allocationShape,
    ``Agave.Ed25519.Verifier.Execution.Dalek.bytesEq_allocationShape,
    ``Agave.Ed25519.Verifier.Execution.Dalek.pointEq_allocationShape,
    ``Agave.Ed25519.Verifier.Execution.Dalek.scalarReduce_allocationShape,
    ``Agave.Ed25519.Verifier.Execution.Dalek.cofactor_allocationShape,
    ``Agave.Ed25519.Verifier.Execution.Dalek.cache_allocationShape,
    ``Agave.Ed25519.Verifier.Execution.Dalek.pointTrace_allocationShape,
    ``Agave.Ed25519.Verifier.Execution.Dalek.scalarTrace_allocationShape,
    ``Agave.Ed25519.Verifier.Execution.Dalek.serialGlobals_afterSignature,
    ``Agave.Ed25519.Verifier.Execution.Dalek.serialGlobals_output,
    ``Agave.Ed25519.Verifier.Execution.Dalek.serialGlobals_readOnly,
    ``Agave.Ed25519.Verifier.Execution.Dalek.SerialBackendReadiness.cacheReady,
    ``Agave.Ed25519.Verifier.Execution.Dalek.SerialBackendReadiness.scalarReady,
    ``Agave.Ed25519.Verifier.Execution.Dalek.SerialBackendReadiness.bodyReady_of_ranges,
    ``Agave.Ed25519.Verifier.Execution.Dalek.SerialBackendReadiness.bodyReady,
    ``Agave.Ed25519.Verifier.Execution.Dalek.SerialBackendReadiness.coldReady,
    ``Agave.Ed25519.Verifier.Execution.LinkedColdLeavesUnder.BackendInputs.combine,
    ``Agave.Ed25519.Verifier.Execution.LinkedColdLeavesUnder.serialShaSeparate,
    ``Agave.Ed25519.Verifier.Execution.LinkedColdLeavesUnder.serialBackendInputs]
  for target in targets do
    for dependency in (← collectAxioms target) do
      unless allowed.contains dependency do
        throwError "Uninventoried dependency of {target}: {dependency}"
  let final := ``Agave.Ed25519.Verifier.Execution.LinkedColdLeavesUnder.serialBackendInputs
  let actual := (← collectAxioms final).toList
  unless actual.length == allowed.length && allowed.all actual.contains do
    throwError "Unexpected exact inventory for {final}: {actual}"
  logInfo "Serial prefix transport and caller readiness retain only standard foundations."
