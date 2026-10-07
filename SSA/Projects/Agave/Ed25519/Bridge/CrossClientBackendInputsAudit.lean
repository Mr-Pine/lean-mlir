import SSA.Projects.Agave.Ed25519.Bridge.CrossClientBackendInputs
import SSA.Projects.Agave.Ed25519.Bridge.CrossClientGuardedCaller

/-! Audit actual global transport and the concrete serial/AVX2 composition. -/
/-- info: Concrete backend readiness transport uses only standard foundations. -/
#guard_msgs in
open Lean Elab Command in
run_cmd do
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  let targets : List Name := [
    ``Agave.Ed25519.Verifier.Execution.Dalek.Avx2BackendReadiness.ready_output_of_globalShape,
    ``Agave.Ed25519.Verifier.Execution.Dalek.Avx2BackendReadiness.ready_output,
    ``Agave.Ed25519.Verifier.Execution.Dalek.Avx2BackendReadiness.ready_readOnly,
    ``Agave.Ed25519.Verifier.Execution.Dalek.Avx2BackendReadiness.cacheReady,
    ``Agave.Ed25519.Verifier.Execution.Dalek.Avx2BackendReadiness.scalarReady,
    ``Agave.Ed25519.Verifier.Execution.Dalek.Avx2BackendReadiness.bodyReady_of_ranges,
    ``Agave.Ed25519.Verifier.Execution.Dalek.Avx2BackendReadiness.coldReady,
    ``Agave.Ed25519.Verifier.Execution.BackendReadiness.avxShaSeparate,
    ``Agave.Ed25519.Verifier.Execution.BackendReadiness.inputs]
  for target in targets do
    for dependency in (← collectAxioms target) do
      unless allowed.contains dependency do
        throwError "Unexpected dependency of {target}: {dependency}"
  let guardedTargets : List Name := [
    ``Agave.Ed25519.Verifier.Execution.Dalek.program_from_entry_of_leaf_contracts_cold_guarded,
    ``Agave.Ed25519.Verifier.Execution.Dalek.program_call_of_leaf_contracts_cold_guarded,
    ``Agave.Ed25519.Verifier.Execution.LinkedColdLeavesGuarded.primitive_calls,
    ``Agave.Ed25519.Verifier.Execution.LinkedColdLeavesGuarded.observe,
    ``Agave.Ed25519.Bridge.parameterizedCaller_guarded_cold_crossClient_observations,
    ``Agave.Ed25519.Bridge.parameterizedCaller_guarded_cold_crossClient_of_canonical]
  for target in guardedTargets do
    let actual := (← collectAxioms target).toList
    unless actual.length == allowed.length && allowed.all actual.contains do
      throwError "Unexpected guarded-path inventory of {target}: {actual}"
  let target := ``Agave.Ed25519.Verifier.Execution.BackendReadiness.inputs
  let actual := (← collectAxioms target).toList
  unless actual.length == allowed.length && allowed.all actual.contains do
    throwError "Unexpected exact inventory of {target}: {actual}"
  logInfo "Concrete backend readiness transport uses only standard foundations."
