import SSA.Projects.Agave.Ed25519.Bridge.AgaveBcmpOnly

/-- info: Concrete Agave verifier endpoints retain exactly the three standard foundations. -/
#guard_msgs in
open Lean Elab Command in
run_cmd do
  let expected : List Name := [`propext, `Classical.choice, `Quot.sound]
  let targets : List Name := [
    ``Agave.Ed25519.Verifier.Execution.ColdInput.linked_decoder_callerBlocks,
    ``Agave.Ed25519.Verifier.Execution.Dalek.decoderPrefix_of_cold_trace,
    ``Agave.Ed25519.Bridge.AgaveReady.decoderPrefix,
    ``Agave.Ed25519.Bridge.AgaveReady.inputs,
    ``Agave.Ed25519.Bridge.AgaveReady.verify_eq_strict,
    ``Agave.Ed25519.Bridge.AgaveReady.primitive_calls,
    ``Agave.Ed25519.Bridge.AgaveReady.call_strict,
    ``Agave.Ed25519.Bridge.AgaveReady.observe_strict,
    ``Agave.Ed25519.Bridge.AgaveReady.call_strict_bcmp]
  for target in targets do
    let actual ← collectAxioms target
    unless actual.size == expected.length do
      throwError "Unexpected axiom count for {target}: {actual}"
    for dependency in actual do
      unless expected.contains dependency do
        throwError "Uninventoried dependency of {target}: {dependency}"
    for dependency in expected do
      unless actual.contains dependency do
        throwError "Missing expected dependency of {target}: {dependency}"
  for target in [``Agave.Ed25519.Verifier.Execution.Dalek.ColdCallTrace.states_eq,
      ``Agave.Ed25519.Bridge.AgaveReady.wrapper_eq_of_compareBytes_eq] do
    for dependency in (← collectAxioms target) do
      unless expected.contains dependency do
        throwError "Uninventoried dependency of {target}: {dependency}"
  logInfo "Concrete Agave verifier endpoints retain exactly the three standard foundations."
