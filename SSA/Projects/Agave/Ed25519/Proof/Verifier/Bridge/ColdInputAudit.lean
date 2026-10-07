import SSA.Projects.Agave.Ed25519.Bridge.CrossClientColdCaller

/-- info: Cold caller-input closure uses only standard Lean axioms. -/
#guard_msgs in
open Lean Elab Command in
run_cmd do
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  let endpoints : List Name := [
    ``Agave.Ed25519.Verifier.Execution.ColdInput.afterSignature_blocks,
    ``Agave.Ed25519.Verifier.Execution.ColdInput.decoded_coordinates,
    ``Agave.Ed25519.Verifier.Execution.ColdInput.decoderCall,
    ``Agave.Ed25519.Verifier.Execution.ColdInput.decoderResult_of_contract,
    ``Agave.Ed25519.Verifier.Execution.ColdInput.afterSignature_publicKey,
    ``Agave.Ed25519.Verifier.Execution.ColdInput.signatureMemory,
    ``Agave.Ed25519.Verifier.Execution.ColdInput.ReductionGlobals.ready,
    ``Agave.Ed25519.Verifier.Execution.ColdInput.coldReady,
    ``Agave.Ed25519.Verifier.Execution.ColdInput.inputs_of_decoder,
    ``Agave.Ed25519.Verifier.Execution.ColdInput.inputs_of_linked_decoder,
    ``Agave.Ed25519.Bridge.cold_caller_crossClient_observations]
  for endpoint in endpoints do
    for dependency in (← collectAxioms endpoint) do
      unless allowed.contains dependency do
        throwError "Unexpected axiom {dependency} in {endpoint}"
  logInfo "Cold caller-input closure uses only standard Lean axioms."
