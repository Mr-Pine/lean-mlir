import SSA.Projects.Agave.Ed25519.Bridge.CrossClientContextual

/-- info: Contextual cross-client composition uses only standard Lean axioms. -/
#guard_msgs in
open Lean Elab Command in
run_cmd do
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  let endpoints : List Name := [
    ``Agave.Ed25519.Verifier.Execution.Challenge.challenge_call_under,
    ``Agave.Ed25519.Verifier.Execution.Dalek.challenge_call_of_sha_contracts_under,
    ``Agave.Ed25519.Verifier.Execution.Dalek.entry_of_sha_contracts_under,
    ``Agave.Ed25519.Verifier.Execution.Dalek.scalar_tail_of_nondecoder_contracts,
    ``Agave.Ed25519.Verifier.Execution.Dalek.body_of_decoder_contract_under,
    ``Agave.Ed25519.Verifier.Execution.Dalek.entry_decoder_ready,
    ``Agave.Ed25519.Verifier.Execution.ResidualLeaves.NonDecoderContracts.complete,
    ``Agave.Ed25519.Verifier.Execution.Dalek.program_from_entry_of_leaf_contracts_under,
    ``Agave.Ed25519.Verifier.Execution.Dalek.program_call_of_leaf_contracts_under,
    ``Agave.Ed25519.Verifier.Execution.LinkedContextualLeaves.primitive_calls,
    ``Agave.Ed25519.Verifier.Execution.LinkedContextualLeaves.observe,
    ``Agave.Ed25519.Bridge.contextual_crossClient_acceptance,
    ``Agave.Ed25519.Bridge.contextual_crossClient_observations,
    ``Agave.Ed25519.Bridge.contextual_crossClient_of_canonical]
  for endpoint in endpoints do
    for dependency in (← collectAxioms endpoint) do
      unless allowed.contains dependency do
        throwError "Unexpected axiom {dependency} in {endpoint}"
  logInfo "Contextual cross-client composition uses only standard Lean axioms."
