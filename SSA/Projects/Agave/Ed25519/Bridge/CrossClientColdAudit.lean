import SSA.Projects.Agave.Ed25519.Bridge.CrossClientCold

/-- info: Cold-cache wrapper composition uses only standard Lean axioms. -/
#guard_msgs in
open Lean Elab Command in
run_cmd do
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  let endpoints : List Name := [
    ``Agave.Ed25519.Verifier.Execution.Dalek.ColdEntryReady.challenge,
    ``Agave.Ed25519.Verifier.Execution.Dalek.cold_entry_body_memory,
    ``Agave.Ed25519.Verifier.Execution.Dalek.cold_entry_decoder_ready,
    ``Agave.Ed25519.Verifier.Execution.Dalek.challenge_call_of_sha_contracts_cold,
    ``Agave.Ed25519.Verifier.Execution.Dalek.challenge_call_of_sha_contracts_cold_warm,
    ``Agave.Ed25519.Verifier.Execution.Dalek.entry_of_sha_contracts_cold,
    ``Agave.Ed25519.Verifier.Execution.Dalek.program_call_of_leaf_contracts_cold,
    ``Agave.Ed25519.Verifier.Execution.LinkedColdLeaves.primitive_calls,
    ``Agave.Ed25519.Verifier.Execution.LinkedColdLeaves.observe,
    ``Agave.Ed25519.Bridge.cold_crossClient_acceptance,
    ``Agave.Ed25519.Bridge.cold_crossClient_observations,
    ``Agave.Ed25519.Bridge.cold_crossClient_of_canonical]
  for endpoint in endpoints do
    for dependency in (← collectAxioms endpoint) do
      unless allowed.contains dependency do
        throwError "Unexpected axiom {dependency} in {endpoint}"
  logInfo "Cold-cache wrapper composition uses only standard Lean axioms."
