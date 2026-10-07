import SSA.Projects.Agave.Ed25519.Proof.Verifier.DalekChallengeLinked

/-! Axiom audit of the linked challenge call and Dalek entry execution.
The two local SHA contracts, scalar representation equality, and per-call
initialized IV remain explicit hypotheses of the audited endpoints. -/

/-- info: Both linked challenge endpoints use only standard Lean axioms. -/
#guard_msgs in
open Lean Elab Command in
run_cmd do
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  let endpoints : List Name := [
    ``Agave.Ed25519.Verifier.Execution.Dalek.challenge_call_of_sha_contracts,
    ``Agave.Ed25519.Verifier.Execution.Dalek.entry_of_sha_contracts]
  for endpoint in endpoints do
    for dependency in (← collectAxioms endpoint) do
      unless allowed.contains dependency do
        throwError "Unexpected axiom {dependency} in {endpoint}"
  logInfo "Both linked challenge endpoints use only standard Lean axioms."
