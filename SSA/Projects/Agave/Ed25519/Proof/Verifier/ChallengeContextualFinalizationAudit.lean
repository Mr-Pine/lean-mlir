import SSA.Projects.Agave.Ed25519.Proof.Verifier.ChallengeContextualFinalization

/-- info: Contextual challenge finalization uses only standard Lean axioms. -/
#guard_msgs in
open Lean Elab Command in
run_cmd do
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  let endpoint := ``Agave.Ed25519.Verifier.Execution.Challenge.challenge_call_under
  for dependency in (← collectAxioms endpoint) do
    unless allowed.contains dependency do
      throwError "Unexpected axiom {dependency} in {endpoint}"
  logInfo "Contextual challenge finalization uses only standard Lean axioms."
