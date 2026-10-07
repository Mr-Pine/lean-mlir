import SSA.Projects.Agave.Ed25519.Proof.Verifier.ChallengeExecutionLinked
import SSA.Projects.Agave.Ed25519.Proof.Verifier.ChallengeExecutionCFG

/-! Logical-axiom audit for the actual challenge CFG and linked callee.
The two local SHA primitive contracts remain explicit theorem premises. -/

/-- info: All challenge execution endpoints use only standard Lean axioms. -/
#guard_msgs in
open Lean Elab Command in
run_cmd do
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  let endpoints : List Name := [
    ``Agave.Ed25519.Verifier.Execution.Challenge.program_no_fuel_exhaustion,
    ``Agave.Ed25519.Verifier.Execution.Challenge.entry_context,
    ``Agave.Ed25519.Verifier.Execution.Challenge.compress_blocks,
    ``Agave.Ed25519.Verifier.Execution.Challenge.entry_block,
    ``Agave.Ed25519.Verifier.Execution.Challenge.short_block,
    ``Agave.Ed25519.Verifier.Execution.Challenge.first_block,
    ``Agave.Ed25519.Verifier.Execution.Challenge.slice_block,
    ``Agave.Ed25519.Verifier.Execution.Challenge.bulk_block,
    ``Agave.Ed25519.Verifier.Execution.Challenge.tail_block,
    ``Agave.Ed25519.Verifier.Execution.Challenge.remaining_reaches_final,
    ``Agave.Ed25519.Verifier.Execution.Challenge.challenge_reaches_final,
    ``Agave.Ed25519.Verifier.Execution.Challenge.challenge_runFrom,
    ``Agave.Ed25519.Verifier.Execution.Challenge.challenge_call]
  for endpoint in endpoints do
    for dependency in (← collectAxioms endpoint) do
      unless allowed.contains dependency do
        throwError "Unexpected axiom {dependency} in {endpoint}"
  logInfo "All challenge execution endpoints use only standard Lean axioms."
