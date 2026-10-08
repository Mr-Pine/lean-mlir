import SSA.Projects.Agave.Ed25519.Bridge.RIRChallengeEquivalence

/-- info: Actual RIR challenge agreement uses only standard Lean axioms. -/
#guard_msgs in
open Lean Elab Command in
run_cmd do
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  let endpoints : List Name := [
    ``Agave.Ed25519.Bridge.RIRChallengeEquivalence.source_reduce_bytes,
    ``Agave.Ed25519.Bridge.RIRChallengeEquivalence.calls]
  for endpoint in endpoints do
    for dependency in (← collectAxioms endpoint) do
      unless allowed.contains dependency do
        throwError "Unexpected axiom {dependency} in {endpoint}"
  logInfo "Actual RIR challenge agreement uses only standard Lean axioms."
