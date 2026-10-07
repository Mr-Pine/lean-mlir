import SSA.Projects.Agave.Ed25519.Proof.Verifier.KeyPayloadLayout

/-- info: Key payload layout endpoints use only standard Lean axioms. -/
#guard_msgs in
open Lean Elab Command in
run_cmd do
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  let endpoints : List Name := [
    ``Agave.Ed25519.Verifier.Execution.Key.payload_point_readback,
    ``Agave.Ed25519.Verifier.Execution.Key.returned_point_readback,
    ``Agave.Ed25519.Verifier.Execution.Key.PointWords.negate_represents,
    ``Agave.Ed25519.Verifier.Execution.Key.call_concrete_cached_point,
    ``Agave.Ed25519.Verifier.Execution.Key.call_shared_cached_point,
    ``Agave.Ed25519.Verifier.Execution.Key.call_cached_point]
  for endpoint in endpoints do
    for dependency in (← collectAxioms endpoint) do
      unless allowed.contains dependency do
        throwError "Unexpected axiom {dependency} in {endpoint}"
  logInfo "Key payload layout endpoints use only standard Lean axioms."
