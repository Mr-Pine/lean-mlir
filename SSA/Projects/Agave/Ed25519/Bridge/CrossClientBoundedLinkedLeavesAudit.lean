import SSA.Projects.Agave.Ed25519.Bridge.CrossClientBoundedLinkedLeaves

/-! Guarded audit of the corrected represented-point, bounded-scalar
cross-client endpoints. Named semantic leaf contracts remain explicit. -/

/-- info: Bounded linked cross-client endpoints use only standard Lean axioms. -/
#guard_msgs in
open Lean Elab Command in
run_cmd do
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  let endpoints : List Name := [
    ``Agave.Ed25519.Bridge.linkedLeaves_bounded_crossClient_acceptance,
    ``Agave.Ed25519.Bridge.linkedLeaves_bounded_crossClient_observations,
    ``Agave.Ed25519.Bridge.linkedLeaves_bounded_crossClient_exact_signature]
  for endpoint in endpoints do
    for dependency in (← collectAxioms endpoint) do
      unless allowed.contains dependency do
        throwError "Unexpected axiom {dependency} in {endpoint}"
  logInfo "Bounded linked cross-client endpoints use only standard Lean axioms."
