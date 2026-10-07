import SSA.Projects.Agave.Ed25519.Bridge.CrossClientPrimitiveCalls

/-! The conditional execution bridge retains its implementation premises, but
none of these endpoints may depend on legacy SHA constants or native oracles. -/

/-- info: All eleven cross-client execution endpoints use only standard Lean axioms. -/
#guard_msgs in
open Lean Elab Command in
run_cmd do
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  let endpoints : List Name := [
    ``Agave.Ed25519.Bridge.firedancerObserve_success_iff,
    ``Agave.Ed25519.Bridge.crossClient_observe_acceptance,
    ``Agave.Ed25519.Bridge.crossClient_observations_equal_with_canonical_check,
    ``Agave.Ed25519.Bridge.crossClient_observations_equal_of_canonical,
    ``Agave.Ed25519.Bridge.crossClient_observe_acceptance_of_canonical,
    ``Agave.Ed25519.Bridge.crossClient_firedancer_only_iff_noncanonical,
    ``Agave.Ed25519.Bridge.crossClient_fullInput_observe_acceptance,
    ``Agave.Ed25519.Bridge.crossClient_linked_fullInput_observe_acceptance,
    ``Agave.Ed25519.Bridge.crossClient_fullInput_observations_of_primitive_calls,
    ``Agave.Ed25519.Bridge.crossClient_fullInput_observations_of_primitive_calls_of_canonical,
    ``Agave.Ed25519.Bridge.crossClient_linked_fullInput_observations_of_primitive_calls]
  for endpoint in endpoints do
    for dependency in (← collectAxioms endpoint) do
      unless allowed.contains dependency do
        throwError "Unexpected axiom {dependency} in {endpoint}"
  logInfo "All eleven cross-client execution endpoints use only standard Lean axioms."
