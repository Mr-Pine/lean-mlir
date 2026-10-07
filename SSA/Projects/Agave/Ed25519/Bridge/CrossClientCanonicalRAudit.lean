import SSA.Projects.Agave.Ed25519.Bridge.CrossClientCanonicalR

/-! Strict axiom inventories, including the reused mathematical witness and
committed execution bridge. No legacy SHA bindings, native certificates, or
`sorryAx` are allowed. Machine and local challenge premises stay parameterized. -/

/-- info: Canonical-R characterization endpoints use only standard foundations. -/
#guard_msgs in
open Lean Elab Command in
run_cmd do
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  let targets : List Name := [
    ``Agave.Ed25519.Bridge.agave_iff_firedancer_and_canonical,
    ``Agave.Ed25519.Bridge.agave_iff_firedancer_of_canonical,
    ``Agave.Ed25519.Bridge.acceptance_agreement_iff,
    ``Agave.Ed25519.Bridge.noncanonical_encoded_y_lt_nineteen,
    ``Agave.Ed25519.Bridge.noncanonical_non_small_order_encoding_exists,
    ``Agave.Ed25519.Bridge.witness_firedancer_accepts,
    ``Agave.Ed25519.Bridge.witness_agave_rejects,
    ``Agave.Ed25519.Bridge.shared_challenge_policies_differ,
    ``Agave.Ed25519.Bridge.crossClient_observe_acceptance,
    ``Agave.Ed25519.Bridge.crossClient_observations_equal_of_canonical,
    ``Agave.Ed25519.Bridge.crossClient_reject_success_iff_noncanonical,
    ``Agave.Ed25519.Bridge.crossClient_observations_agree_iff,
    ``Agave.Ed25519.Bridge.crossClient_no_agave_only_success]
  for target in targets do
    for dependency in (← collectAxioms target) do
      unless allowed.contains dependency do
        throwError "Unexpected dependency {dependency} of {target}"
  logInfo "Canonical-R characterization endpoints use only standard foundations."

/-- info: Execution characterization endpoints retain exactly the standard three. -/
#guard_msgs in
open Lean Elab Command in
run_cmd do
  let expected : List Name := [`propext, `Classical.choice, `Quot.sound]
  let targets : List Name := [
    ``Agave.Ed25519.Bridge.crossClient_observe_acceptance,
    ``Agave.Ed25519.Bridge.crossClient_observations_equal_of_canonical,
    ``Agave.Ed25519.Bridge.crossClient_reject_success_iff_noncanonical,
    ``Agave.Ed25519.Bridge.crossClient_observations_agree_iff,
    ``Agave.Ed25519.Bridge.crossClient_no_agave_only_success]
  for target in targets do
    let mut actual : List Name := []
    for dependency in (← collectAxioms target) do
      actual := dependency :: actual
      unless expected.contains dependency do
        throwError "Unexpected dependency {dependency} of {target}"
    for dependency in expected do
      unless actual.contains dependency do
        throwError "Missing expected dependency {dependency} of {target}"
    unless actual.length == expected.length do
      throwError "Wrong axiom count for {target}: {actual.length}"
  logInfo "Execution characterization endpoints retain exactly the standard three."
