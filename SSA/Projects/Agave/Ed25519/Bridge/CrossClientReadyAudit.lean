import SSA.Projects.Agave.Ed25519.Bridge.CrossClientReady

/-! Exact axiom inventory for the readiness-based cross-client composition.
The remaining semantic premises are explicit in the theorem, not axioms. -/

/-- info: Ready cold endpoints retain exactly the three standard foundations. -/
#guard_msgs in
open Lean Elab Command in
run_cmd do
  let expected : List Name := [
    `propext, `Classical.choice, `Quot.sound]
  let targets : List Name := [
    ``Agave.Ed25519.Bridge.ready_cold_crossClient_observations,
    ``Agave.Ed25519.Bridge.ready_cold_crossClient_of_canonical]
  for target in targets do
    let mut actual : List Name := []
    for dependency in (← collectAxioms target) do
      actual := dependency :: actual
      unless expected.contains dependency do
        throwError "Uninventoried dependency of {target}: {dependency}"
    for dependency in expected do
      unless actual.contains dependency do
        throwError "Expected dependency missing from {target}: {dependency}"
    unless actual.length == expected.length do
      throwError "Expected {expected.length} dependencies for {target}, found {actual.length}"
  logInfo "Ready cold endpoints retain exactly the three standard foundations."
