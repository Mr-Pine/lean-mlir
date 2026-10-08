import SSA.Projects.Agave.Ed25519.Bridge.CrossClientReachableRawLoaded

/-- info: Actual Agave and reachable Firedancer source comparison uses exactly the three standard foundations. -/
#guard_msgs in
open Lean Elab Command in
run_cmd do
  let expected : List Name := [`propext, `Classical.choice, `Quot.sound]
  let targets : List Name := [
    ``Agave.Ed25519.Bridge.CrossClientReachableSource.observations,
    ``Agave.Ed25519.Bridge.CrossClientReachableSource.observations_of_canonical,
    ``Agave.Ed25519.Bridge.CrossClientReachableSource.runs,
    ``Agave.Ed25519.Bridge.CrossClientReachableLoaded.observations,
    ``Agave.Ed25519.Bridge.CrossClientReachableLoaded.observations_of_canonical,
    ``Agave.Ed25519.Bridge.CrossClientReachableLoaded.runs,
    ``Agave.Ed25519.Bridge.CrossClientReachableRawLoaded.observations,
    ``Agave.Ed25519.Bridge.CrossClientReachableRawLoaded.observations_of_canonical,
    ``Agave.Ed25519.Bridge.CrossClientReachableRawLoaded.runs]
  for target in targets do
    let actual := (← collectAxioms target).toList
    unless actual.length == expected.length && expected.all actual.contains do
      throwError "Unexpected cross-client source axioms for {target}: {actual}"
  logInfo "Actual Agave and reachable Firedancer source comparison uses exactly the three standard foundations."
