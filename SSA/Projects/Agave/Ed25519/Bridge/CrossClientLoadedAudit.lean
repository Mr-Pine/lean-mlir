import SSA.Projects.Agave.Ed25519.Bridge.CrossClientLoaded

/-- info: Loaded cross-client executions use only standard Lean axioms. -/
#guard_msgs in
open Lean Elab Command in
run_cmd do
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  for endpoint in [
      ``Agave.Ed25519.Bridge.CrossClientLoaded.runs,
      ``Agave.Ed25519.Bridge.CrossClientLoaded.runs_of_canonical] do
    for dependency in (← collectAxioms endpoint) do
      unless allowed.contains dependency do
        throwError "Unexpected axiom {dependency} in {endpoint}"
  logInfo "Loaded cross-client executions use only standard Lean axioms."
