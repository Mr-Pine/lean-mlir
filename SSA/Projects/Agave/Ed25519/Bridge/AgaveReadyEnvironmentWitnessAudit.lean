import SSA.Projects.Agave.Ed25519.Bridge.AgaveReadyEnvironmentWitnessCaller

/-- info: The joint Agave environment witnesses retain exactly the three standard foundations. -/
#guard_msgs in
open Lean Elab Command in
run_cmd do
  let expected : List Name := [`propext, `Classical.choice, `Quot.sound]
  let targets : List Name := [
    ``Agave.Ed25519.Bridge.AgaveReady.EnvironmentWitness.globals_jointly_satisfiable,
    ``Agave.Ed25519.Bridge.AgaveReady.EnvironmentWitness.caller_memory,
    ``Agave.Ed25519.Bridge.AgaveReady.EnvironmentWitness.environment_jointly_satisfiable,
    ``Agave.Ed25519.Bridge.AgaveReady.EnvironmentWitness.call_strict_loaded]
  for target in targets do
    let actual ← collectAxioms target
    unless actual.size == expected.length do
      throwError "Unexpected axiom count for {target}: {actual}"
    for dependency in actual do
      unless expected.contains dependency do
        throwError "Uninventoried dependency of {target}: {dependency}"
    for dependency in expected do
      unless actual.contains dependency do
        throwError "Missing expected dependency of {target}: {dependency}"
  logInfo "The joint Agave environment witnesses retain exactly the three standard foundations."
