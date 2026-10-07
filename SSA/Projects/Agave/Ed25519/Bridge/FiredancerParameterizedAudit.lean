import SSA.Projects.Agave.Ed25519.Bridge.FiredancerParameterizedReady

/-! The abstracted source proof and preparation endpoint introduce no axioms:
even the three legacy SHA program constants are absent from this inventory. -/

/-- info: Parameterized Firedancer source proof and prepared execution have exactly the three standard foundations. -/
#guard_msgs in
open Lean Elab Command in
run_cmd do
  let expected : List Name := [`propext, `Classical.choice, `Quot.sound]
  let targets : List Name := [
    ``Agave.Ed25519.Bridge.firedancerParameterizedProgram_eq,
    ``Agave.Ed25519.Bridge.firedancerParameterizedSource_conforms,
    ``Agave.Ed25519.Bridge.firedancerParameterized_ready_executionRefines,
    ``Agave.Ed25519.Bridge.firedancerParameterized_ready_executionRefines_of_digestBy]
  for target in targets do
    let actual := (← collectAxioms target).toList
    unless actual.length == expected.length && expected.all actual.contains do
      throwError "Unexpected source execution axioms for {target}: {actual}"
  logInfo "Parameterized Firedancer source proof and prepared execution have exactly the three standard foundations."
