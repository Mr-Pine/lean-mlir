import SSA.Projects.Agave.Ed25519.Bridge.CrossClientCheckedLeaves

/-! Audit the actual proof witnesses filling the discharged Agave leaf slots. -/

/-- info: Checked scalar, equality and cache leaves retain exactly the three standard foundations. -/
#guard_msgs in
open Lean Elab Command in
run_cmd do
  let expected : List Name := [`propext, `Classical.choice, `Quot.sound]
  let target := ``Agave.Ed25519.Bridge.CheckedLeaves.RemainingContracts.complete
  let actual := (← collectAxioms target).toList
  unless actual.length == expected.length && expected.all actual.contains do
    throwError "Unexpected proof witness axioms for {target}: {actual}"
  logInfo "Checked scalar, equality and cache leaves retain exactly the three standard foundations."
