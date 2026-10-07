import SSA.Projects.Agave.Ed25519.Proof.SmallOrder.CofactorContextual

/-- info: Contextual linked cofactor execution and its group interpretation use only standard Lean axioms. -/
#guard_msgs in
open Lean Elab Command in
run_cmd do
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  for endpoint in [``Agave.Ed25519.SmallOrder.Execution.linked_cofactorContract,
      ``Agave.Ed25519.SmallOrder.Execution.linked_cofactor_call_valid,
      ``Agave.Ed25519.SmallOrder.ValidPoint.timesEight,
      ``Agave.Ed25519.SmallOrder.ValidPoint.timesEight_curve] do
    for dependency in (← collectAxioms endpoint) do
      unless allowed.contains dependency do
        throwError "Unexpected axiom {dependency} in {endpoint}"
  logInfo "Contextual linked cofactor execution and its group interpretation use only standard Lean axioms."
