import SSA.Projects.Agave.Ed25519.Proof.SmallOrder.CofactorLinked

/-- info: Linked cofactor execution, memory frame, ABI payload, and group interpretation use only standard Lean axioms. -/
#guard_msgs in
open Lean Elab Command in
run_cmd do
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  for endpoint in [``Agave.Ed25519.SmallOrder.Execution.cofactor_call_three,
      ``Agave.Ed25519.SmallOrder.Execution.cofactor_call_three_normal,
      ``Agave.Ed25519.SmallOrder.Execution.cofactorState_frame,
      ``Agave.Ed25519.SmallOrder.Execution.cofactorState_payload,
      ``Agave.Ed25519.SmallOrder.Execution.cofactorContract,
      ``Agave.Ed25519.SmallOrder.ValidPoint.timesEight,
      ``Agave.Ed25519.SmallOrder.ValidPoint.timesEight_curve] do
    for dependency in (← collectAxioms endpoint) do
      unless allowed.contains dependency do
        throwError "Unexpected axiom {dependency} in {endpoint}"
  logInfo "Linked cofactor execution, memory frame, ABI payload, and group interpretation use only standard Lean axioms."
