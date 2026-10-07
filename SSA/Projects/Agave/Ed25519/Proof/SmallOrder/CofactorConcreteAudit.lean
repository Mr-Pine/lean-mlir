import SSA.Projects.Agave.Ed25519.Proof.SmallOrder.CofactorConcreteExecution
import SSA.Projects.Agave.Ed25519.Proof.SmallOrder.CofactorPayload

/-- info: Fixed-k cofactor execution and exact memory readback use only standard Lean axioms. -/
#guard_msgs in
open Lean Elab Command in
run_cmd do
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  for endpoint in [``Agave.Ed25519.SmallOrder.Execution.cofactor_call_three_of_double,
      ``Agave.Ed25519.SmallOrder.Execution.two_loops_run,
      ``Agave.Ed25519.SmallOrder.Execution.cofactorState_read,
      ``Agave.Ed25519.SmallOrder.Execution.cofactorState_eq_pointPost,
      ``Agave.Ed25519.SmallOrder.Execution.cofactorState_frame,
      ``Agave.Ed25519.SmallOrder.Execution.cofactorState_payload,
      ``Agave.Ed25519.SmallOrder.ValidPoint.timesEight] do
    for dependency in (← collectAxioms endpoint) do
      unless allowed.contains dependency do
        throwError "Unexpected axiom {dependency} in {endpoint}"
  logInfo "Fixed-k cofactor execution and exact memory readback use only standard Lean axioms."
