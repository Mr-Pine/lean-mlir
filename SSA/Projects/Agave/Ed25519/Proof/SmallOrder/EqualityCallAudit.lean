import SSA.Projects.Agave.Ed25519.Proof.SmallOrder.EqualityValidPoint

/-- info: Small-order equality execution endpoints use only standard Lean axioms. -/
#guard_msgs in
open Lean Elab Command in
run_cmd do
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  let endpoints : List Name := [
    ``Agave.Ed25519.SmallOrder.Execution.EqualityCall.call_exact,
    ``Agave.Ed25519.SmallOrder.Execution.EqualityCall.call_contract,
    ``Agave.Ed25519.SmallOrder.Execution.EqualityResult.result_eq_raw,
    ``Agave.Ed25519.SmallOrder.Execution.EqualityResult.call_raw,
    ``Agave.Ed25519.SmallOrder.Execution.EqualityResult.call_raw_exact,
    ``Agave.Ed25519.SmallOrder.Execution.EqualityValidPoint.call_valid,
    ``Agave.Ed25519.SmallOrder.Execution.EqualityValidPoint.smallOrder_contract]
  for endpoint in endpoints do
    for dependency in (← collectAxioms endpoint) do
      unless allowed.contains dependency do
        throwError "Unexpected axiom {dependency} in {endpoint}"
  logInfo "Small-order equality execution endpoints use only standard Lean axioms."
