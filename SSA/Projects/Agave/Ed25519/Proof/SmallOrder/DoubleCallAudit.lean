import SSA.Projects.Agave.Ed25519.Proof.SmallOrder.DoubleCall

/-- info: Linked small-order projective double uses only standard Lean axioms. -/
#guard_msgs in
open Lean Elab Command in
run_cmd do
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  for endpoint in [``Agave.Ed25519.SmallOrder.Execution.projective_double_call,
      ``Agave.Ed25519.SmallOrder.Execution.projective_double_readback] do
    for dependency in (← collectAxioms endpoint) do
      unless allowed.contains dependency do
        throwError "Unexpected axiom {dependency} in {endpoint}"
  logInfo "Linked small-order projective double uses only standard Lean axioms."
