import SSA.Projects.Agave.Ed25519.Proof.SmallOrder.CofactorValidPoint

/-- info: Concrete cofactor word interpretation uses only standard Lean axioms. -/
#guard_msgs in
open Lean Elab Command in
run_cmd do
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  for endpoint in [``Agave.Ed25519.SmallOrder.eightTimesWord_unsigned,
      ``Agave.Ed25519.SmallOrder.eightTimesWord_represents,
      ``Agave.Ed25519.SmallOrder.ValidPoint.timesEight,
      ``Agave.Ed25519.SmallOrder.ValidPoint.timesEight_curve] do
    for dependency in (← collectAxioms endpoint) do
      unless allowed.contains dependency do
        throwError "Unexpected axiom {dependency} in {endpoint}"
  logInfo "Concrete cofactor word interpretation uses only standard Lean axioms."
