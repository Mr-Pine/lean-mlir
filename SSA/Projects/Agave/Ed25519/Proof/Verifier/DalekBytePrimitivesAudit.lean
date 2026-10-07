import SSA.Projects.Agave.Ed25519.Proof.Verifier.DalekBytePrimitives

/-- info: Both Dalek byte primitive contracts use only standard Lean axioms. -/
#guard_msgs in
open Lean Elab Command in
run_cmd do
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  let endpoints : List Name := [
    ``Agave.Ed25519.Verifier.Execution.Dalek.BytePrimitives.blackBox_contract,
    ``Agave.Ed25519.Verifier.Execution.Dalek.BytePrimitives.bytesEq_contract]
  for endpoint in endpoints do
    for dependency in (← collectAxioms endpoint) do
      unless allowed.contains dependency do
        throwError "Unexpected axiom {dependency} in {endpoint}"
  logInfo "Both Dalek byte primitive contracts use only standard Lean axioms."
