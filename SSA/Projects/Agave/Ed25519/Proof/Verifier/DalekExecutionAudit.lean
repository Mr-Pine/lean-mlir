import SSA.Projects.Agave.Ed25519.Proof.Verifier.DalekExecutionFull

/-! Axiom audit of the actual extracted Dalek control-flow refinement. The
named primitive contracts remain explicit theorem premises; this audit does
not discharge those cryptographic or hardware-facing implementation proofs. -/

/-- info: All seven Dalek control-flow endpoints use only standard Lean axioms. -/
#guard_msgs in
open Lean Elab Command in
run_cmd do
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  let endpoints : List Name := [
    ``Agave.Ed25519.Verifier.Execution.Dalek.entry_of_contracts,
    ``Agave.Ed25519.Verifier.Execution.Dalek.point_check_of_contracts,
    ``Agave.Ed25519.Verifier.Execution.Dalek.scalar_tail_of_contracts,
    ``Agave.Ed25519.Verifier.Execution.Dalek.body_of_contracts,
    ``Agave.Ed25519.Verifier.Execution.Dalek.program_from_entry_of_contracts,
    ``Agave.Ed25519.Verifier.Execution.Dalek.program_run_of_contracts,
    ``Agave.Ed25519.Verifier.Execution.Dalek.program_call_of_contracts]
  for endpoint in endpoints do
    for dependency in (← collectAxioms endpoint) do
      unless allowed.contains dependency do
        throwError "Unexpected axiom {dependency} in {endpoint}"
  logInfo "All seven Dalek control-flow endpoints use only standard Lean axioms."
