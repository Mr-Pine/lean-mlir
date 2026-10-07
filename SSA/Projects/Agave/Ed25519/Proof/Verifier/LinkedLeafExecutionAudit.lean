import SSA.Projects.Agave.Ed25519.Proof.Verifier.LinkedLeafExecution

/-- info: Linked Agave leaf execution uses only standard Lean axioms. -/
#guard_msgs in
open Lean Elab Command in
run_cmd do
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  let endpoints : List Name := [
    ``Agave.Ed25519.Verifier.Execution.Dalek.body_of_leaf_contracts,
    ``Agave.Ed25519.Verifier.Execution.Dalek.program_from_entry_of_leaf_contracts,
    ``Agave.Ed25519.Verifier.Execution.Dalek.program_call_of_leaf_contracts,
    ``Agave.Ed25519.Verifier.Execution.LinkedLeaves.SignatureMemory.continuation,
    ``Agave.Ed25519.Verifier.Execution.LinkedLeaves.observe_exact_signature,
    ``Agave.Ed25519.Verifier.Execution.LinkedLeaves.refines_exact_signature]
  for endpoint in endpoints do
    for dependency in (← collectAxioms endpoint) do
      unless allowed.contains dependency do
        throwError "Unexpected axiom {dependency} in {endpoint}"
  logInfo "Linked Agave leaf execution uses only standard Lean axioms."
