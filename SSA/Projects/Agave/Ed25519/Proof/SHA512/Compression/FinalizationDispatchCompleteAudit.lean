import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.FinalizationDispatchComplete

/-- info: Complete linked SHA-512 dispatch, finalization and challenge use only standard Lean axioms. -/
#guard_msgs in
open Lean Elab Command in
run_cmd do
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  let endpoints : List Name := [
    ``Agave.Ed25519.SHA512.Execution.Dispatch.Finalization.Complete.avx2_bulk_call_equation,
    ``Agave.Ed25519.SHA512.Execution.Dispatch.Finalization.Complete.linked_compress_contract,
    ``Agave.Ed25519.SHA512.Execution.Dispatch.Finalization.Complete.linked_finalizer_contract,
    ``Agave.Ed25519.SHA512.Execution.Dispatch.Finalization.Complete.linked_challenge_call]
  for endpoint in endpoints do
    for dependency in (← collectAxioms endpoint) do
      unless allowed.contains dependency do
        throwError "Unexpected axiom {dependency} in {endpoint}"
  logInfo "Complete linked SHA-512 dispatch, finalization and challenge use only standard Lean axioms."
