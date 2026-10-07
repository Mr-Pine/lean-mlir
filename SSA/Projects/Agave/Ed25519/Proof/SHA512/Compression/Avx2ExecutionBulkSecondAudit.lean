import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionBulkSecond

/-! Standard-three axiom audit of the exact imported bb15 execution. -/

/-- info: Exact AVX2 SHA-512 second-block rounds use only standard Lean axioms. -/
#guard_msgs in
open Lean Elab Command in
run_cmd do
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  let endpoints : List Name := [
    ``Agave.Ed25519.SHA512.Execution.Avx2.bulkSecond_index_add,
    ``Agave.Ed25519.SHA512.Execution.Avx2.bulkSecond_index_gep,
    ``Agave.Ed25519.SHA512.Execution.Avx2.bulkSecond_index_eq640,
    ``Agave.Ed25519.SHA512.Execution.Avx2.bulkSecond_body,
    ``Agave.Ed25519.SHA512.Execution.Avx2.bulkSecond_next_ready,
    ``Agave.Ed25519.SHA512.Execution.Avx2.bulkSecond_final_ready,
    ``Agave.Ed25519.SHA512.Execution.Avx2.bulkSecond_backedge,
    ``Agave.Ed25519.SHA512.Execution.Avx2.bulkSecond_exit,
    ``Agave.Ed25519.SHA512.Execution.Avx2.bulkSecondBodyEnv_frame,
    ``Agave.Ed25519.SHA512.Execution.Avx2.bulkSecondNextEnv_frame,
    ``Agave.Ed25519.SHA512.Execution.Avx2.bulkSecondRoundEnv_frame,
    ``Agave.Ed25519.SHA512.Execution.Avx2.bulkSecond_suffix,
    ``Agave.Ed25519.SHA512.Execution.Avx2.bulkSecond_eighty,
    ``Agave.Ed25519.SHA512.Execution.Avx2.bulkSecond_eighty_runFrom,
    ``Agave.Ed25519.SHA512.Execution.Avx2.bulkSecond_eighty_evalFrom]
  for endpoint in endpoints do
    for dependency in (← collectAxioms endpoint) do
      unless allowed.contains dependency do
        throwError "Unexpected axiom {dependency} in {endpoint}"
  logInfo "Exact AVX2 SHA-512 second-block rounds use only standard Lean axioms."
