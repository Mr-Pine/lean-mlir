import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionBulkInitialSetup
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionBulkPairPrefix

/-- info: Exact bulk AVX2 setup and first-64-round schedule use only standard Lean axioms. -/
#guard_msgs in
open Lean Elab Command in
run_cmd do
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  let endpoints : List Name := [
    ``Agave.Ed25519.SHA512.Execution.Avx2.bulk_initial_setup_body,
    ``Agave.Ed25519.SHA512.Execution.Avx2.bulk_initial_setup_run,
    ``Agave.Ed25519.SHA512.Execution.Avx2.bulk_initial_setup_pointers,
    ``Agave.Ed25519.SHA512.Execution.Avx2.bulk_initial_setup_ready,
    ``Agave.Ed25519.SHA512.Execution.Avx2.bulk_pair_schedule_prefix,
    ``Agave.Ed25519.SHA512.Execution.Avx2.bulkPairScheduleEnv_words,
    ``Agave.Ed25519.SHA512.Execution.Avx2.bulkPairScheduleEnv_spec,
    ``Agave.Ed25519.SHA512.Execution.Avx2.bulk_pair_first_body,
    ``Agave.Ed25519.SHA512.Execution.Avx2.bulk_pair_second_body,
    ``Agave.Ed25519.SHA512.Execution.Avx2.bulk_pair_store_body,
    ``Agave.Ed25519.SHA512.Execution.Avx2.bulk_pair_body,
    ``Agave.Ed25519.SHA512.Execution.Avx2.bulkPairBodyEnv_next_ready,
    ``Agave.Ed25519.SHA512.Execution.Avx2.bulk_pair_terminator_backedge,
    ``Agave.Ed25519.SHA512.Execution.Avx2.bulk_pair_terminator_exit,
    ``Agave.Ed25519.SHA512.Execution.Avx2.bulk_group_backedge,
    ``Agave.Ed25519.SHA512.Execution.Avx2.bulk_group_exit,
    ``Agave.Ed25519.SHA512.Execution.Avx2.bulk_group_setup_run,
    ``Agave.Ed25519.SHA512.Execution.Avx2.bulkCacheStore_read,
    ``Agave.Ed25519.SHA512.Execution.Avx2.BulkCachePrefix.advance,
    ``Agave.Ed25519.SHA512.Execution.Avx2.BulkCachePrefix.complete,
    ``Agave.Ed25519.SHA512.Execution.Avx2.bulkPairSpecMem_scratch,
    ``Agave.Ed25519.SHA512.Execution.Avx2.bulkPairSpecMem_cache,
    ``Agave.Ed25519.SHA512.Execution.Avx2.bulkPairSpecMem_constants,
    ``Agave.Ed25519.SHA512.Execution.Avx2.bulkPairSpecMem_frame,
    ``Agave.Ed25519.SHA512.Execution.Avx2.bulk_pair_body_spec,
    ``Agave.Ed25519.SHA512.Execution.Avx2.bulk_pair_group,
    ``Agave.Ed25519.SHA512.Execution.Avx2.bulk_prefix_sixtyfour]
  for endpoint in endpoints do
    for dependency in (← collectAxioms endpoint) do
      unless allowed.contains dependency do
        throwError "Unexpected axiom {dependency} in {endpoint}"
  logInfo "Exact bulk AVX2 setup and first-64-round schedule use only standard Lean axioms."
