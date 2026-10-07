import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionBulkTailSecondEntry

/-! Strict transitive axiom audit for exact bb13 rounds 64..79, bb14
feed-forward, and the initialized second-block header. -/

/-- info: Exact AVX2 first-block tail and bb15 entry use only standard Lean axioms. -/
#guard_msgs in
open Lean Elab Command in
run_cmd do
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  let endpoints : List Name := [
    ``Agave.Ed25519.SHA512.Execution.Avx2.bulkTail_body,
    ``Agave.Ed25519.SHA512.Execution.Avx2.bulkTail_next_ready,
    ``Agave.Ed25519.SHA512.Execution.Avx2.bulkTail_final_ready,
    ``Agave.Ed25519.SHA512.Execution.Avx2.bulkTail_backedge,
    ``Agave.Ed25519.SHA512.Execution.Avx2.bulkTail_exit,
    ``Agave.Ed25519.SHA512.Execution.Avx2.bulkTail_backedge_runFrom,
    ``Agave.Ed25519.SHA512.Execution.Avx2.bulkTail_exit_runFrom,
    ``Agave.Ed25519.SHA512.Execution.Avx2.bulkTailBodyEnv_frame,
    ``Agave.Ed25519.SHA512.Execution.Avx2.bulkTailNextEnv_frame,
    ``Agave.Ed25519.SHA512.Execution.Avx2.bulkTailRoundEnv_frame,
    ``Agave.Ed25519.SHA512.Execution.Avx2.bulkTail_suffix,
    ``Agave.Ed25519.SHA512.Execution.Avx2.bulkTail_sixteen,
    ``Agave.Ed25519.SHA512.Execution.Avx2.bulkTail_sixteen_runFrom,
    ``Agave.Ed25519.SHA512.Execution.Avx2.bulkTail_sixteen_from_prefix,
    ``Agave.Ed25519.SHA512.Execution.Avx2.BulkTailFeedForwardReady.of_frame,
    ``Agave.Ed25519.SHA512.Execution.Avx2.bulkTailFeedForwardNextEnv_frame,
    ``Agave.Ed25519.SHA512.Execution.Avx2.bulkTailFeedForward_final_ready,
    ``Agave.Ed25519.SHA512.Execution.Avx2.bulkTailFeedForward_body,
    ``Agave.Ed25519.SHA512.Execution.Avx2.bulkTailFeedForward_block,
    ``Agave.Ed25519.SHA512.Execution.Avx2.bulkTailFeedForward_runFrom,
    ``Agave.Ed25519.SHA512.Execution.Avx2.bulkTail_feedForward,
    ``Agave.Ed25519.SHA512.Execution.Avx2.BulkTailSecondConstants.of_frame,
    ``Agave.Ed25519.SHA512.Execution.Avx2.bulkTailFeedForward_second_ready,
    ``Agave.Ed25519.SHA512.Execution.Avx2.bulkTail_feedForward_second]
  for endpoint in endpoints do
    for dependency in (← collectAxioms endpoint) do
      unless allowed.contains dependency do
        throwError "Unexpected axiom {dependency} in {endpoint}"
  logInfo "Exact AVX2 first-block tail and bb15 entry use only standard Lean axioms."
