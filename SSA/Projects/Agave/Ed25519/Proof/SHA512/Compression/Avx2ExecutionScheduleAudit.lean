import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionSchedulePrefix

/-! Guard the exact bb5 schedule-generation slice and the scratch-store
invariant. The remaining scalar rounds, store instruction and loop-control
composition remain separate execution obligations. -/

/-- info: Exact AVX2 SHA-512 schedule prefix uses only standard Lean axioms. -/
#guard_msgs in
open Lean Elab Command in
run_cmd do
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  let endpoints : List Name := [
    ``Agave.Ed25519.SHA512.Execution.Avx2.pair_schedule_prefix,
    ``Agave.Ed25519.SHA512.Execution.Avx2.pairScheduleEnv_words,
    ``Agave.Ed25519.SHA512.Execution.Avx2.pairScheduleEnv_spec,
    ``Agave.Ed25519.SHA512.Execution.Avx2.pairScratchStore_read,
    ``Agave.Ed25519.SHA512.Execution.Avx2.PairScratch.advance,
    ``Agave.Ed25519.SHA512.Execution.Avx2.PairScratch.next_group,
    ``Agave.Ed25519.SHA512.Execution.Avx2.PairScratch.tail]
  for endpoint in endpoints do
    for dependency in (← collectAxioms endpoint) do
      unless allowed.contains dependency do
        throwError "Unexpected axiom {dependency} in {endpoint}"
  logInfo "Exact AVX2 SHA-512 schedule prefix uses only standard Lean axioms."
