import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionCountOne

/-! Kernel audit of the imported AVX2 entry, initial loads, all eighty rounds,
actual count-one return, and complete public call against the independent
SHA-512 compression specification. -/

/-- info: Exact count-one AVX2 SHA-512 compression uses only standard Lean axioms. -/
#guard_msgs in
open Lean Elab Command in
run_cmd do
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  let endpoints : List Name := [
    ``Agave.Ed25519.SHA512.Execution.Avx2.entry_constants,
    ``Agave.Ed25519.SHA512.Execution.Avx2.entry_body,
    ``Agave.Ed25519.SHA512.Execution.Avx2.entry_block,
    ``Agave.Ed25519.SHA512.Execution.Avx2.entry_ready,
    ``Agave.Ed25519.SHA512.Execution.Avx2.entry_frame,
    ``Agave.Ed25519.SHA512.Execution.Avx2.entryState_wf,
    ``Agave.Ed25519.SHA512.Execution.Avx2.entryState_frame,
    ``Agave.Ed25519.SHA512.Execution.Avx2.entryState_counter,
    ``Agave.Ed25519.SHA512.Execution.Avx2.PairConstants.entryState,
    ``Agave.Ed25519.SHA512.Execution.Avx2.PairConstants.initialScratchStores,
    ``Agave.Ed25519.SHA512.Execution.Avx2.entryState_readBytes,
    ``Agave.Ed25519.SHA512.Execution.Avx2.initial_block_body,
    ``Agave.Ed25519.SHA512.Execution.Avx2.initial_block_run_unpack,
    ``Agave.Ed25519.SHA512.Execution.Avx2.initialPairEnv_ready,
    ``Agave.Ed25519.SHA512.Execution.Avx2.prefix_sixtyfour_private,
    ``Agave.Ed25519.SHA512.Execution.Avx2.compression_from_pairs_private,
    ``Agave.Ed25519.SHA512.Execution.Avx2.return_block,
    ``Agave.Ed25519.SHA512.Execution.Avx2.return_evalFrom,
    ``Agave.Ed25519.SHA512.Execution.Avx2.entry_to_pairs,
    ``Agave.Ed25519.SHA512.Execution.Avx2.count_one_evalFrom,
    ``Agave.Ed25519.SHA512.Execution.Avx2.count_one_call,
    ``Agave.Ed25519.SHA512.Execution.Avx2.count_one_call_spec,
    ``Agave.Ed25519.SHA512.Execution.Avx2.count_one_call_source,
    ``Agave.Ed25519.SHA512.Execution.Avx2.count_one_contract]
  for endpoint in endpoints do
    for dependency in (← collectAxioms endpoint) do
      unless allowed.contains dependency do
        throwError "Unexpected axiom {dependency} in {endpoint}"
  logInfo "Exact count-one AVX2 SHA-512 compression uses only standard Lean axioms."
