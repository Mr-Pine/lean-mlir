import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.SqrtRatioInlinePrefixSquare

/-! Strict audit of the actual sqrt prefix through instruction 87. Later
helper calls, byte serialization and root selection are outside this claim. -/

/-- info: All 29 sqrt inline-prefix endpoints use only standard Lean axioms. -/
#guard_msgs in
open Lean Elab Command in
run_cmd do
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  let endpoints : List Name := [
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline.entry_segment,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline.entry_state,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline.allocate_counter,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline.allocate_wf,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline.allocate_ready,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline.entry_ready,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline.alloca_live,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline.allocate_live,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline.allocate_read,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline.allocate_erase,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline.entry_public,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline.entry_slot,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline.entry_args,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline.entry_first_count,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline.allocate_slot_live,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline.slot_live,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline.slot_id,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline.slot_private,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline.slot_distinct,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline.slot_caller_disjoint,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline.entry_live,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline.entry_readLimbs,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline.segment_append,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline.first_square_segment,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline.first_mul_segment,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline.v3_prefix,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline.private_store_erase,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline.v3_public,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline.v3_field]
  for endpoint in endpoints do
    for dependency in (← collectAxioms endpoint) do
      unless allowed.contains dependency do
        throwError "Unexpected axiom {dependency} in {endpoint}"
  logInfo "All 29 sqrt inline-prefix endpoints use only standard Lean axioms."
