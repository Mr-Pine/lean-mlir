import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.SqrtRatioInline577Execution

/-! Strict transitive audit of the exact 577..946 execution and its frames.
The audit rejects every foundational dependency outside the standard three. -/

/-- info: All 68 sqrt 577 endpoints use only standard Lean axioms. -/
#guard_msgs in
open Lean Elab Command in
run_cmd do
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  let endpoints : List Name := [
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline577.constants_frame,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline577.registers_frame,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline577.first_serializer,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline577.second_serializer,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline577.segment,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline577.resume,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline577.segment_correct,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SerializerFrame.Frame.refl,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SerializerFrame.Frame.trans,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SerializerFrame.Frame.mono,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SerializerFrame.Frame.write,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SerializerFrame.load_frame,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SerializerFrame.store_frame,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SerializerFrame.instr_frame,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SerializerFrame.list_frame,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline577.first_load_segment,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline577.second_load_segment,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline577.first_load_args,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline577.second_load_args,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline577.first_load_frame,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline577.second_load_frame,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline577.firstIndex_bound,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline577.firstIndex_injective,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline577.firstArg_disjoint,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline577.secondIndex_bound,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline577.secondIndex_injective,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline577.secondArg_disjoint,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline577.serialize_alloc,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline577.serialize_live,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline577.serialize_read,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline577.serialize_words,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline577.serialize_wf,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline577.serialize_canonical,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline577.serialize_private,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline577.result_alloc,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline577.result_wf,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline577.result_live,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline577.result_read,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline577.result_words,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline577.result_private,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline577.result_first_canonical,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline577.result_second_canonical,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline577.result_comparison_inputs,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline577.result_equal_iff,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline577.result_ready,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline577.first_prepared,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline577.first_source_args,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline577.second_prepared,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline577.second_source_args,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline577.take_map_append,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline577.first_tail_chunk0,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline577.first_tail_chunk1,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline577.first_tail_chunk2,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline577.first_tail_chunk3,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline577.first_tail_chunk4,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline577.first_tail_chunk5,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline577.first_tail_chunk6,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline577.first_tail_names,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline577.second_tail_chunk0,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline577.second_tail_chunk1,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline577.second_tail_chunk2,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline577.second_tail_chunk3,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline577.second_tail_chunk4,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline577.second_tail_chunk5,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline577.second_tail_chunk6,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline577.second_tail_names,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline577.first_writes,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline577.second_writes]
  for endpoint in endpoints do
    for dependency in (← collectAxioms endpoint) do
      unless allowed.contains dependency do
        throwError "Unexpected axiom {dependency} in {endpoint}"
  logInfo "All 68 sqrt 577 endpoints use only standard Lean axioms."
