import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.DecoderSemanticReady

/-- info: All 49 closed decoder composition endpoints use only standard Lean axioms. -/
#guard_msgs in
open Lean Elab Command in
run_cmd do
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  let endpoints : List Name := [
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline.ScratchFrame.wf,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline.ScratchFrame.old_live,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline.ScratchFrame.old_read,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline.ScratchFrame.old_words,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline.ScratchFrame.ready,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline.ScratchFrame.advance,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline.ScratchFrame.storeAt,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline.ScratchFrame.storeLimbs,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline.ScratchFrame.storeBytes,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline.state117_scratch,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline.entry_constants,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline.entry_sqrtM1,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline.frame_constants,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline.frame_slot,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline.state306_scratch,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline.prefix306,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline.cached_frame,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline.state308_scratch,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline.firstByte_semantic,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline.prefix308,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline.pieces_eq_segment,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline.executionPrefix_eq_segment,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline.sqrtM1_payload,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline.sqrtM1_words,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline.CommonRegisters.frame,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline.state569_scratch,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline.secondByte_semantic,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline.state308_words,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline.state569_words,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline.prefix569,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline.state576_scratch,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline.state577_scratch,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline.state576_negative,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline.state577_product,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline.state577_words,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline.state577_candidate_check,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline.prefix577,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline.prefix1047,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline.executionPrefix_of_ready,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline.prefixWitness_of_ready,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline.call_of_ready,
    ``Agave.Ed25519.Encoding.Decompress.Execution.Decode.ReadySemantic.sqrtPrefixProvider,
    ``Agave.Ed25519.Encoding.Decompress.Execution.Decode.ReadySemantic.prefixBoundary_of_ready,
    ``Agave.Ed25519.Encoding.Decompress.Execution.Decode.ReadySemantic.linked_call_valid,
    ``Agave.Ed25519.Encoding.Decompress.Execution.Decode.ReadySemantic.linked_call_classification,
    ``Agave.Ed25519.Encoding.Decompress.Execution.Decode.ReadySemantic.contractUnder,
    ``Agave.Ed25519.Encoding.Decompress.Execution.Decode.ReadySemantic.call_allocation,
    ``Agave.Ed25519.Encoding.Decompress.Execution.Decode.ReadySemantic.call_shape,
    ``Agave.Ed25519.Encoding.Decompress.Execution.Decode.ReadySemantic.call_callerBlocks]
  for endpoint in endpoints do
    for dependency in (← collectAxioms endpoint) do
      unless allowed.contains dependency do
        throwError "Unexpected axiom {dependency} in {endpoint}"
  logInfo "All 49 closed decoder composition endpoints use only standard Lean axioms."
