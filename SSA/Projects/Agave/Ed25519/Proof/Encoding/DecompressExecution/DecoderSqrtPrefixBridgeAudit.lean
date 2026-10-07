import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.DecoderSqrtCallerFrames

/-! This audit checks the actual sqrt return/call cleanup and decoder semantic
adapters. The finite source-prefix witness remains explicit until supplied by
the independently checked slice composition. -/

/-- info: All 19 sqrt-prefix call and decoder bridge endpoints use only standard Lean axioms. -/
#guard_msgs in
open Lean Elab Command in
run_cmd do
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  let endpoints : List Name := [
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.CallFromPrefix.callState_wf,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.CallFromPrefix.callState_frame,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.CallFromPrefix.callState_flag,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.CallFromPrefix.callState_root,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.CallFromPrefix.callState_allocation,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.CallFromPrefix.callState_shape,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.CallFromPrefix.callState_private,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.CallFromPrefix.call_of_prefix,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.CallFromPrefix.call_of_witness,
    ``Agave.Ed25519.Encoding.Decompress.Execution.Decode.SqrtPrefixBridge.prefixBoundary_of_witness,
    ``Agave.Ed25519.Encoding.Decompress.Execution.Decode.SqrtPrefixBridge.sqrtInput_numerator_bytes,
    ``Agave.Ed25519.Encoding.Decompress.Execution.Decode.SqrtPrefixBridge.sqrtInput_denominator_bytes,
    ``Agave.Ed25519.Encoding.Decompress.Execution.Decode.SqrtPrefixBridge.prefixBoundary_of_provider,
    ``Agave.Ed25519.Encoding.Decompress.Execution.Decode.SqrtPrefixBridge.contractUnder_of_provider,
    ``Agave.Ed25519.Encoding.Decompress.Execution.Decode.SqrtPrefixBridge.call_memory_of_prefix,
    ``Agave.Ed25519.Encoding.Decompress.Execution.Decode.SqrtPrefixBridge.call_allocation_of_prefix,
    ``Agave.Ed25519.Encoding.Decompress.Execution.Decode.SqrtPrefixBridge.call_shape_of_prefix,
    ``Agave.Ed25519.Encoding.Decompress.Execution.Decode.SqrtPrefixBridge.call_callerBlocks_of_prefix,
    ``Agave.Ed25519.Encoding.Decompress.Execution.Decode.SqrtPrefixBridge.call_present_of_prefix]
  for endpoint in endpoints do
    for dependency in (← collectAxioms endpoint) do
      unless allowed.contains dependency do
        throwError "Unexpected axiom {dependency} in {endpoint}"
  logInfo "All 19 sqrt-prefix call and decoder bridge endpoints use only standard Lean axioms."
