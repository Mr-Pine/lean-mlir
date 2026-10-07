import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.SqrtRatioHelperFrames

/-! Checked helper intervals of the actual imported square-root body, plus exact
readback and memory-frame endpoints. This audit covers foundations, not the
remaining independently composed arithmetic slices. -/

/-- info: All 46 sqrt-ratio helper endpoints use only standard Lean axioms. -/
#guard_msgs in
open Lean Elab Command in
run_cmd do
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  let endpoints : List Name := [
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Helpers.advance_wf,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Helpers.segment_append,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Helpers.toBytes_306,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Helpers.bytesEq_307,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Helpers.bytesEq_569,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Helpers.bytesEq_947,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Helpers.mul_576,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Helpers.mul_953,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Helpers.blackBox_955,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Helpers.negativeState_live,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Helpers.negativeState_wf,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Helpers.stores_570_576,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Helpers.lifetimes_948_953,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Helpers.or_954,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Helpers.segment_306_308,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Helpers.segment_569_577,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Helpers.segment_947_956,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Helpers.serialize_wf,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Helpers.serialize_live,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Helpers.serialize_read,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Helpers.serialize_read_other,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Helpers.serialize_allocation,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Helpers.serialize_private,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Helpers.serialize_shape,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Helpers.multiply_wf,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Helpers.multiply_live,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Helpers.multiply_readLimbs,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Helpers.multiply_read_other,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Helpers.multiply_allocation,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Helpers.multiply_private,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Helpers.multiply_shape,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Helpers.negativeState_read320,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Helpers.negativeState_readLimbs,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Helpers.negativeState_read_other,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Helpers.negativeState_allocation,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Helpers.negativeState_private,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Helpers.negativeState_shape,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Helpers.comparison_canonical,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Helpers.comparison_equalWords,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Helpers.correction_byte,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Helpers.comparison_zero_or_one,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Helpers.correction_zero_or_one,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Helpers.advance_ready,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Helpers.serialize_ready,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Helpers.multiply_ready,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Helpers.negativeState_ready]
  for endpoint in endpoints do
    for dependency in (← collectAxioms endpoint) do
      unless allowed.contains dependency do
        throwError "Unexpected axiom {dependency} in {endpoint}"
  logInfo "All 46 sqrt-ratio helper endpoints use only standard Lean axioms."
