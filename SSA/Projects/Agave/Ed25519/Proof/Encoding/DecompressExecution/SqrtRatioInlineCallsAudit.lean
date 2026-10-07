import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.SqrtRatioInlineCallsPrefix

/-- info: All 49 sqrt arithmetic-prefix endpoints use only standard Lean axioms. -/
#guard_msgs in
open Lean Elab Command in
run_cmd do
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  let endpoints : List Name := [
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline.callSlot_injective,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline.callWrite_live,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline.callWrite_wf,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline.callWrite_read,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline.callWrite_words_ne,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline.callWrite_read320,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline.callWrite_words,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline.callsState_wf,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline.callsState_live,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline.callsState_slot_live,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline.call_destination_live,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline.callsState_words_written,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline.callsState_read320_written,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline.callsState_read_old,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline.callsState_words_old,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline.callsState_normal,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline.callsState_six,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline.calls_square,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline.calls_mul,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline.calls_pow,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline.calls_copy,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline.callWords0,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline.callWords1,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline.callWords2,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline.callWords3,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline.callWords4,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline.callWords5,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline.callWords6,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline.callWords7,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline.callWords8,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline.callWords9,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline.callWords10,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline.callWords11,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline.callWords12,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline.callWords_pow,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline.callWords_candidate,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline.callWords_check,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline.arithmetic_calls_segment,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline.checked_arithmetic_calls,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline.callWrite_counter,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline.callsState_counter,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline.callWrite_private,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline.callsState_private,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline.callsState_ready,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline.prefix117,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline.state117_words,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline.state117_wf,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline.state117_ready,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline.state117_private]
  for endpoint in endpoints do
    for dependency in (← collectAxioms endpoint) do
      unless allowed.contains dependency do
        throwError "Unexpected axiom {dependency} in {endpoint}"
  logInfo "All 49 sqrt arithmetic-prefix endpoints use only standard Lean axioms."
