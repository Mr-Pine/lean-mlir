import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.DecoderOuterFrame
import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.DecoderOuterRegisters

/-! Checked composition progress, deliberately separate from a mathematical
correctness claim for the decoder. Source prefixes remain explicit computations:
sqrt bb0:0--1046, decoder bb0:0--136, and decoder bb1:0--49. The theorems preserve
poison and require only concrete readiness facts on states actually reached.
They prove the continuation, branch, output-store and actual call-erase steps;
they do not prove these prefixes produce canonical sqrt or point coordinates.

`SqrtPow22501Call` is confined to the exact helper-call cut theorem. The optional
`SqrtRatioExecutionLinked` module discharges it using actual Pow22501 execution.
The outer composition theorems do not assume any whole-decoder execution result.
Remaining work: evaluate inline arithmetic, establish prefix success/readiness,
and prove prefix erasure. Output-pointer argument preservation is proved for
arbitrary source slices, even when helper behavior remains uninterpreted. -/

/-- info: All 24 outer composition components use only standard Lean axioms. -/
#guard_msgs in
open Lean Elab Command in
run_cmd do
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  let endpoints : List Name := [
    ``Agave.Ed25519.Encoding.Decompress.Execution.sqrtratio_pow22501_0_100,
    ``Agave.Ed25519.Encoding.Decompress.Execution.sqrtratio_pow2k_0_105,
    ``Agave.Ed25519.Encoding.Decompress.Execution.OuterComposition.resume_segment,
    ``Agave.Ed25519.Encoding.Decompress.Execution.OuterComposition.resume_pieces,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.executionPieceLengths_sum,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.executionPrefix_resume,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.execution_run,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.execution_call,
    ``Agave.Ed25519.Encoding.Decompress.Execution.Decode.outerSuccess_run,
    ``Agave.Ed25519.Encoding.Decompress.Execution.Decode.outerDecision_run,
    ``Agave.Ed25519.Encoding.Decompress.Execution.Decode.outer_run,
    ``Agave.Ed25519.Encoding.Decompress.Execution.Decode.outer_call,
    ``Agave.Ed25519.Encoding.Decompress.Execution.Decode.finishPointState_erase,
    ``Agave.Ed25519.Encoding.Decompress.Execution.Decode.outerSuccessState_erase,
    ``Agave.Ed25519.Encoding.Decompress.Execution.Decode.outerSuccessState_public,
    ``Agave.Ed25519.Encoding.Decompress.Execution.Decode.outerRejectionState_public,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.executionOutputState_erase,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.executionOutputState_public,
    ``Agave.Ed25519.Encoding.Decompress.Execution.OuterComposition.instruction_args,
    ``Agave.Ed25519.Encoding.Decompress.Execution.OuterComposition.segment_args,
    ``Agave.Ed25519.Encoding.Decompress.Execution.OuterComposition.pieces_args,
    ``Agave.Ed25519.Encoding.Decompress.Execution.Decode.outerEntryPrefix_outputRegister,
    ``Agave.Ed25519.Encoding.Decompress.Execution.Decode.outerSuccessPrefix_outputRegister,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.executionPrefix_outputRegister]
  for endpoint in endpoints do
    for dependency in (← collectAxioms endpoint) do
      unless allowed.contains dependency do
        throwError "Unexpected axiom {dependency} in {endpoint}"
  logInfo "All 24 outer composition components use only standard Lean axioms."
