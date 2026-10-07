import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.Ready
import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.PointOutput

/-! Kernel audit of checked contextual readiness and exact CFG/memory cuts.
These endpoints do not assert whole-decoder execution or sqrt correctness. -/

/-- info: All 22 decompression cut-point endpoints use only standard Lean axioms. -/
#guard_msgs in
open Lean Elab Command in
run_cmd do
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  let endpoints : List Name := [
    ``Agave.Ed25519.Encoding.Decompress.Execution.Ready.of_outputFrame,
    ``Agave.Ed25519.Encoding.Decompress.Execution.Ready.of_readOnlyFrame,
    ``Agave.Ed25519.Encoding.Decompress.Execution.Ready.alloca,
    ``Agave.Ed25519.Encoding.Decompress.Execution.Ready.storeAt,
    ``Agave.Ed25519.Encoding.Decompress.Execution.Ready.of_present,
    ``Agave.Ed25519.Encoding.Decompress.Execution.Cutpoint.zero,
    ``Agave.Ed25519.Encoding.Decompress.Execution.Cutpoint.step,
    ``Agave.Ed25519.Encoding.Decompress.Execution.Cutpoint.after_segment,
    ``Agave.Ed25519.Encoding.Decompress.Execution.Decode.decide_path,
    ``Agave.Ed25519.Encoding.Decompress.Execution.limbBytes_extract,
    ``Agave.Ed25519.Encoding.Decompress.Execution.storeLimbs_read320,
    ``Agave.Ed25519.Encoding.Decompress.Execution.storeVectorLimbs_read320,
    ``Agave.Ed25519.Encoding.Decompress.Execution.storeVectorLimbs_readLimbs,
    ``Agave.Ed25519.Encoding.Decompress.Execution.Decode.successState_frame,
    ``Agave.Ed25519.Encoding.Decompress.Execution.Decode.rejectionState_frame,
    ``Agave.Ed25519.Encoding.Decompress.Execution.Decode.successState_payload,
    ``Agave.Ed25519.Encoding.Decompress.Execution.Decode.keyChunks_of_payload,
    ``Agave.Ed25519.Encoding.Decompress.Execution.Decode.success_copy_run,
    ``Agave.Ed25519.Encoding.Decompress.Execution.Decode.rejection_run,
    ``Agave.Ed25519.Encoding.Decompress.Execution.Decode.finishPoint_segment,
    ``Agave.Ed25519.Encoding.Decompress.Execution.Decode.finishPoint_run,
    ``Agave.Ed25519.Encoding.Decompress.Execution.Decode.finishPointState_coordinates]
  for endpoint in endpoints do
    for dependency in (← collectAxioms endpoint) do
      unless allowed.contains dependency do
        throwError "Unexpected axiom {dependency} in {endpoint}"
  logInfo "All 22 decompression cut-point endpoints use only standard Lean axioms."
