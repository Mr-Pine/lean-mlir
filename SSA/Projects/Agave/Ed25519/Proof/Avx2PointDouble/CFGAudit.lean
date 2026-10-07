import SSA.Projects.Agave.Ed25519.Proof.Avx2PointDouble.CFGExecution

/-! The execution endpoints retain explicit `SquareContract` and `MulContract`
premises. This audit checks the complete conditional caller proof. -/

/-- info: AVX2 point-double execution endpoints use only standard Lean axioms. -/
#guard_msgs in
open Lean Elab Command in
run_cmd do
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  let endpoints : List Name := [
    ``Agave.Ed25519.Avx2PointDouble.prepareOperation_value,
    ``Agave.Ed25519.Avx2PointDouble.mixOperation_value,
    ``Agave.Ed25519.Avx2PointDouble.Execution.square_packed_state,
    ``Agave.Ed25519.Avx2PointDouble.Execution.multiply_packed_state,
    ``Agave.Ed25519.Avx2PointDouble.CFG.body_continue,
    ``Agave.Ed25519.Avx2PointDouble.CFG.dispatch_body,
    ``Agave.Ed25519.Avx2PointDouble.CFG.dispatch_exit,
    ``Agave.Ed25519.Avx2PointDouble.CFG.block_correct,
    ``Agave.Ed25519.Avx2PointDouble.CFG.block_run,
    ``Agave.Ed25519.Avx2PointDouble.CFG.resultEnv_frame,
    ``Agave.Ed25519.Avx2PointDouble.CFG.resultEnv_reads,
    ``Agave.Ed25519.Avx2PointDouble.CFG.resultState_wf,
    ``Agave.Ed25519.Avx2PointDouble.CFG.resultState_live,
    ``Agave.Ed25519.Avx2PointDouble.CFG.resultState_read,
    ``Agave.Ed25519.Avx2PointDouble.CFG.resultState_buffer,
    ``Agave.Ed25519.Avx2PointDouble.CFG.exitEnv_frame,
    ``Agave.Ed25519.Avx2PointDouble.CFG.exitEnv_reads,
    ``Agave.Ed25519.Avx2PointDouble.CFG.exitEnv_zero_reads,
    ``Agave.Ed25519.Avx2PointDouble.doublePoint_reduced,
    ``Agave.Ed25519.Avx2PointDouble.doublePoint_value]
  for endpoint in endpoints do
    for dependency in (← collectAxioms endpoint) do
      unless allowed.contains dependency do
        throwError "Unexpected axiom {dependency} in {endpoint}"
  logInfo "AVX2 point-double execution endpoints use only standard Lean axioms."

#print axioms Agave.Ed25519.Avx2PointDouble.mixOperation_value
#print axioms Agave.Ed25519.Avx2PointDouble.Execution.square_packed_state
#print axioms Agave.Ed25519.Avx2PointDouble.Execution.multiply_packed_state
#print axioms Agave.Ed25519.Avx2PointDouble.CFG.body_continue
#print axioms Agave.Ed25519.Avx2PointDouble.CFG.block_correct
#print axioms Agave.Ed25519.Avx2PointDouble.CFG.block_run
#print axioms Agave.Ed25519.Avx2PointDouble.doublePoint_reduced
#print axioms Agave.Ed25519.Avx2PointDouble.doublePoint_value
