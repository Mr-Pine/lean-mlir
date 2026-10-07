import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.Montgomery
import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.Setup
import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.Output
import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.PipelineContract
import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.StartupMemory
import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.UnpackRegisters

/-! Audit the exact scalar32 pipeline, its public post-state, and the independent
arithmetic certificates. The caller contract remains conditional on constructing
the explicit pipeline invariants and proving the canonical-byte identity. -/

/-- info: Scalar32 execution pipeline and arithmetic certificates use only standard Lean axioms. -/
#guard_msgs in
open Lean Elab Command in
run_cmd do
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  let endpoints : List Name := [
    ``Agave.Ed25519.ScalarReduce32.Execution.block_count,
    ``Agave.Ed25519.ScalarReduce32.Execution.body_length,
    ``Agave.Ed25519.ScalarReduce32.Execution.body_decomposition,
    ``Agave.Ed25519.ScalarReduce32.Execution.runFrom_of_phases,
    ``Agave.Ed25519.ScalarReduce32.Execution.call_of_phases,
    ``Agave.Ed25519.ScalarReduce32.Execution.constants_execute,
    ``Agave.Ed25519.ScalarReduce32.Execution.allocations_execute,
    ``Agave.Ed25519.ScalarReduce32.Execution.allocationSchedule_count,
    ``Agave.Ed25519.ScalarReduce32.Execution.storePrefix_read_bit,
    ``Agave.Ed25519.ScalarReduce32.Execution.storeBytes_read,
    ``Agave.Ed25519.ScalarReduce32.Execution.store_body,
    ``Agave.Ed25519.ScalarReduce32.Execution.store_run,
    ``Agave.Ed25519.ScalarReduce32.Execution.storeBytes_live,
    ``Agave.Ed25519.ScalarReduce32.Execution.storeBytes_frame,
    ``Agave.Ed25519.ScalarReduce32.Execution.store_phase_output,
    ``Agave.Ed25519.ScalarReduce32.Execution.resultState_frame,
    ``Agave.Ed25519.ScalarReduce32.Execution.resultState_read,
    ``Agave.Ed25519.ScalarReduce32.Execution.contract_of_call_equation,
    ``Agave.Ed25519.ScalarReduce32.Execution.allocationSchedule_state,
    ``Agave.Ed25519.ScalarReduce32.Execution.allocationStates_wf,
    ``Agave.Ed25519.ScalarReduce32.Execution.allocationStates_read,
    ``Agave.Ed25519.ScalarReduce32.Execution.startupScratch_live,
    ``Agave.Ed25519.ScalarReduce32.Execution.startupScratch_local,
    ``Agave.Ed25519.ScalarReduce32.Execution.startupScratch_ne_caller,
    ``Agave.Ed25519.ScalarReduce32.Execution.inputWords_extract,
    ``Agave.Ed25519.ScalarReduce32.Execution.inputWords_bound,
    ``Agave.Ed25519.ScalarReduce32.Execution.inputWords_value,
    ``Agave.Ed25519.ScalarReduce32.Execution.unpack_registers,
    ``Agave.Ed25519.ScalarReduce32.Execution.unpack_phase,
    ``Agave.Ed25519.ScalarReduce32.Execution.product_phase,
    ``Agave.Ed25519.ScalarReduce32.Execution.montgomery_phase,
    ``Agave.Ed25519.ScalarReduce32.Execution.subtract_body,
    ``Agave.Ed25519.ScalarReduce32.Execution.subtractWords_value,
    ``Agave.Ed25519.ScalarReduce32.Execution.pack_phase,
    ``Agave.Ed25519.ScalarReduce32.Execution.store_phase,
    ``Agave.Ed25519.ScalarReduce32.Execution.cleanup_phase,
    ``Agave.Ed25519.ScalarReduce32.Execution.pipeline_call,
    ``Agave.Ed25519.ScalarReduce32.Execution.pipeline_memory,
    ``Agave.Ed25519.ScalarReduce32.Execution.pipeline_allocation_count,
    ``Agave.Ed25519.ScalarReduce32.Execution.pipeline_post_state,
    ``Agave.Ed25519.ScalarReduce32.Execution.pipeline_call_public,
    ``Agave.Ed25519.ScalarReduce32.Execution.contract_of_pipeline_witnesses,
    ``Agave.Ed25519.ScalarReduce32.Arithmetic.sourceL_eq_ell,
    ``Agave.Ed25519.ScalarReduce32.Arithmetic.sourceR_eq_mod,
    ``Agave.Ed25519.ScalarReduce32.Arithmetic.lfactor_identity,
    ``Agave.Ed25519.ScalarReduce32.Arithmetic.montgomery_coprime,
    ``Agave.Ed25519.ScalarReduce32.Arithmetic.adjustment_identity,
    ``Agave.Ed25519.ScalarReduce32.Arithmetic.finish_correct,
    ``Agave.Ed25519.ScalarReduce32.Arithmetic.telescope,
    ``Agave.Ed25519.ScalarReduce32.Arithmetic.reduceSchedule_certificate,
    ``Agave.Ed25519.ScalarReduce32.Arithmetic.reduceSchedule_correct]
  for endpoint in endpoints do
    for dependency in (← collectAxioms endpoint) do
      unless allowed.contains dependency do
        throwError "Unexpected axiom {dependency} in {endpoint}"
  logInfo "Scalar32 execution pipeline and arithmetic certificates use only standard Lean axioms."
