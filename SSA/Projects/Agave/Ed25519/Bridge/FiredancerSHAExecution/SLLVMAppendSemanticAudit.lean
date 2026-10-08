import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMAppendAudit
import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMAppendInitSemantic

/-- info: All SLLVM append stream semantics use only standard Lean axioms. -/
#guard_msgs in
open Lean Elab Command in
run_cmd do
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  let endpoints : List Name := [
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.observed_splice_other,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.observed_counter,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.observed_counter_data,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.observed_message_short,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.append_message_short_represents,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.append_message_short_represents_source,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.append_message_short_call_represents,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.observed_message_filled,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.core_readBits_eq,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.observed_core_result,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.observed_compression,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.observed_reset,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.observed_direct_tail,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.short_tail_mask,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.short_tail_aligned,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.observed_message_tail,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.counter32_eq,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.observed_append32,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.observed_append32_buffered,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.append32_represents,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.append32_buffered_represents,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.append32_represents_source,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.append32_call_represents,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.append32_buffered_represents_source,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.append32_buffered_call_represents,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.rir_small_mono,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.rir_small_add,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.observed_other_frames,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.observed_message_result,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.observed_source_fits,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.append_message_result_represents,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.append_message_result_represents_source,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.observed_init,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.init_memory_represents_source ]
  for endpoint in endpoints do
    for dependency in (← collectAxioms endpoint) do
      unless allowed.contains dependency do
        throwError "Unexpected axiom {dependency} in {endpoint}"
  logInfo "All SLLVM append stream semantics use only standard Lean axioms."
