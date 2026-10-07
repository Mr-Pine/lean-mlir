import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.CoreInputMemory
import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.CoreLater
import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.Context
import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.AppendCounter
import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.FinishOutput

/-! Strict transitive axiom closure of the source execution and arithmetic leaves.
A checked source leaf is not a full core/stream/digest correctness theorem. -/

#print axioms Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.first_body_full
#print axioms Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.later_body_full
#print axioms Agave.Ed25519.Bridge.FiredancerSHAExecution.Init.call_represents
#print axioms Agave.Ed25519.Bridge.FiredancerSHAExecution.Append.counter_body
#print axioms Agave.Ed25519.Bridge.FiredancerSHAExecution.Finish.last_prefix
#print axioms Agave.Ed25519.Bridge.FiredancerSHAExecution.Finish.output_body

/-- info: Firedancer scalar SHA source leaves use only standard Lean axioms. -/
#guard_msgs in
open Lean Elab Command in
run_cmd do
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  let endpoints : List Name := [
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.source_choose,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.source_majority,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.firstRound,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.laterRound,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.firstRound_eq,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.laterRound_eq,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.scheduleWord,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.scheduleWord_eq,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.scheduleWord_spec,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.appendLow,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.appendHigh,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.append_counter,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.append_remainder,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.append_partition,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.append_aligned_mask,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.append_remainder_bound,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.append_core_count,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.finish_two_blocks,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.finish_padding_counts,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.gep_zero_index,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.constant_index,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.Constants,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.FirstReady,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.firstEnv,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.first_body,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.first_result,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.LaterReady,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.laterEnv,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.later_body,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.later_result,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.Ring,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.RingRepresents,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.ringWord,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.ringStep,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.ringWord_spec,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.ringStep_represents,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.initialRing,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.initialRing_represents,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.laterLoop,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.laterLoop_represents,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.laterLoop_finishes,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.stateWord,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.readState,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.ContextRepresents,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Init.memory_live,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Init.memory_word,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Init.memory_chaining,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Init.memory_count,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Init.memory_represents,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Init.call_represents,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.ring_index_add,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.ring_index_mask,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.ring_index_gep,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.fshl63_rotate,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.fshl56_rotate,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.fshl45_rotate,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.fshl3_rotate,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.ScheduleReady,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.scheduleMemory,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.scheduleEnv,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.schedule_body,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.scheduleMemory_read,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.LaterStateReady,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.schedule_ready_round,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.schedule_constants,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.laterBodyEnv,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.later_body_full,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.later_body_result,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.later_exit_test,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.first_shift,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.first_data_index,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.InputReady,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.inputMemory,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.inputEnv,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.input_body,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.FirstStateReady,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.input_ready_round,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.input_constants,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.firstBodyEnv,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.first_body_full,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.first_exit_test,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.input_swap_eq,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.InitialRingMemory,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.initialRingMemory_zero,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.inputMemory_initial_step,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.initialRingMemory_full,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.inputMemory_preserves_data,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Append.counterMemory,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Append.CounterReady,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Append.counterEnv,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Append.counter_body,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Append.counter_value,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Append.counterMemory_wf,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Append.counterMemory_other_block,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Finish.byte_index,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Finish.markerMemory,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Finish.entryEnv,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Finish.entry_body,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Finish.entry_choice,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Finish.longMemory,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Finish.longEnv,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Finish.long_prefix,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Finish.last_sub,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Finish.lastMemory,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Finish.lastEnv,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Finish.last_prefix,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Finish.OutputReady,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Finish.outputMemory,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Finish.outputEnv,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Finish.output_body]
  for endpoint in endpoints do
    for dependency in (← collectAxioms endpoint) do
      unless allowed.contains dependency do
        throwError "Unexpected axiom {dependency} in {endpoint}"
  logInfo "Firedancer scalar SHA source leaves use only standard Lean axioms."
