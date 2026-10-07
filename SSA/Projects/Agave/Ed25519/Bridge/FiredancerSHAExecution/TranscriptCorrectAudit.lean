import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.TranscriptCorrect

/-! Strict transitive axiom whitelist for the complete imported transcript. -/
#print axioms Agave.Ed25519.Bridge.FiredancerSHAExecution.TranscriptInvocation.execution
#print axioms Agave.Ed25519.Bridge.FiredancerSHAExecution.TranscriptInvocation.correct_reads

/-- info: Firedancer transcript correctness uses only standard Lean axioms. -/
#guard_msgs in
open Lean Elab Command in
run_cmd do
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  let endpoints : List Name := [
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.TranscriptInvocation.init_writes,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.TranscriptInvocation.writes_readAt,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.TranscriptInvocation.writes_readBytes,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.TranscriptInvocation.bytesOf_injective,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.TranscriptInvocation.readAt_of_readBytes,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.TranscriptInvocation.finishState_output_live,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.TranscriptInvocation.finish_source_live,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.TranscriptInvocation.At,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.TranscriptInvocation.Ready,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.TranscriptInvocation.At.transport,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.TranscriptInvocation.afterInit,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.TranscriptInvocation.afterR,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.TranscriptInvocation.afterA,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.TranscriptInvocation.afterMessage,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.TranscriptInvocation.afterInit_writes,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.TranscriptInvocation.afterR_writes,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.TranscriptInvocation.afterA_writes,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.TranscriptInvocation.afterMessage_writes,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.TranscriptInvocation.Ready.afterInit,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.TranscriptInvocation.Ready.afterR,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.TranscriptInvocation.Ready.afterA,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.TranscriptInvocation.Ready.afterMessage,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.TranscriptInvocation.afterMessage_allocator,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.TranscriptInvocation.context_count_bound,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.TranscriptInvocation.ExecutionResult,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.TranscriptInvocation.ExecutionResult.correct,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.TranscriptInvocation.fresh,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.TranscriptInvocation.fresh_ready,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.TranscriptInvocation.fresh_message,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.TranscriptInvocation.AppendPreserves,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.TranscriptInvocation.append_step_of_semantics,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.TranscriptInvocation.append_optional_of_semantics,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.TranscriptInvocation.execution_of_append_semantics,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.TranscriptInvocation.correct_of_append_semantics,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.TranscriptInvocation.append_preserves,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.TranscriptInvocation.execution,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.TranscriptInvocation.correct,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.TranscriptInvocation.execution_reads,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.TranscriptInvocation.correct_reads,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.TranscriptInvocation.fresh_execution,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.TranscriptInvocation.fresh_correct,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.TranscriptInvocation.message_length_lt]
  for endpoint in endpoints do
    for dependency in (← collectAxioms endpoint) do
      unless allowed.contains dependency do
        throwError "Unexpected axiom {dependency} in {endpoint}"
  logInfo "Firedancer transcript correctness uses only standard Lean axioms."
