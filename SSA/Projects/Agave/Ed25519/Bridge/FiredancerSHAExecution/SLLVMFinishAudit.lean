import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMFinishClosed

/-! Strict transitive audit of the actual-source finalizer, its concrete scalar
core, padding/output observations, and verifier-facing contract. Closed source
endpoints have no compression-execution or digest-correctness premise. -/

#print axioms Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.FinishCorrect.call_digest_source
#print axioms Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.FinishCorrect.reachable_finish_source

/-- info: SLLVM finalizer execution, padding, output, and frame proofs use only standard Lean axioms. -/
#guard_msgs in
open Lean Elab Command in
run_cmd do
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  let endpoints : List Name := [
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.FinishExecution.short_body,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.FinishExecution.long_body,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.FinishExecution.short_call,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.FinishExecution.long_call,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.FinishObservation.Observed.splice,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.FinishObservation.Observed.context,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.FinishObservation.Observed.context_back,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.FinishObservation.first_padding_bytes,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.FinishObservation.only_padding_bytes,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.FinishObservation.last_padding_bytes,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.FinishObservation.output_word,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.FinishDigest.core_result_state,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.FinishCorrect.Ready.core,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.FinishCorrect.Ready.after_core,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.FinishCorrect.short_correct,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.FinishCorrect.long_correct,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.FinishCorrect.call_digest,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.FinishCorrect.ready_of_constants,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.FinishCorrect.Post.output_readWord,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.FinishCorrect.call_digest_constants,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.FinishCorrect.BlockRepresents.of_context,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.FinishCorrect.reachable_finish,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.FinishCorrect.call_digest_source,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.FinishCorrect.call_digest_constants_source,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.FinishCorrect.reachable_finish_source]
  for endpoint in endpoints do
    for dependency in (← collectAxioms endpoint) do
      unless allowed.contains dependency do
        throwError "Unexpected axiom {dependency} in {endpoint}"
  logInfo "SLLVM finalizer execution, padding, output, and frame proofs use only standard Lean axioms."
