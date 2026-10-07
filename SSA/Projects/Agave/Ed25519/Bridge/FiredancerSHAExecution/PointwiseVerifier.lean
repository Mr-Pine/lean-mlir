import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.SemanticAdapter
import SSA.Projects.Agave.Ed25519.Bridge.FiredancerScalarSourceCorrect

/-! Close the invocation-local SHA adapter's scalar return/value premises
with the independently checked Firedancer source reducer. -/
namespace Agave.Ed25519.Bridge.FiredancerSHAExecution
open LeanMLIR SLLVM Firedancer Firedancer.Common

/-- A single actual transcript observation and digest simulation supply the
challenge used by the prepared Firedancer verifier source proof. The source
reducer's termination and value are derived, not assumed. -/
theorem ready_executionRefines_of_transcript
    (programs : FiredancerShaPrograms)
    (state : GlobalState) (msg : Pointer) (sz : BitVec 64) (sig pk : Pointer)
    (kbits : BitVec (80 * 64))
    (input : FiredancerInputReady state msg sz sig pk)
    (globalReady : FiredancerGlobalsReady state kbits)
    (calls : FiredancerHashCalls)
    (finishBlock : Option LiveBlock → BitVec 64 → Option LiveBlock → BitVec 64 → Option LiveBlock)
    (hinit : FiredancerShaInitBy programs calls.init)
    (happend : FiredancerShaAppendBy programs kbits calls.append)
    (hfinish : FiredancerShaFinishBy programs kbits calls.finish finishBlock)
    (v : TranscriptInvocation)
    (hcorrect : v.Correct
      (readBuf (input.args globalReady.reference.wf).sigBuf)
      (readBuf (input.args globalReady.reference.wf).pkBuf)
      (bytesOf (readWord (input.args globalReady.reference.wf).msgFits)))
    (hsim : v.Simulates calls (some { length := 256, bytes := 0#_ }) 0
      (readBuf (input.args globalReady.reference.wf).sigBuf)
      (readBuf (input.args globalReady.reference.wf).pkBuf)
      (bytesOf (readWord (input.args globalReady.reference.wf).msgFits))) :
    FiredancerExecutionRefines programs msg sz sig pk (firedancerFreshSha state)
      (firedancerWithSha state)
      (readBuf (input.args globalReady.reference.wf).pkBuf)
      (readBuf (input.args globalReady.reference.wf).sigBuf)
      (readBuf (input.args globalReady.reference.wf).sBuf)
      (messageChallenge (SHA512.digest SHA512.Spec.compression)
        (readBuf (input.args globalReady.reference.wf).sigBuf)
        (readBuf (input.args globalReady.reference.wf).pkBuf)
        (bytesOf (readWord (input.args globalReady.reference.wf).msgFits))) := by
  obtain ⟨words, hwords, hvalue⟩ := firedancerSourceReduce_correct
    (SHA512.digest SHA512.Spec.compression (hashTranscript
      (readBuf (input.args globalReady.reference.wf).sigBuf)
      (readBuf (input.args globalReady.reference.wf).pkBuf)
      (bytesOf (readWord (input.args globalReady.reference.wf).msgFits))))
  exact ready_executionRefines_of_digest_simulation programs state msg sz sig pk kbits input
    globalReady calls finishBlock hinit happend hfinish v hcorrect hsim words hwords hvalue

end Agave.Ed25519.Bridge.FiredancerSHAExecution
