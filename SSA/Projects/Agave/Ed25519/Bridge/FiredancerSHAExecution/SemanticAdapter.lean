import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.DigestObservation
import SSA.Projects.Agave.Ed25519.Bridge.FiredancerParameterizedReady

/-! Consume a single digest simulation in the existing source-backed verifier
proof. The SLLVM program values and their three local frame/termination
contracts are still explicit. Digest agreement cannot manufacture these CFGs
or prove their memory footprints. No legacy opaque SHA constant is used. -/
namespace Agave.Ed25519.Bridge.FiredancerSHAExecution
open LeanMLIR SLLVM Firedancer Firedancer.Common

/-- Invocation-local common-spec adapter. No uniform hash correctness, equality
of SHA contexts, interpreter simulation on unrelated memory, or verifier
execution conclusion is assumed. The required SHA call contracts are the
original, independently necessary SLLVM contracts. -/
theorem ready_executionRefines_of_digest_simulation
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
      (bytesOf (readWord (input.args globalReady.reference.wf).msgFits)))
    (words : Fin 4 → BitVec 64)
    (hwords : firedancerSourceReduce
      (SHA512.digest SHA512.Spec.compression (hashTranscript
        (readBuf (input.args globalReady.reference.wf).sigBuf)
        (readBuf (input.args globalReady.reference.wf).pkBuf)
        (bytesOf (readWord (input.args globalReady.reference.wf).msgFits)))) = some words)
    (hvalue : (packWords words).toNat = hashToScalar
      (SHA512.digest SHA512.Spec.compression (hashTranscript
        (readBuf (input.args globalReady.reference.wf).sigBuf)
        (readBuf (input.args globalReady.reference.wf).pkBuf)
        (bytesOf (readWord (input.args globalReady.reference.wf).msgFits))))) :
    FiredancerExecutionRefines programs msg sz sig pk (firedancerFreshSha state)
      (firedancerWithSha state)
      (readBuf (input.args globalReady.reference.wf).pkBuf)
      (readBuf (input.args globalReady.reference.wf).sigBuf)
      (readBuf (input.args globalReady.reference.wf).sBuf)
      (messageChallenge (SHA512.digest SHA512.Spec.compression)
        (readBuf (input.args globalReady.reference.wf).sigBuf)
        (readBuf (input.args globalReady.reference.wf).pkBuf)
        (bytesOf (readWord (input.args globalReady.reference.wf).msgFits))) := by
  have hdigest := (v.simulates_iff_digest calls _ _ _ _ _ hcorrect).mp hsim
  have hexecution := firedancerParameterized_ready_executionRefines programs state msg sz sig pk
    kbits input globalReady calls finishBlock hinit happend hfinish _ words
    (by rw [firedancerFreshSha_live]; exact hdigest) hwords
  simpa only [firedancerReducedScalar_eq_hashToScalar _ words hvalue,
    messageChallenge] using hexecution

end Agave.Ed25519.Bridge.FiredancerSHAExecution
