import SSA.Projects.Agave.Ed25519.Bridge.FiredancerReachablePrefixRepresents
import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMAppendMessageAdapter
import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMFinishClosed

/-! Close the two remaining reachable SHA contracts from the concrete prefix.
The sole message-size condition follows from the caller's live allocation. -/
namespace Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource
open LeanMLIR SLLVM Firedancer Firedancer.Common
set_option maxRecDepth 24000
set_option maxHeartbeats 2000000

theorem verifierMessage_small {m : MemoryState} {p : Pointer} {n : Nat}
    (h : Fits m p (n*8)) (hsmall : FiredancerBlockSmall m p.id) :
    (bytesOf (readWord h)).length < 2^63 := by
  obtain ⟨b, hb, hlen⟩ := h
  have hs := hsmall b (by simp only [MemoryState.live?, hb])
  simp only [bytesOf, List.length_ofFn]
  simp only [Pointer.offsetInBits, LiveBlock.lengthInBits] at hlen
  omega

/-- The message append and finalizer are actual source executions. Their exact
intermediate allocation is an internal witness, not a caller-supplied hash
result, source-execution premise, or cross-client result equality. -/
theorem verifierTailCalls (r a : BitVec 256) (message : List (BitVec 8))
    (hmessage : message.length < 2^63) :
    ∃ afterMessage : Option LiveBlock,
      FiredancerReachableAppend programs constantsBytes (verifierAfterA r a)
        afterMessage 0 message ∧
      FiredancerReachableFinish programs constantsBytes afterMessage 0
        ((SHA512.model SHA512.Spec.compression).digest (hashTranscript r a message)) := by
  obtain ⟨before, hb, hlen⟩ := verifierAfterA_live r a
  have hp := verifierAfterA_represents r a before hb hlen
  obtain ⟨after, hal, ha, hrep⟩ := MessageExecution.reachable_message before
    (bytesOf (n := 32) r) (bytesOf (n := 32) a) message hlen
    (by simp [bytesOf]) (by simp [bytesOf]) hp hmessage
  refine ⟨some after, ?_, ?_⟩
  · simpa only [hb, show (0 : BitVec 64) = 0#64 by decide] using ha
  · have hf := FinishCorrect.reachable_finish_source after 0
      (StreamSpec.complete (bytesOf (n := 32) r ++ bytesOf (n := 32) a ++ message))
      (StreamSpec.pending (bytesOf (n := 32) r ++ bytesOf (n := 32) a ++ message))
      (by rw [hal]; decide) hrep
    simpa only [StreamSpec.partition, SHA512.model, hashTranscript,
      inputBytes_eq_firedancer] using hf

end Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource
