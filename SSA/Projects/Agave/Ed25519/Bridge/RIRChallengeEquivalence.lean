import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.TranscriptCorrect
import SSA.Projects.Agave.Ed25519.Bridge.FiredancerScalarSourceCorrect
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.FinalizationDispatchComplete

/-! Compare the actual Agave challenge call with the actual Firedancer SHA
transcript calls in RIR. Both executions and their output relation follow from
ordinary input/global memory facts and the hardware instruction interface.
This does not identify RIR execution with the older SLLVM SHA bindings. -/
namespace Agave.Ed25519.Bridge.RIRChallengeEquivalence
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.Verifier.Execution
open Agave.Ed25519.Verifier.Execution.Challenge
open Agave.Ed25519.Verifier.Execution.SHA512Finalization
open Agave.Ed25519.Verifier.Execution.Dalek.Avx2Cache.Instructions
open Agave.Ed25519.SHA512.Execution.Dispatch
open FiredancerSHAExecution

/-- The independently checked Firedancer source scalar reducer produces the
same complete 32-byte scalar encoding as the Agave challenge. -/
theorem source_reduce_bytes (digest : BitVec 512) :
    ∃ words, firedancerSourceReduce digest = some words ∧
      Firedancer.Common.packWords words = digestScalarBytes digest := by
  obtain ⟨words, hcall, hvalue⟩ := firedancerSourceReduce_correct digest
  refine ⟨words, hcall, BitVec.eq_of_toNat_eq ?_⟩
  rw [hvalue, digestScalarBytes_toNat]
  rfl

/-- Defined executions with equal reduced challenge bytes for the same
original R, A and message bytes. No SHA execution, digest equality, scalar
arithmetic, or cross-interpreter simulation is an input premise. -/
theorem calls
    (hardware : HardwareInstructions) (laws : InstructionContracts hardware)
    (g : CompressionGlobals) (sg : ScalarWide.Globals) (cg : Challenge.Globals)
    (s : GlobalState) (dst aptr rptr msg : Pointer) (n : BitVec 64)
    (r a : BitVec 256) (message : List (BitVec 8))
    (hwf : s.WF) (hready : ColdChallengeReady g sg s dst aptr rptr msg)
    (hout : SmallRange s.mem dst 32) (ha : SmallRange s.mem aptr 192)
    (hsig : SmallRange s.mem rptr 64) (hinput : SmallRange s.mem msg n.toNat)
    (har : s.mem.readAt aptr 256 = a) (hrr : s.mem.readAt rptr 256 = r)
    (hm : readBytes s.mem msg n.toNat = message)
    (hiv : SmallRange s.mem cg.address0 64)
    (hivr : s.mem.readAt cg.address0 512 = initialWords)
    (hda : (Range.of dst 256).Disjoint (Range.of aptr 1536))
    (hdr : (Range.of dst 256).Disjoint (Range.of rptr 512))
    (hdm : (Range.of dst 256).Disjoint (Range.of msg (8 * n.toNat)))
    (v : TranscriptInvocation) (id : BlockId) (hfd : TranscriptInvocation.Ready v id)
    (hfdr : readBytes v.initial.mem v.signature 32 = Agave.Ed25519.Bridge.Challenge.bytesOf (n := 32) r)
    (hfda : readBytes v.initial.mem v.publicKey 32 = Agave.Ed25519.Bridge.Challenge.bytesOf (n := 32) a)
    (hfdm : readBytes v.initial.mem v.message v.size.toNat = message) :
    ∃ agaveFinal fdFinal,
      (Challenge.program (coldLinkedPrimitives sg (Finalization.linkedCall hardware g)) cg).call
        (challengeArgs dst aptr rptr msg n) s = .value (.nil, agaveFinal) ∧
      TranscriptInvocation.ExecutionResult v fdFinal r a message ∧
      agaveFinal.mem.readAt dst 256 = digestScalarBytes (fdFinal.mem.readAt v.output 512) ∧
      CacheOutputEffect g s agaveFinal dst
        (digestScalarBytes (fdFinal.mem.readAt v.output 512)) ∧
      ChallengeCallerRegions s agaveFinal aptr rptr msg n.toNat ∧
      agaveFinal.WF ∧
      ∃ words, firedancerSourceReduce (fdFinal.mem.readAt v.output 512) = some words ∧
        Firedancer.Common.packWords words = agaveFinal.mem.readAt dst 256 := by
  obtain ⟨agaveFinal, hagave, heffect, hframe, hscalar, hawf⟩ :=
    Finalization.Complete.linked_challenge_call hardware laws g sg cg s dst aptr rptr msg
      n r a message hwf hready hout ha hsig hinput har hrr hm hiv hivr hda hdr hdm
  obtain ⟨fdFinal, hfdResult⟩ := TranscriptInvocation.execution v id r a message hfd hfdr hfda hfdm
  have hbytes : agaveFinal.mem.readAt dst 256 =
      digestScalarBytes (fdFinal.mem.readAt v.output 512) := by
    rw [hfdResult.digest]
    exact hscalar
  refine ⟨agaveFinal, fdFinal, hagave, hfdResult, hbytes, ?_, hframe, hawf, ?_⟩
  · rw [hfdResult.digest]
    exact heffect
  · obtain ⟨words, hcall, hwords⟩ := source_reduce_bytes (fdFinal.mem.readAt v.output 512)
    exact ⟨words, hcall, hwords.trans hbytes.symm⟩

end Agave.Ed25519.Bridge.RIRChallengeEquivalence
