import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionBulkCall

/-! Close the actual SHA dispatcher and its callers using the proved arbitrary
AVX2 block loop. The only instruction contracts concern the external CPUID,
gated XGETBV and atomic cache-store operations. Memory and initialized-global
conditions remain local to each reached call. -/
namespace Agave.Ed25519.SHA512.Execution.Dispatch.Finalization.Complete

open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.Verifier.Execution
open Agave.Ed25519.Verifier.Execution.Challenge
open Agave.Ed25519.Verifier.Execution.SHA512Finalization
open Agave.Ed25519.Verifier.Execution.Dalek.Avx2Cache.Instructions
open Agave.Ed25519.Bridge.Challenge

/-- Arbitrary counts, including zero, discharge the last direct backend
execution boundary of the imported dispatcher. -/
theorem avx2_bulk_call_equation (g : CompressionGlobals) : Avx2BulkCallEquation g :=
  Avx2.bulk_call_equation g

/-- Both real backend bodies and cold cache initialization are linked. There
is no compressor execution or digest-correctness premise. -/
theorem linked_compress_contract (hardware : HardwareInstructions)
    (laws : InstructionContracts hardware) (g : CompressionGlobals) :
    CompressContractUnder g (linkedCall hardware g) Spec.compression :=
  Finalization.linked_compress_contract hardware laws g (avx2_bulk_call_equation g)

/-- Padding, compression and wide reduction execute their actual RIR bodies. -/
theorem linked_finalizer_contract (hardware : HardwareInstructions)
    (laws : InstructionContracts hardware) (g : CompressionGlobals) (r : ScalarWide.Globals) :
    ScalarFromSha512ColdContract g r
      (coldLinkedPrimitives r (linkedCall hardware g)).scalarFromSha512 Spec.compression :=
  Finalization.linked_finalizer_contract hardware laws g r

/-- Exact R || A || message challenge execution for the fully linked SHA
implementation. No whole-challenge execution contract is assumed. -/
theorem linked_challenge_call (hardware : HardwareInstructions)
    (laws : InstructionContracts hardware) (g : CompressionGlobals) (r : ScalarWide.Globals)
    (cg : Challenge.Globals) (s : GlobalState) (dst aptr rptr msg : Pointer)
    (n : BitVec 64) (rbytes abytes : BitVec 256) (message : Bytes) (hwf : s.WF)
    (hr : ColdChallengeReady g r s dst aptr rptr msg)
    (hout : SmallRange s.mem dst 32) (ha : SmallRange s.mem aptr 192)
    (hsig : SmallRange s.mem rptr 64) (hinput : SmallRange s.mem msg n.toNat)
    (har : s.mem.readAt aptr 256 = abytes) (hrr : s.mem.readAt rptr 256 = rbytes)
    (hm : readBytes s.mem msg n.toNat = message)
    (hiv : SmallRange s.mem cg.address0 64)
    (hivr : s.mem.readAt cg.address0 512 = initialWords)
    (hda : (Range.of dst 256).Disjoint (Range.of aptr 1536))
    (hdr : (Range.of dst 256).Disjoint (Range.of rptr 512))
    (hdm : (Range.of dst 256).Disjoint (Range.of msg (8 * n.toNat))) :
    ∃ after,
      (Challenge.program (coldLinkedPrimitives r (linkedCall hardware g)) cg).call
        (challengeArgs dst aptr rptr msg n) s = .value (.nil, after) ∧
      CacheOutputEffect g s after dst
        (digestScalarBytes (Agave.Ed25519.SHA512.digest Spec.compression
          (transcript rbytes abytes message))) ∧
      ChallengeCallerRegions s after aptr rptr msg n.toNat ∧
      after.mem.readAt dst 256 =
        digestScalarBytes (Agave.Ed25519.SHA512.digest Spec.compression
          (transcript rbytes abytes message)) ∧ after.WF :=
  challenge_call_cold g r (coldLinkedPrimitives r (linkedCall hardware g)) cg Spec.compression
    (linked_compress_contract hardware laws g) (linked_finalizer_contract hardware laws g r)
    s dst aptr rptr msg n rbytes abytes message hwf hr hout ha hsig hinput har hrr hm hiv hivr
    hda hdr hdm

end Agave.Ed25519.SHA512.Execution.Dispatch.Finalization.Complete
