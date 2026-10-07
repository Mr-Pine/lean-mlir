import SSA.Projects.Agave.Ed25519.Bridge.CrossClientExistingProofCold
import SSA.Projects.Agave.Ed25519.Bridge.CrossClientChallengeValue
import SSA.Projects.Agave.Ed25519.Bridge.CrossClientProvedLeaves
import SSA.Projects.Agave.Ed25519.Bridge.FiredancerScalarSourceCorrect
import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressValidPoint

/-!
Composition after the available decoder, point-compression, scalar-wide and
Firedancer verifier proofs have supplied their witnesses. The decoder here is
the exact word specification with proved soundness and completeness. Its RIR
execution, the remaining Dalek leaves, SHA compression/digest agreement,
and invocation readiness stay explicit. Firedancer reduction arithmetic is supplied
by the universal source-correctness proof.

No challenge-equality or whole-verifier execution premise is assumed. The
original transcript and modulo-L challenge are connected by the proved
Firedancer returned-value theorem. This module remains pending validation
until all imported implementation proof modules and its audit have built.
-/
namespace Agave.Ed25519.Bridge
open Verifier Verifier.Execution Firedancer.Common
open LeanMLIR.RIR (Vals EffectM)
attribute [local instance] Classical.propDecidable

section
variable (remaining : Dalek.Primitives) (dg : Dalek.Globals)
variable (hardware : Dalek.Avx2Cache.Instructions.HardwareInstructions)
variable (hhardware : Dalek.Avx2Cache.Instructions.InstructionContracts hardware)
variable (compressCall : Vals [.ptr, .ptr, .bv 64] → EffectM (Vals []))
variable (compression : Agave.Ed25519.SHA512.Compression)
variable (cg : Execution.Challenge.Globals) (sg : ScalarWide.Globals)
variable (scg : SHA512Finalization.CompressionGlobals)
variable (ddg : Encoding.Decompress.Execution.Decode.Globals)
variable (dsg : Encoding.Decompress.Execution.SqrtRatio.Globals)
variable (hleaves : ProvedLeaves.RemainingContracts remaining)
variable (hdecodeRun : Dalek.DecompressContractUnder (Encoding.Decompress.Execution.Ready ddg dsg)
  (Encoding.Decompress.Execution.linkedProgram ddg dsg).call
  (ValidPoint.layout SmallOrder.ValidPoint.timesEight) (ValidPoint.shared Encoding.Decompress.Valid.decode))
variable (hcompress : SHA512Finalization.CompressContractUnder scg compressCall compression)
variable (i : Invocation) (initial : LeanMLIR.RIR.GlobalState)
variable (fd : FiredancerProofInvocation)
variable (hinput : LinkedColdLeaves.Inputs (LinkedColdLeaves.keyPrimitives ddg dsg)
  dg cg sg scg ddg dsg Encoding.Decompress.Valid.decode SmallOrder.ValidPoint.timesEight i initial
  fd.a fd.r fd.s fd.messageBytes)
variable (hhash : Challenge.DigestBy ⟨fd.init, fd.append, fd.finish⟩
  (fd.state.mem.live? fd.sha.id) fd.sha.offset (Agave.Ed25519.SHA512.model compression).digest)

include hhardware hleaves hdecodeRun hcompress hinput hhash

/-- The mathematical decoder, point compressor, full scalar-wide call,
Firedancer conformance and returned challenge are actual proof witnesses. -/
theorem provedLeaves_cold_crossClient_observations :
    Execution.observe
      (linkedWrapper (LinkedColdLeaves.keyPrimitives ddg dsg)
        (LinkedColdLeaves.primitives (ProvedLeaves.primitives remaining dg hardware)
          compressCall sg cg ddg dsg) dg Signature.program.call)
      i initial =
      (firedancerObserve FiredancerProofInvocation.programs fd.message fd.size fd.signature
        fd.publicKey fd.sha fd.state).map
        (fun ret => decide (ret = FD_ED25519_SUCCESS) && decide (CanonicalY fd.r)) := by
  apply existingProof_cold_crossClient_observations (ProvedLeaves.primitives remaining dg hardware) dg
    compressCall compression cg sg scg ddg dsg Encoding.Decompress.Valid.decode SmallOrder.ValidPoint.timesEight
    Encoding.Decompress.Valid.decoderCorrect
    (ProvedLeaves.RemainingContracts.complete remaining dg hardware
      Encoding.Decompress.Valid.decode hleaves hhardware)
    hdecodeRun hcompress i initial fd hinput
  rw [agave_scalarChallenge_eq_messageChallenge]
  exact (fd.challenge_eq_of_proved_reducer (Agave.Ed25519.SHA512.model compression).digest
    hhash).symm

/-- Canonical R removes exactly the additional Agave encoding-policy check. -/
theorem provedLeaves_cold_crossClient_of_canonical (hcanonical : CanonicalY fd.r) :
    Execution.observe
      (linkedWrapper (LinkedColdLeaves.keyPrimitives ddg dsg)
        (LinkedColdLeaves.primitives (ProvedLeaves.primitives remaining dg hardware)
          compressCall sg cg ddg dsg) dg Signature.program.call)
      i initial =
      (firedancerObserve FiredancerProofInvocation.programs fd.message fd.size fd.signature
        fd.publicKey fd.sha fd.state).map
        (fun ret => decide (ret = FD_ED25519_SUCCESS)) := by
  simpa only [hcanonical, decide_true, Bool.and_true] using
    provedLeaves_cold_crossClient_observations remaining dg hardware hhardware compressCall compression
      cg sg scg ddg dsg hleaves hdecodeRun hcompress i initial fd hinput hhash

end
end Agave.Ed25519.Bridge
