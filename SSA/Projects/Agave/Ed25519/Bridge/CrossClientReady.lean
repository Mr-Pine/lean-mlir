import SSA.Projects.Agave.Ed25519.Bridge.FiredancerScalarSourceCorrect
import SSA.Projects.Agave.Ed25519.Bridge.CrossClientProvedLeaves
import SSA.Projects.Agave.Ed25519.Bridge.CrossClientParameterizedCaller
import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.FullCall
import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressValidPoint

/-!
Cross-client observation from ordinary loaded inputs and a fresh Firedancer
SHA allocation. Explicit SHA programs replace the legacy bindings. The source
scalar-determinism proof, canonical base-table values, digest return and complete
FD run are constructed. The remaining premises describe both double-base
backends, external bcmp, hardware instructions, contextual decoder execution
and its exact caller-block frame, SHA execution and digest agreement, loaded
memory/constants. FD reducer termination/value correctness is proved for every digest.
No whole-verifier or challenge-equality
premise remains. Pending validation until the imported proof closure builds.
-/
namespace Agave.Ed25519.Bridge
open Verifier Verifier.Execution Firedancer Firedancer.Common
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
variable (programs : FiredancerShaPrograms)
variable (fdState : LeanMLIR.GlobalState) (fdMessage : LeanMLIR.Pointer) (fdSize : BitVec 64)
variable (fdSignature fdPublicKey : LeanMLIR.Pointer) (kbits : BitVec (80 * 64))
variable (input : FiredancerInputReady fdState fdMessage fdSize fdSignature fdPublicKey)
variable (fdGlobals : FiredancerGlobalsReady fdState kbits)
variable (calls : FiredancerHashCalls)
variable (finishBlock : Option LeanMLIR.LiveBlock → BitVec 64 →
  Option LeanMLIR.LiveBlock → BitVec 64 → Option LeanMLIR.LiveBlock)
variable (hinit : FiredancerShaInitBy programs calls.init)
variable (happend : FiredancerShaAppendBy programs kbits calls.append)
variable (hfinish : FiredancerShaFinishBy programs kbits calls.finish finishBlock)
variable (hcaller : ColdInput.CallerMemory i initial
  (readBuf (input.args fdGlobals.reference.wf).pkBuf)
  (readBuf (input.args fdGlobals.reference.wf).sigBuf)
  (readBuf (input.args fdGlobals.reference.wf).sBuf)
  (bytesOf (readWord (input.args fdGlobals.reference.wf).msgFits)))
variable (hagaveGlobals : ColdInput.InitializedGlobals dg cg sg scg ddg dsg initial i.message)
variable (hframe : ∀ decoded,
  (Encoding.Decompress.Execution.linkedProgram ddg dsg).call
    (Key.args (Key.optionSlot (Wrapper.allocated initial)) i.publicKey)
    ((Wrapper.allocated initial).alloca 168) = .value (.nil, decoded) →
  ColdInput.CallerBlocks (Wrapper.allocated initial) decoded)
variable (hhash : Challenge.DigestBy calls
  (some { length := 256, bytes := 0#_ }) 0
  (Agave.Ed25519.SHA512.model compression).digest)


include hhardware hleaves hdecodeRun hcompress hinit happend hfinish hcaller hagaveGlobals hframe hhash

/-- Final observation endpoint with only the explicit implementation and
initialization boundaries. Every removed contract is supplied by its proof. -/
theorem ready_cold_crossClient_observations :
    Execution.observe
      (linkedWrapper (LinkedColdLeaves.keyPrimitives ddg dsg)
        (LinkedColdLeaves.primitives (ProvedLeaves.primitives remaining dg hardware)
          compressCall sg cg ddg dsg) dg Signature.program.call)
      i initial =
      (firedancerObserve programs fdMessage fdSize fdSignature
        fdPublicKey (firedancerFreshSha fdState) (firedancerWithSha fdState)).map
        (fun ret => decide (ret = FD_ED25519_SUCCESS) &&
          decide (CanonicalY (readBuf (input.args fdGlobals.reference.wf).sigBuf))) := by
  exact parameterizedCaller_cold_crossClient_observations (ProvedLeaves.primitives remaining dg hardware) dg
    compressCall compression cg sg scg ddg dsg Encoding.Decompress.Valid.decode SmallOrder.ValidPoint.timesEight
    Encoding.Decompress.Valid.decoderCorrect
    (ProvedLeaves.RemainingContracts.complete remaining dg hardware
      Encoding.Decompress.Valid.decode hleaves hhardware)
    hdecodeRun hcompress (ScalarWide.execution_obligation sg) i initial
    programs fdState fdMessage fdSize fdSignature fdPublicKey kbits input fdGlobals calls finishBlock
    hinit happend hfinish hcaller hagaveGlobals hframe hhash (firedancerSourceReduce_correct _)

/-- On canonical R, compare only Agave's Boolean with FD's success code. -/
theorem ready_cold_crossClient_of_canonical
    (hcanonical : CanonicalY (readBuf (input.args fdGlobals.reference.wf).sigBuf)) :
    Execution.observe
      (linkedWrapper (LinkedColdLeaves.keyPrimitives ddg dsg)
        (LinkedColdLeaves.primitives (ProvedLeaves.primitives remaining dg hardware)
          compressCall sg cg ddg dsg) dg Signature.program.call)
      i initial =
      (firedancerObserve programs fdMessage fdSize fdSignature
        fdPublicKey (firedancerFreshSha fdState) (firedancerWithSha fdState)).map
        (fun ret => decide (ret = FD_ED25519_SUCCESS)) := by
  simpa only [hcanonical, decide_true, Bool.and_true] using
    ready_cold_crossClient_observations remaining dg hardware hhardware compressCall compression cg sg scg ddg dsg
      hleaves hdecodeRun hcompress i initial programs fdState fdMessage fdSize fdSignature
      fdPublicKey kbits input fdGlobals calls finishBlock hinit happend hfinish hcaller hagaveGlobals hframe
      hhash

end
end Agave.Ed25519.Bridge
