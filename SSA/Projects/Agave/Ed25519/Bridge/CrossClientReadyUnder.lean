import SSA.Projects.Agave.Ed25519.Bridge.CrossClientProvedLeavesUnder
import SSA.Projects.Agave.Ed25519.Bridge.CrossClientBackendInputs
import SSA.Projects.Agave.Ed25519.Bridge.CrossClientGuardedCaller
import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.FullCall
import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressValidPoint

/-! Cross-client execution with both concrete backend proofs. The caller only
supplies actual loaded globals and the reached decoder prefix; all constructors, field
helpers, arithmetic blocks and backend execution are discharged internally. -/
namespace Agave.Ed25519.Bridge
open Verifier Verifier.Execution Firedancer Firedancer.Common
open LeanMLIR.RIR (Vals EffectM)
open Dalek.SerialBackendReadiness
attribute [local instance] Classical.propDecidable

section
variable (remaining : Dalek.Primitives) (dg : Dalek.Globals)
variable (hardware : Dalek.Avx2Cache.Instructions.HardwareInstructions)
variable (hhardware : Dalek.Avx2Cache.Instructions.InstructionContracts hardware)
variable (serialGlobals : DoubleBase.SerialCFG.Globals)
variable (d2 : Tables.SerialConstructor.Globals) (panic : DoubleBase.RIR.SerialPanic)
variable (avx2Panic : Vals [.bv 64, .bv 64, .ptr] → EffectM (Vals []))
variable (avx2Globals : DoubleBase.Avx2CFG.Globals)
variable (compressCall : Vals [.ptr, .ptr, .bv 64] → EffectM (Vals []))
variable (compression : Agave.Ed25519.SHA512.Compression)
variable (cg : Execution.Challenge.Globals) (sg : ScalarWide.Globals)
variable (scg : SHA512Finalization.CompressionGlobals)
variable (ddg : Encoding.Decompress.Execution.Decode.Globals)
variable (dsg : Encoding.Decompress.Execution.SqrtRatio.Globals)
variable (hleaves : ContextualProvedLeaves.RemainingContracts remaining)
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
variable (hserial : Ready serialGlobals d2 initial)
variable (havxGlobals : DoubleBase.ExecutionAvx2.GlobalsReady avx2Globals initial)
variable (hseparate : Separate serialGlobals d2 dg.address1)
variable (havxSeparate : avx2Globals.address2.id ≠ dg.address1.id)
variable (hprefix : BackendReadiness.DecoderPrefix (LinkedColdLeaves.keyPrimitives ddg dsg)
  (LinkedColdLeaves.primitives (ContextualProvedLeaves.primitives remaining dg hardware serialGlobals d2 panic avx2Panic avx2Globals)
    compressCall sg cg ddg dsg) ddg dsg Encoding.Decompress.Valid.decode i initial
  (readBuf (input.args fdGlobals.reference.wf).pkBuf)
  (readBuf (input.args fdGlobals.reference.wf).sigBuf)
  (bytesOf (readWord (input.args fdGlobals.reference.wf).msgFits)))
variable (hdigest : firedancerDigest calls
  (some { length := 256, bytes := 0#_ }) 0
  (readBuf (input.args fdGlobals.reference.wf).sigBuf)
  (readBuf (input.args fdGlobals.reference.wf).pkBuf)
  (bytesOf (readWord (input.args fdGlobals.reference.wf).msgFits)) =
  some ((Agave.Ed25519.SHA512.model compression).digest (hashTranscript
    (readBuf (input.args fdGlobals.reference.wf).sigBuf)
    (readBuf (input.args fdGlobals.reference.wf).pkBuf)
    (bytesOf (readWord (input.args fdGlobals.reference.wf).msgFits)))))


include hhardware hserial havxGlobals hseparate havxSeparate hprefix hleaves hdecodeRun hcompress hinit happend hfinish hcaller hagaveGlobals hframe hdigest

/-- Concrete backend witnesses and initial loaded globals determine the full
cross-client observation, subject only to the remaining SHA/decoder/ABI and
reached decoder-prefix boundaries. -/
theorem ready_contextual_cold_crossClient_observations :
    Execution.observe
      (linkedWrapper (LinkedColdLeaves.keyPrimitives ddg dsg)
        (LinkedColdLeaves.primitives (ContextualProvedLeaves.primitives remaining dg hardware serialGlobals d2 panic avx2Panic avx2Globals)
          compressCall sg cg ddg dsg) dg Signature.program.call)
      i initial =
      (firedancerObserve programs fdMessage fdSize fdSignature
        fdPublicKey (firedancerFreshSha fdState) (firedancerWithSha fdState)).map
        (fun ret => decide (ret = FD_ED25519_SUCCESS) &&
          decide (CanonicalY (readBuf (input.args fdGlobals.reference.wf).sigBuf))) := by
  have hbackend := BackendReadiness.inputs
    (LinkedColdLeaves.primitives (ContextualProvedLeaves.primitives remaining dg hardware serialGlobals d2 panic avx2Panic avx2Globals)
      compressCall sg cg ddg dsg) dg cg sg scg ddg dsg Encoding.Decompress.Valid.decode SmallOrder.ValidPoint.timesEight
    hardware hhardware ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ serialGlobals d2 avx2Globals compressCall compression rfl rfl hcompress hdecodeRun i initial _ _ _ _
    hcaller hagaveGlobals hframe hserial havxGlobals hseparate havxSeparate hprefix
  exact parameterizedCaller_guarded_cold_crossClient_observations
    (ContextualProvedLeaves.primitives remaining dg hardware serialGlobals d2 panic avx2Panic avx2Globals) dg
    compressCall compression cg sg scg ddg dsg Encoding.Decompress.Valid.decode SmallOrder.ValidPoint.timesEight
    Encoding.Decompress.Valid.decoderCorrect
    (DoubleBase.RIR.serialLinkedReady serialGlobals d2) (BackendLeaves.avx2Ready avx2Globals)
    (ContextualProvedLeaves.RemainingContracts.complete remaining dg hardware serialGlobals d2 panic
      avx2Panic avx2Globals Encoding.Decompress.Valid.decode hleaves hhardware)
    hdecodeRun hcompress (ScalarWide.execution_obligation sg) i initial
    programs fdState fdMessage fdSize fdSignature fdPublicKey kbits input fdGlobals calls finishBlock
    hinit happend hfinish hcaller hagaveGlobals hframe hbackend hdigest

/-- On canonical R, compare only Agave's Boolean with FD's success code. -/
theorem ready_contextual_cold_crossClient_of_canonical
    (hcanonical : CanonicalY (readBuf (input.args fdGlobals.reference.wf).sigBuf)) :
    Execution.observe
      (linkedWrapper (LinkedColdLeaves.keyPrimitives ddg dsg)
        (LinkedColdLeaves.primitives (ContextualProvedLeaves.primitives remaining dg hardware serialGlobals d2 panic avx2Panic avx2Globals)
          compressCall sg cg ddg dsg) dg Signature.program.call)
      i initial =
      (firedancerObserve programs fdMessage fdSize fdSignature
        fdPublicKey (firedancerFreshSha fdState) (firedancerWithSha fdState)).map
        (fun ret => decide (ret = FD_ED25519_SUCCESS)) := by
  simpa only [hcanonical, decide_true, Bool.and_true] using
    ready_contextual_cold_crossClient_observations remaining dg hardware hhardware
      serialGlobals d2 panic avx2Panic avx2Globals compressCall compression cg sg scg ddg dsg
      hleaves hdecodeRun hcompress i initial programs fdState fdMessage fdSize fdSignature
      fdPublicKey kbits input fdGlobals calls finishBlock hinit happend hfinish hcaller hagaveGlobals hframe hserial havxGlobals hseparate havxSeparate hprefix
      hdigest

end
end Agave.Ed25519.Bridge
