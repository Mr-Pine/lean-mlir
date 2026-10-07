import SSA.Projects.Agave.Ed25519.Bridge.CrossClientReadyRuns
import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.PointwiseVerifier
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.FinalizationDispatchComplete

/-! Compare the actual verifier observations using only the current machine
SHA transcript. Both Agave scalar-multiplication backends and its SHA dispatcher
are the linked RIR implementations. Firedancer SHA correctness and simulation
are pointwise output-byte observations; there is no uniform hash oracle premise.
The reached-decoder prefix retains the public-key small-order branch guard. -/
namespace Agave.Ed25519.Bridge
open Verifier Verifier.Execution Firedancer Firedancer.Common
open LeanMLIR.RIR (Vals EffectM)
open Dalek.SerialBackendReadiness
open Agave.Ed25519.SHA512.Execution.Dispatch
attribute [local instance] Classical.propDecidable
attribute [local irreducible] firedancerRun
set_option maxRecDepth 16384

section
variable (remaining : Dalek.Primitives) (dg : Dalek.Globals)
variable (hardware : Dalek.Avx2Cache.Instructions.HardwareInstructions)
variable (hhardware : Dalek.Avx2Cache.Instructions.InstructionContracts hardware)
variable (serialGlobals : DoubleBase.SerialCFG.Globals)
variable (d2 : Tables.SerialConstructor.Globals) (panic : DoubleBase.RIR.SerialPanic)
variable (avx2Panic : Vals [.bv 64, .bv 64, .ptr] → EffectM (Vals []))
variable (avx2Globals : DoubleBase.Avx2CFG.Globals)
variable (cg : Execution.Challenge.Globals) (sg : ScalarWide.Globals)
variable (scg : SHA512Finalization.CompressionGlobals)
variable (ddg : Encoding.Decompress.Execution.Decode.Globals)
variable (dsg : Encoding.Decompress.Execution.SqrtRatio.Globals)
variable (hleaves : ContextualProvedLeaves.RemainingContracts remaining)
variable (hdecodeRun : Dalek.DecompressContractUnder (Encoding.Decompress.Execution.Ready ddg dsg)
  (Encoding.Decompress.Execution.linkedProgram ddg dsg).call
  (ValidPoint.layout SmallOrder.ValidPoint.timesEight) (ValidPoint.shared Encoding.Decompress.Valid.decode))
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
    (Finalization.linkedCall hardware scg) sg cg ddg dsg) ddg dsg Encoding.Decompress.Valid.decode i initial
  (readBuf (input.args fdGlobals.reference.wf).pkBuf)
  (readBuf (input.args fdGlobals.reference.wf).sigBuf)
  (bytesOf (readWord (input.args fdGlobals.reference.wf).msgFits)))
variable (v : FiredancerSHAExecution.TranscriptInvocation)
variable (hcorrect : v.Correct
  (readBuf (input.args fdGlobals.reference.wf).sigBuf)
  (readBuf (input.args fdGlobals.reference.wf).pkBuf)
  (bytesOf (readWord (input.args fdGlobals.reference.wf).msgFits)))
variable (hsim : v.Simulates calls (some { length := 256, bytes := 0#_ }) 0
  (readBuf (input.args fdGlobals.reference.wf).sigBuf)
  (readBuf (input.args fdGlobals.reference.wf).pkBuf)
  (bytesOf (readWord (input.args fdGlobals.reference.wf).msgFits)))


include hhardware hserial havxGlobals hseparate havxSeparate hprefix hleaves hdecodeRun hinit happend hfinish hcaller hagaveGlobals hframe hcorrect hsim

/-- One actual R || A || message digest observation suffices for the full
cross-client result. The canonical-R mask records the exact policy difference.
No compressor, scalar reducer, point-arithmetic, or whole-verifier execution
witness is supplied by the caller. -/
theorem pointwise_cold_crossClient_observations :
    Execution.observe
      (linkedWrapper (LinkedColdLeaves.keyPrimitives ddg dsg)
        (LinkedColdLeaves.primitives (ContextualProvedLeaves.primitives remaining dg hardware serialGlobals d2 panic avx2Panic avx2Globals)
          (Finalization.linkedCall hardware scg) sg cg ddg dsg) dg Signature.program.call)
      i initial =
      (firedancerObserve programs fdMessage fdSize fdSignature
        fdPublicKey (firedancerFreshSha fdState) (firedancerWithSha fdState)).map
        (fun ret => decide (ret = FD_ED25519_SUCCESS) &&
          decide (CanonicalY (readBuf (input.args fdGlobals.reference.wf).sigBuf))) := by
  have hdigest := (v.simulates_iff_digest calls _ _ _ _ _ hcorrect).mp hsim
  exact ready_contextual_cold_crossClient_observations remaining dg hardware hhardware
    serialGlobals d2 panic avx2Panic avx2Globals (Finalization.linkedCall hardware scg)
    Agave.Ed25519.SHA512.Spec.compression cg sg scg ddg dsg hleaves hdecodeRun
    (Finalization.Complete.linked_compress_contract hardware hhardware scg)
    i initial programs fdState fdMessage fdSize fdSignature fdPublicKey kbits input fdGlobals
    calls finishBlock hinit happend hfinish hcaller hagaveGlobals hframe hserial havxGlobals
    hseparate havxSeparate hprefix hdigest

/-- On canonical R, compare only Agave's Boolean with FD's success code. -/
theorem pointwise_cold_crossClient_of_canonical
    (hcanonical : CanonicalY (readBuf (input.args fdGlobals.reference.wf).sigBuf)) :
    Execution.observe
      (linkedWrapper (LinkedColdLeaves.keyPrimitives ddg dsg)
        (LinkedColdLeaves.primitives (ContextualProvedLeaves.primitives remaining dg hardware serialGlobals d2 panic avx2Panic avx2Globals)
          (Finalization.linkedCall hardware scg) sg cg ddg dsg) dg Signature.program.call)
      i initial =
      (firedancerObserve programs fdMessage fdSize fdSignature
        fdPublicKey (firedancerFreshSha fdState) (firedancerWithSha fdState)).map
        (fun ret => decide (ret = FD_ED25519_SUCCESS)) := by
  simpa only [hcanonical, decide_true, Bool.and_true] using
    pointwise_cold_crossClient_observations remaining dg hardware hhardware
      serialGlobals d2 panic avx2Panic avx2Globals cg sg scg ddg dsg
      hleaves hdecodeRun i initial programs fdState fdMessage fdSize fdSignature
      fdPublicKey kbits input fdGlobals calls finishBlock hinit happend hfinish hcaller hagaveGlobals hframe hserial havxGlobals hseparate havxSeparate hprefix
      v hcorrect hsim

/-- Both clients return defined values. The Agave Boolean is precisely FD
success together with canonical R; the two final states are constructed. -/
theorem pointwise_cold_crossClient_runs :
    ∃ (agaveFinal : LeanMLIR.RIR.GlobalState) (fdFinal : LeanMLIR.GlobalState)
      (b : Bool) (ret : BitVec 32),
      (Wrapper.program (linkedWrapper (LinkedColdLeaves.keyPrimitives ddg dsg)
        (LinkedColdLeaves.primitives (ContextualProvedLeaves.primitives remaining dg hardware serialGlobals d2 panic avx2Panic avx2Globals)
          (Finalization.linkedCall hardware scg) sg cg ddg dsg) dg Signature.program.call)).call i.args initial =
        .value (Wrapper.boolResult b, agaveFinal) ∧
      firedancerRun programs fdMessage fdSize fdSignature fdPublicKey
        (firedancerFreshSha fdState) (firedancerWithSha fdState) =
        .value (.cons (.value ret) .nil, fdFinal) ∧
      b = decide (ret = FD_ED25519_SUCCESS ∧
        CanonicalY (readBuf (input.args fdGlobals.reference.wf).sigBuf)) := by
  have hdigest := (v.simulates_iff_digest calls _ _ _ _ _ hcorrect).mp hsim
  exact ready_contextual_cold_crossClient_runs remaining dg hardware hhardware
    serialGlobals d2 panic avx2Panic avx2Globals (Finalization.linkedCall hardware scg)
    Agave.Ed25519.SHA512.Spec.compression cg sg scg ddg dsg hleaves hdecodeRun
    (Finalization.Complete.linked_compress_contract hardware hhardware scg)
    i initial programs fdState fdMessage fdSize fdSignature fdPublicKey kbits input fdGlobals
    calls finishBlock hinit happend hfinish hcaller hagaveGlobals hframe hserial havxGlobals
    hseparate havxSeparate hprefix hdigest

/-- With canonical R, both defined executions agree on acceptance. -/
theorem pointwise_cold_crossClient_runs_of_canonical
    (hcanonical : CanonicalY (readBuf (input.args fdGlobals.reference.wf).sigBuf)) :
    ∃ (agaveFinal : LeanMLIR.RIR.GlobalState) (fdFinal : LeanMLIR.GlobalState)
      (b : Bool) (ret : BitVec 32),
      (Wrapper.program (linkedWrapper (LinkedColdLeaves.keyPrimitives ddg dsg)
        (LinkedColdLeaves.primitives (ContextualProvedLeaves.primitives remaining dg hardware serialGlobals d2 panic avx2Panic avx2Globals)
          (Finalization.linkedCall hardware scg) sg cg ddg dsg) dg Signature.program.call)).call i.args initial =
        .value (Wrapper.boolResult b, agaveFinal) ∧
      firedancerRun programs fdMessage fdSize fdSignature fdPublicKey
        (firedancerFreshSha fdState) (firedancerWithSha fdState) =
        .value (.cons (.value ret) .nil, fdFinal) ∧
      b = decide (ret = FD_ED25519_SUCCESS) := by
  simpa only [hcanonical, and_true] using
    pointwise_cold_crossClient_runs remaining dg hardware hhardware
      serialGlobals d2 panic avx2Panic avx2Globals cg sg scg ddg dsg
      hleaves hdecodeRun i initial programs fdState fdMessage fdSize fdSignature
      fdPublicKey kbits input fdGlobals calls finishBlock hinit happend hfinish hcaller hagaveGlobals hframe hserial havxGlobals hseparate havxSeparate hprefix
      v hcorrect hsim

end
end Agave.Ed25519.Bridge
