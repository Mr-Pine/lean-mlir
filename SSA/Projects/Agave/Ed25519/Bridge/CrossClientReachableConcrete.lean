import SSA.Projects.Agave.Ed25519.Bridge.CrossClientReachablePrefix
import SSA.Projects.Agave.Ed25519.Bridge.FiredancerReachableConcreteCalls
import SSA.Projects.Agave.Ed25519.Bridge.FiredancerFieldInitializer

/-! Actual Agave RIR and Firedancer source executions from caller memory and
raw source-pinned initialized globals. All SHA init/append/finish calls are
proved internally; there is no SHA execution, digest, or result-equality premise.
The policy difference is explicit: Agave accepts exactly Firedancer success
with canonical R. -/
namespace Agave.Ed25519.Bridge.CrossClientReachableConcrete
open Verifier Verifier.Execution Firedancer Firedancer.Common
open LeanMLIR.RIR (Vals EffectM)
open Dalek.SerialBackendReadiness (Ready Separate)
open FiredancerSHAExecution
attribute [local instance] Classical.propDecidable
set_option maxRecDepth 24000
set_option maxHeartbeats 8000000
section
variable (compareCall : Vals [.ptr, .ptr, .bv 64] → EffectM (Vals [.bv 32]))
variable (dg : Dalek.Globals)
variable (hardware : Dalek.Avx2Cache.Instructions.HardwareInstructions)
variable (serialGlobals : DoubleBase.SerialCFG.Globals)
variable (d2 : Tables.SerialConstructor.Globals) (panic : DoubleBase.RIR.SerialPanic)
variable (avx2Panic : Vals [.bv 64, .bv 64, .ptr] → EffectM (Vals []))
variable (avx2Globals : DoubleBase.Avx2CFG.Globals)
variable (cg : Execution.Challenge.Globals) (sg : ScalarWide.Globals)
variable (scg : SHA512Finalization.CompressionGlobals)
variable (ddg : Encoding.Decompress.Execution.Decode.Globals)
variable (dsg : Encoding.Decompress.Execution.SqrtRatio.Globals)
variable (hhardware : Dalek.Avx2Cache.Instructions.InstructionContracts hardware)
variable (hbcmp : Dalek.CompareContract compareCall)
variable (i : Invocation) (initial : LeanMLIR.RIR.GlobalState)
variable (fdState : LeanMLIR.GlobalState) (fdMessage : LeanMLIR.Pointer) (fdSize : BitVec 64)
variable (fdSignature fdPublicKey : LeanMLIR.Pointer)
variable (input : FiredancerInputReady fdState fdMessage fdSize fdSignature fdPublicKey)
variable (hwf : fdState.WF)
variable (hfields : FiredancerFieldInitializer.Loaded fdState)
variable (shaConstants : LeanMLIR.Pointer)
variable (hshaLoaded : FiredancerShaRawLoaded fdState shaConstants constantsBytes)
variable (table : LeanMLIR.Pointer) (hloaded : FiredancerBaseInitializer.Loaded fdState table)
variable (hmsgSmall : FiredancerBlockSmall fdState.mem fdMessage.id)
variable (hsigSmall : FiredancerBlockSmall fdState.mem fdSignature.id)
variable (hpkSmall : FiredancerBlockSmall fdState.mem fdPublicKey.id)
variable (hcaller : ColdInput.CallerMemory i initial (readBuf (input.args hwf).pkBuf) (readBuf (input.args hwf).sigBuf) (readBuf (input.args hwf).sBuf) (bytesOf (readWord (input.args hwf).msgFits)))
variable (hglobals : ColdInput.InitializedGlobals dg cg sg scg ddg dsg initial i.message)
variable (hserial : Ready serialGlobals d2 initial)
variable (havxGlobals : DoubleBase.ExecutionAvx2.GlobalsReady avx2Globals initial)
variable (hseparate : Separate serialGlobals d2 dg.address1)
variable (havxSeparate : avx2Globals.address2.id ≠ dg.address1.id)
include hhardware hbcmp hcaller hglobals hserial havxGlobals hseparate havxSeparate
  hmsgSmall hsigSmall hpkSmall hshaLoaded hloaded hfields

theorem observations :
    Execution.observe
      (AgaveReady.wrapper (AgaveReady.bcmpOnly compareCall) dg hardware serialGlobals d2 panic
        avx2Panic avx2Globals cg sg scg ddg dsg) i initial =
      (firedancerObserve SLLVMSource.programs fdMessage fdSize fdSignature fdPublicKey
        (firedancerFreshSha fdState) (firedancerWithSha fdState)).map
        (fun ret => decide (ret = FD_ED25519_SUCCESS) && decide (CanonicalY (readBuf (input.args hwf).sigBuf))) := by
  have hm : (bytesOf (readWord (input.args hwf).msgFits)).length < 2^63 := by
    simpa only [bytesOf, List.length_ofFn] using
      SLLVMSource.verifierMessage_small input.message hmsgSmall
  obtain ⟨afterMessage, hM, hF⟩ := SLLVMSource.verifierTailCalls
    (readBuf (input.args hwf).sigBuf) (readBuf (input.args hwf).pkBuf)
    (bytesOf (readWord (input.args hwf).msgFits)) hm
  exact CrossClientReachablePrefix.observations
    compareCall dg hardware serialGlobals d2 panic avx2Panic avx2Globals
      cg sg scg ddg dsg hhardware hbcmp i initial fdState fdMessage fdSize fdSignature fdPublicKey
      constantsBytes input (hfields.refWF hwf hloaded) shaConstants hshaLoaded table hloaded
      hmsgSmall hsigSmall hpkSmall
      hcaller hglobals hserial havxGlobals hseparate havxSeparate
      afterMessage hM hF

theorem observations_of_canonical (hcanonical : CanonicalY (readBuf (input.args hwf).sigBuf)) :
    Execution.observe (AgaveReady.wrapper (AgaveReady.bcmpOnly compareCall) dg hardware serialGlobals d2 panic
        avx2Panic avx2Globals cg sg scg ddg dsg) i initial =
      (firedancerObserve SLLVMSource.programs fdMessage fdSize fdSignature fdPublicKey
        (firedancerFreshSha fdState) (firedancerWithSha fdState)).map (fun ret => decide (ret = FD_ED25519_SUCCESS)) := by
  have hm : (bytesOf (readWord (input.args hwf).msgFits)).length < 2^63 := by
    simpa only [bytesOf, List.length_ofFn] using
      SLLVMSource.verifierMessage_small input.message hmsgSmall
  obtain ⟨afterMessage, hM, hF⟩ := SLLVMSource.verifierTailCalls
    (readBuf (input.args hwf).sigBuf) (readBuf (input.args hwf).pkBuf)
    (bytesOf (readWord (input.args hwf).msgFits)) hm
  exact CrossClientReachablePrefix.observations_of_canonical
    compareCall dg hardware serialGlobals d2 panic avx2Panic avx2Globals
      cg sg scg ddg dsg hhardware hbcmp i initial fdState fdMessage fdSize fdSignature fdPublicKey
      constantsBytes input (hfields.refWF hwf hloaded) shaConstants hshaLoaded table hloaded
      hmsgSmall hsigSmall hpkSmall
      hcaller hglobals hserial havxGlobals hseparate havxSeparate
      afterMessage hM hF hcanonical

theorem runs :
    ∃ (agaveFinal : LeanMLIR.RIR.GlobalState) (fdFinal : LeanMLIR.GlobalState)
      (b : Bool) (ret : BitVec 32),
      (Wrapper.program (AgaveReady.wrapper (AgaveReady.bcmpOnly compareCall) dg hardware serialGlobals d2 panic
        avx2Panic avx2Globals cg sg scg ddg dsg)).call i.args initial =
        .value (Wrapper.boolResult b, agaveFinal) ∧
      firedancerRun SLLVMSource.programs fdMessage fdSize fdSignature fdPublicKey
        (firedancerFreshSha fdState) (firedancerWithSha fdState) =
        .value ([.value ret]ₕ, fdFinal) ∧
      b = (decide (ret = FD_ED25519_SUCCESS) && decide (CanonicalY (readBuf (input.args hwf).sigBuf))) := by
  have hm : (bytesOf (readWord (input.args hwf).msgFits)).length < 2^63 := by
    simpa only [bytesOf, List.length_ofFn] using
      SLLVMSource.verifierMessage_small input.message hmsgSmall
  obtain ⟨afterMessage, hM, hF⟩ := SLLVMSource.verifierTailCalls
    (readBuf (input.args hwf).sigBuf) (readBuf (input.args hwf).pkBuf)
    (bytesOf (readWord (input.args hwf).msgFits)) hm
  exact CrossClientReachablePrefix.runs
    compareCall dg hardware serialGlobals d2 panic avx2Panic avx2Globals
      cg sg scg ddg dsg hhardware hbcmp i initial fdState fdMessage fdSize fdSignature fdPublicKey
      constantsBytes input (hfields.refWF hwf hloaded) shaConstants hshaLoaded table hloaded
      hmsgSmall hsigSmall hpkSmall
      hcaller hglobals hserial havxGlobals hseparate havxSeparate
      afterMessage hM hF

end
end Agave.Ed25519.Bridge.CrossClientReachableConcrete
