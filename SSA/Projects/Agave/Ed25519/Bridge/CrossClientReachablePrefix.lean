import SSA.Projects.Agave.Ed25519.Bridge.CrossClientReachableRawLoaded
import SSA.Projects.Agave.Ed25519.Bridge.FiredancerReachableSourcePrefix

/-! The raw-loaded bridge with both 32-byte source append contracts discharged.
The remaining boundary is exactly the third append and finalizer, with the
incoming context fixed by the actual signature and public-key bytes.  This
module does not claim to discharge those two remaining source-call premises. -/
namespace Agave.Ed25519.Bridge.CrossClientReachablePrefix
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
variable (fdSignature fdPublicKey : LeanMLIR.Pointer) (kbits : BitVec (80 * 64))
variable (input : FiredancerInputReady fdState fdMessage fdSize fdSignature fdPublicKey)
variable (href : fdState.RefWF [])
variable (shaConstants : LeanMLIR.Pointer)
variable (hshaLoaded : FiredancerShaRawLoaded fdState shaConstants kbits)
variable (table : LeanMLIR.Pointer) (hloaded : FiredancerBaseInitializer.Loaded fdState table)
variable (hmsgSmall : FiredancerBlockSmall fdState.mem fdMessage.id)
variable (hsigSmall : FiredancerBlockSmall fdState.mem fdSignature.id)
variable (hpkSmall : FiredancerBlockSmall fdState.mem fdPublicKey.id)
variable (hcaller : ColdInput.CallerMemory i initial (readBuf (input.args href.wf).pkBuf) (readBuf (input.args href.wf).sigBuf) (readBuf (input.args href.wf).sBuf) (bytesOf (readWord (input.args href.wf).msgFits)))
variable (hglobals : ColdInput.InitializedGlobals dg cg sg scg ddg dsg initial i.message)
variable (hserial : Ready serialGlobals d2 initial)
variable (havxGlobals : DoubleBase.ExecutionAvx2.GlobalsReady avx2Globals initial)
variable (hseparate : Separate serialGlobals d2 dg.address1)
variable (havxSeparate : avx2Globals.address2.id ≠ dg.address1.id)
variable (afterMessage : Option LeanMLIR.LiveBlock)
variable (hM : FiredancerReachableAppend SLLVMSource.programs kbits
  (SLLVMSource.verifierAfterA (readBuf (input.args href.wf).sigBuf)
    (readBuf (input.args href.wf).pkBuf)) afterMessage 0 (bytesOf (readWord (input.args href.wf).msgFits)))
variable (hF : FiredancerReachableFinish SLLVMSource.programs kbits
  afterMessage 0 ((SHA512.model SHA512.Spec.compression).digest (hashTranscript (readBuf (input.args href.wf).sigBuf) (readBuf (input.args href.wf).pkBuf) (bytesOf (readWord (input.args href.wf).msgFits)))))
include hhardware hbcmp hcaller hglobals hserial havxGlobals hseparate havxSeparate
  hmsgSmall hsigSmall hpkSmall hM hF hshaLoaded hloaded

theorem observations :
    Execution.observe
      (AgaveReady.wrapper (AgaveReady.bcmpOnly compareCall) dg hardware serialGlobals d2 panic
        avx2Panic avx2Globals cg sg scg ddg dsg) i initial =
      (firedancerObserve SLLVMSource.programs fdMessage fdSize fdSignature fdPublicKey
        (firedancerFreshSha fdState) (firedancerWithSha fdState)).map
        (fun ret => decide (ret = FD_ED25519_SUCCESS) && decide (CanonicalY (readBuf (input.args href.wf).sigBuf))) :=
  CrossClientReachableRawLoaded.observations
    compareCall dg hardware serialGlobals d2 panic avx2Panic avx2Globals
      cg sg scg ddg dsg hhardware hbcmp i initial fdState fdMessage fdSize fdSignature fdPublicKey
      kbits input href shaConstants hshaLoaded table hloaded
      hmsgSmall hsigSmall hpkSmall
      hcaller hglobals hserial havxGlobals hseparate havxSeparate
      (SLLVMSource.verifierAfterR (readBuf (input.args href.wf).sigBuf))
      (SLLVMSource.verifierAfterA (readBuf (input.args href.wf).sigBuf)
        (readBuf (input.args href.wf).pkBuf)) afterMessage
      (SLLVMSource.verifierAppendR kbits (readBuf (input.args href.wf).sigBuf))
      (SLLVMSource.verifierAppendA kbits (readBuf (input.args href.wf).sigBuf)
        (readBuf (input.args href.wf).pkBuf)) hM hF

theorem observations_of_canonical (hcanonical : CanonicalY (readBuf (input.args href.wf).sigBuf)) :
    Execution.observe (AgaveReady.wrapper (AgaveReady.bcmpOnly compareCall) dg hardware serialGlobals d2 panic
        avx2Panic avx2Globals cg sg scg ddg dsg) i initial =
      (firedancerObserve SLLVMSource.programs fdMessage fdSize fdSignature fdPublicKey
        (firedancerFreshSha fdState) (firedancerWithSha fdState)).map (fun ret => decide (ret = FD_ED25519_SUCCESS)) :=
  CrossClientReachableRawLoaded.observations_of_canonical
    compareCall dg hardware serialGlobals d2 panic avx2Panic avx2Globals
      cg sg scg ddg dsg hhardware hbcmp i initial fdState fdMessage fdSize fdSignature fdPublicKey
      kbits input href shaConstants hshaLoaded table hloaded
      hmsgSmall hsigSmall hpkSmall
      hcaller hglobals hserial havxGlobals hseparate havxSeparate
      (SLLVMSource.verifierAfterR (readBuf (input.args href.wf).sigBuf))
      (SLLVMSource.verifierAfterA (readBuf (input.args href.wf).sigBuf)
        (readBuf (input.args href.wf).pkBuf)) afterMessage
      (SLLVMSource.verifierAppendR kbits (readBuf (input.args href.wf).sigBuf))
      (SLLVMSource.verifierAppendA kbits (readBuf (input.args href.wf).sigBuf)
        (readBuf (input.args href.wf).pkBuf)) hM hF hcanonical

theorem runs :
    ∃ (agaveFinal : LeanMLIR.RIR.GlobalState) (fdFinal : LeanMLIR.GlobalState)
      (b : Bool) (ret : BitVec 32),
      (Wrapper.program (AgaveReady.wrapper (AgaveReady.bcmpOnly compareCall) dg hardware serialGlobals d2 panic
        avx2Panic avx2Globals cg sg scg ddg dsg)).call i.args initial =
        .value (Wrapper.boolResult b, agaveFinal) ∧
      firedancerRun SLLVMSource.programs fdMessage fdSize fdSignature fdPublicKey
        (firedancerFreshSha fdState) (firedancerWithSha fdState) =
        .value ([.value ret]ₕ, fdFinal) ∧
      b = (decide (ret = FD_ED25519_SUCCESS) && decide (CanonicalY (readBuf (input.args href.wf).sigBuf))) :=
  CrossClientReachableRawLoaded.runs
    compareCall dg hardware serialGlobals d2 panic avx2Panic avx2Globals
      cg sg scg ddg dsg hhardware hbcmp i initial fdState fdMessage fdSize fdSignature fdPublicKey
      kbits input href shaConstants hshaLoaded table hloaded
      hmsgSmall hsigSmall hpkSmall
      hcaller hglobals hserial havxGlobals hseparate havxSeparate
      (SLLVMSource.verifierAfterR (readBuf (input.args href.wf).sigBuf))
      (SLLVMSource.verifierAfterA (readBuf (input.args href.wf).sigBuf)
        (readBuf (input.args href.wf).pkBuf)) afterMessage
      (SLLVMSource.verifierAppendR kbits (readBuf (input.args href.wf).sigBuf))
      (SLLVMSource.verifierAppendA kbits (readBuf (input.args href.wf).sigBuf)
        (readBuf (input.args href.wf).pkBuf)) hM hF

end
end Agave.Ed25519.Bridge.CrossClientReachablePrefix
