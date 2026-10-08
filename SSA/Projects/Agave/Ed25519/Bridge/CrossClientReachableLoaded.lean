import SSA.Projects.Agave.Ed25519.Bridge.CrossClientReachableSource
import SSA.Projects.Agave.Ed25519.Bridge.FiredancerBaseTableLoader

/-! Strongest current comparison boundary: base-table mathematics is derived
from the pinned Firedancer source initializer bytes. The only remaining SHA
premises are the four reachable source tail calls. -/
namespace Agave.Ed25519.Bridge.CrossClientReachableLoaded
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
variable (hsha : ∃ p, HoldsGlobal fdState "fd_sha512_core_ref.K" p kbits)
variable (table : LeanMLIR.Pointer) (hloaded : FiredancerBaseInitializer.Loaded fdState table)
variable (small : FiredancerReachableMemoryReady fdState fdMessage fdSignature fdPublicKey)
variable (hcaller : ColdInput.CallerMemory i initial (readBuf (input.args href.wf).pkBuf) (readBuf (input.args href.wf).sigBuf) (readBuf (input.args href.wf).sBuf) (bytesOf (readWord (input.args href.wf).msgFits)))
variable (hglobals : ColdInput.InitializedGlobals dg cg sg scg ddg dsg initial i.message)
variable (hserial : Ready serialGlobals d2 initial)
variable (havxGlobals : DoubleBase.ExecutionAvx2.GlobalsReady avx2Globals initial)
variable (hseparate : Separate serialGlobals d2 dg.address1)
variable (havxSeparate : avx2Globals.address2.id ≠ dg.address1.id)
variable (afterR afterA afterMessage : Option LeanMLIR.LiveBlock)
variable (hR : FiredancerReachableAppend SLLVMSource.programs kbits
  (SLLVMSource.initBlock (some { length := 256, bytes := 0#_ }) 0) afterR 0
  (bytesOf (n := 32) (readBuf (input.args href.wf).sigBuf)))
variable (hA : FiredancerReachableAppend SLLVMSource.programs kbits afterR afterA 0
  (bytesOf (n := 32) (readBuf (input.args href.wf).pkBuf)))
variable (hM : FiredancerReachableAppend SLLVMSource.programs kbits afterA afterMessage 0 (bytesOf (readWord (input.args href.wf).msgFits)))
variable (hF : FiredancerReachableFinish SLLVMSource.programs kbits
  afterMessage 0 ((SHA512.model SHA512.Spec.compression).digest (hashTranscript (readBuf (input.args href.wf).sigBuf) (readBuf (input.args href.wf).pkBuf) (bytesOf (readWord (input.args href.wf).msgFits)))))
include hhardware hbcmp hcaller hglobals hserial havxGlobals hseparate havxSeparate
  small hR hA hM hF hsha hloaded

theorem observations :
    Execution.observe
      (AgaveReady.wrapper (AgaveReady.bcmpOnly compareCall) dg hardware serialGlobals d2 panic
        avx2Panic avx2Globals cg sg scg ddg dsg) i initial =
      (firedancerObserve SLLVMSource.programs fdMessage fdSize fdSignature fdPublicKey
        (firedancerFreshSha fdState) (firedancerWithSha fdState)).map
        (fun ret => decide (ret = FD_ED25519_SUCCESS) && decide (CanonicalY (readBuf (input.args href.wf).sigBuf))) :=
  CrossClientReachableSource.observations
    compareCall dg hardware serialGlobals d2 panic avx2Panic avx2Globals
      cg sg scg ddg dsg hhardware hbcmp i initial fdState fdMessage fdSize fdSignature fdPublicKey
      kbits input
      (FiredancerBaseInitializer.globalsReady_of_loaded fdState kbits href hsha table hloaded) small hcaller hglobals hserial havxGlobals hseparate havxSeparate
      afterR afterA afterMessage hR hA hM hF

theorem observations_of_canonical (hcanonical : CanonicalY (readBuf (input.args href.wf).sigBuf)) :
    Execution.observe (AgaveReady.wrapper (AgaveReady.bcmpOnly compareCall) dg hardware serialGlobals d2 panic
        avx2Panic avx2Globals cg sg scg ddg dsg) i initial =
      (firedancerObserve SLLVMSource.programs fdMessage fdSize fdSignature fdPublicKey
        (firedancerFreshSha fdState) (firedancerWithSha fdState)).map (fun ret => decide (ret = FD_ED25519_SUCCESS)) :=
  CrossClientReachableSource.observations_of_canonical
    compareCall dg hardware serialGlobals d2 panic avx2Panic avx2Globals
      cg sg scg ddg dsg hhardware hbcmp i initial fdState fdMessage fdSize fdSignature fdPublicKey
      kbits input
      (FiredancerBaseInitializer.globalsReady_of_loaded fdState kbits href hsha table hloaded) small hcaller hglobals hserial havxGlobals hseparate havxSeparate
      afterR afterA afterMessage hR hA hM hF hcanonical

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
  CrossClientReachableSource.runs
    compareCall dg hardware serialGlobals d2 panic avx2Panic avx2Globals
      cg sg scg ddg dsg hhardware hbcmp i initial fdState fdMessage fdSize fdSignature fdPublicKey
      kbits input
      (FiredancerBaseInitializer.globalsReady_of_loaded fdState kbits href hsha table hloaded) small hcaller hglobals hserial havxGlobals hseparate havxSeparate
      afterR afterA afterMessage hR hA hM hF

end
end Agave.Ed25519.Bridge.CrossClientReachableLoaded
