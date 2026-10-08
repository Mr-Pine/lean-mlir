import SSA.Projects.Agave.Ed25519.Bridge.AgaveBcmpOnly
import SSA.Projects.Agave.Ed25519.Bridge.FiredancerReachableSourceInit

/-! Actual Agave RIR wrapper versus actual Firedancer SLLVM verifier, including
its source SHA programs. Agave's only opaque function is bcmp. Firedancer's
remaining semantic obligations are exactly the three reachable append calls
and one finish call; source initialization and reduction are already proved. -/
namespace Agave.Ed25519.Bridge.CrossClientReachableSource
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
variable (fdGlobals : FiredancerGlobalsReady fdState kbits)
variable (small : FiredancerReachableMemoryReady fdState fdMessage fdSignature fdPublicKey)
variable (hcaller : ColdInput.CallerMemory i initial (readBuf (input.args fdGlobals.reference.wf).pkBuf) (readBuf (input.args fdGlobals.reference.wf).sigBuf) (readBuf (input.args fdGlobals.reference.wf).sBuf) (bytesOf (readWord (input.args fdGlobals.reference.wf).msgFits)))
variable (hglobals : ColdInput.InitializedGlobals dg cg sg scg ddg dsg initial i.message)
variable (hserial : Ready serialGlobals d2 initial)
variable (havxGlobals : DoubleBase.ExecutionAvx2.GlobalsReady avx2Globals initial)
variable (hseparate : Separate serialGlobals d2 dg.address1)
variable (havxSeparate : avx2Globals.address2.id ≠ dg.address1.id)
variable (afterR afterA afterMessage : Option LeanMLIR.LiveBlock)
variable (hR : FiredancerReachableAppend SLLVMSource.programs kbits
  (SLLVMSource.initBlock (some { length := 256, bytes := 0#_ }) 0) afterR 0
  (bytesOf (n := 32) (readBuf (input.args fdGlobals.reference.wf).sigBuf)))
variable (hA : FiredancerReachableAppend SLLVMSource.programs kbits afterR afterA 0
  (bytesOf (n := 32) (readBuf (input.args fdGlobals.reference.wf).pkBuf)))
variable (hM : FiredancerReachableAppend SLLVMSource.programs kbits afterA afterMessage 0 (bytesOf (readWord (input.args fdGlobals.reference.wf).msgFits)))
variable (hF : FiredancerReachableFinish SLLVMSource.programs kbits
  afterMessage 0 ((SHA512.model SHA512.Spec.compression).digest (hashTranscript (readBuf (input.args fdGlobals.reference.wf).sigBuf) (readBuf (input.args fdGlobals.reference.wf).pkBuf) (bytesOf (readWord (input.args fdGlobals.reference.wf).msgFits)))))
include hhardware hbcmp hcaller hglobals hserial havxGlobals hseparate havxSeparate
  small hR hA hM hF

/-- The observation equality compares both actual executions. The SHA premises
are four individual reachable source calls with their store/frame results,
never a transcript equality or a whole-verifier execution hypothesis. -/
theorem observations :
    Execution.observe
      (AgaveReady.wrapper (AgaveReady.bcmpOnly compareCall) dg hardware serialGlobals d2 panic
        avx2Panic avx2Globals cg sg scg ddg dsg) i initial =
      (firedancerObserve SLLVMSource.programs fdMessage fdSize fdSignature fdPublicKey
        (firedancerFreshSha fdState) (firedancerWithSha fdState)).map
        (fun ret => decide (ret = FD_ED25519_SUCCESS) && decide (CanonicalY (readBuf (input.args fdGlobals.reference.wf).sigBuf))) := by
  let calls := SLLVMSource.reachableCalls (some { length := 256, bytes := 0#_ }) 0
    kbits (readBuf (input.args fdGlobals.reference.wf).sigBuf) (readBuf (input.args fdGlobals.reference.wf).pkBuf) (bytesOf (readWord (input.args fdGlobals.reference.wf).msgFits)) ((SHA512.model SHA512.Spec.compression).digest (hashTranscript (readBuf (input.args fdGlobals.reference.wf).sigBuf) (readBuf (input.args fdGlobals.reference.wf).pkBuf) (bytesOf (readWord (input.args fdGlobals.reference.wf).msgFits)))) afterR afterA afterMessage hR hA hM hF
  have hexecution := firedancerReachable_ready_executionRefines SLLVMSource.programs
    fdState fdMessage fdSize fdSignature fdPublicKey kbits input fdGlobals small ((SHA512.model SHA512.Spec.compression).digest (hashTranscript (readBuf (input.args fdGlobals.reference.wf).sigBuf) (readBuf (input.args fdGlobals.reference.wf).pkBuf) (bytesOf (readWord (input.args fdGlobals.reference.wf).msgFits)))) calls
  have hiff := agave_iff_firedancerObserve_success_and_canonical SLLVMSource.programs
    fdMessage fdSize fdSignature fdPublicKey (firedancerFreshSha fdState)
    (firedancerWithSha fdState) (readBuf (input.args fdGlobals.reference.wf).pkBuf) (readBuf (input.args fdGlobals.reference.wf).sigBuf) (readBuf (input.args fdGlobals.reference.wf).sBuf) (hashToScalar ((SHA512.model SHA512.Spec.compression).digest (hashTranscript (readBuf (input.args fdGlobals.reference.wf).sigBuf) (readBuf (input.args fdGlobals.reference.wf).pkBuf) (bytesOf (readWord (input.args fdGlobals.reference.wf).msgFits))))) hexecution
  obtain ⟨finalState, ret, hrun, _⟩ := hexecution
  have hfd : firedancerObserve SLLVMSource.programs fdMessage fdSize fdSignature fdPublicKey
      (firedancerFreshSha fdState) (firedancerWithSha fdState) = some ret := by
    unfold firedancerObserve
    rw [hrun]
    rfl
  rw [AgaveReady.observe_strict (AgaveReady.bcmpOnly compareCall) dg hardware serialGlobals d2
    panic avx2Panic avx2Globals cg sg scg ddg dsg hhardware hbcmp i initial (readBuf (input.args fdGlobals.reference.wf).pkBuf) (readBuf (input.args fdGlobals.reference.wf).sigBuf) (readBuf (input.args fdGlobals.reference.wf).sBuf) (bytesOf (readWord (input.args fdGlobals.reference.wf).msgFits))
    hcaller hglobals hserial havxGlobals hseparate havxSeparate, hfd]
  simp only [Option.map_some, Option.some.injEq]
  apply Bool.eq_iff_iff.mpr
  rw [hfd] at hiff
  change decide (AgaveStrictAccept (readBuf (input.args fdGlobals.reference.wf).pkBuf) (readBuf (input.args fdGlobals.reference.wf).sigBuf) (readBuf (input.args fdGlobals.reference.wf).sBuf).toNat
    (hashToScalar ((SHA512.model SHA512.Spec.compression).digest (hashTranscript (readBuf (input.args fdGlobals.reference.wf).sigBuf) (readBuf (input.args fdGlobals.reference.wf).pkBuf) (bytesOf (readWord (input.args fdGlobals.reference.wf).msgFits)))))) = true ↔ _
  simp only [decide_eq_true_eq, Bool.and_eq_true]
  simpa only [Option.some.injEq] using hiff

/-- Canonical R removes the exact policy mask. -/
theorem observations_of_canonical (hcanonical : CanonicalY (readBuf (input.args fdGlobals.reference.wf).sigBuf)) :
    Execution.observe (AgaveReady.wrapper (AgaveReady.bcmpOnly compareCall) dg hardware serialGlobals d2 panic
        avx2Panic avx2Globals cg sg scg ddg dsg) i initial =
      (firedancerObserve SLLVMSource.programs fdMessage fdSize fdSignature fdPublicKey
        (firedancerFreshSha fdState) (firedancerWithSha fdState)).map (fun ret => decide (ret = FD_ED25519_SUCCESS)) := by
  simpa only [hcanonical, decide_true, Bool.and_true] using observations
    compareCall dg hardware serialGlobals d2 panic avx2Panic avx2Globals
      cg sg scg ddg dsg hhardware hbcmp i initial fdState fdMessage fdSize fdSignature fdPublicKey
      kbits input fdGlobals small hcaller hglobals hserial havxGlobals hseparate havxSeparate
      afterR afterA afterMessage hR hA hM hF

/-- Both linked source programs return defined values, related by exactly
the canonical-R policy mask. This also covers all rejecting paths. -/
theorem runs :
    ∃ (agaveFinal : LeanMLIR.RIR.GlobalState) (fdFinal : LeanMLIR.GlobalState)
      (b : Bool) (ret : BitVec 32),
      (Wrapper.program (AgaveReady.wrapper (AgaveReady.bcmpOnly compareCall) dg hardware serialGlobals d2 panic
        avx2Panic avx2Globals cg sg scg ddg dsg)).call i.args initial =
        .value (Wrapper.boolResult b, agaveFinal) ∧
      firedancerRun SLLVMSource.programs fdMessage fdSize fdSignature fdPublicKey
        (firedancerFreshSha fdState) (firedancerWithSha fdState) =
        .value ([.value ret]ₕ, fdFinal) ∧
      b = (decide (ret = FD_ED25519_SUCCESS) && decide (CanonicalY (readBuf (input.args fdGlobals.reference.wf).sigBuf))) := by
  obtain ⟨agaveFinal, hagave⟩ := AgaveReady.call_strict_bcmp
    compareCall dg hardware serialGlobals d2 panic avx2Panic avx2Globals cg sg scg ddg dsg
    hhardware hbcmp i initial (readBuf (input.args fdGlobals.reference.wf).pkBuf) (readBuf (input.args fdGlobals.reference.wf).sigBuf) (readBuf (input.args fdGlobals.reference.wf).sBuf) (bytesOf (readWord (input.args fdGlobals.reference.wf).msgFits))
    hcaller hglobals hserial havxGlobals hseparate havxSeparate
  let calls := SLLVMSource.reachableCalls (some { length := 256, bytes := 0#_ }) 0
    kbits (readBuf (input.args fdGlobals.reference.wf).sigBuf) (readBuf (input.args fdGlobals.reference.wf).pkBuf) (bytesOf (readWord (input.args fdGlobals.reference.wf).msgFits)) ((SHA512.model SHA512.Spec.compression).digest (hashTranscript (readBuf (input.args fdGlobals.reference.wf).sigBuf) (readBuf (input.args fdGlobals.reference.wf).pkBuf) (bytesOf (readWord (input.args fdGlobals.reference.wf).msgFits)))) afterR afterA afterMessage hR hA hM hF
  obtain ⟨fdFinal, ret, hfd, hchecks⟩ := firedancerReachable_ready_executionRefines
    SLLVMSource.programs fdState fdMessage fdSize fdSignature fdPublicKey kbits input fdGlobals
    small ((SHA512.model SHA512.Spec.compression).digest (hashTranscript (readBuf (input.args fdGlobals.reference.wf).sigBuf) (readBuf (input.args fdGlobals.reference.wf).pkBuf) (bytesOf (readWord (input.args fdGlobals.reference.wf).msgFits)))) calls
  refine ⟨agaveFinal, fdFinal, AgaveReady.strictVerify (readBuf (input.args fdGlobals.reference.wf).pkBuf) (readBuf (input.args fdGlobals.reference.wf).sigBuf) (readBuf (input.args fdGlobals.reference.wf).sBuf) (bytesOf (readWord (input.args fdGlobals.reference.wf).msgFits)), ret,
    hagave, hfd, ?_⟩
  apply Bool.eq_iff_iff.mpr
  change decide (AgaveStrictAccept (readBuf (input.args fdGlobals.reference.wf).pkBuf) (readBuf (input.args fdGlobals.reference.wf).sigBuf) (readBuf (input.args fdGlobals.reference.wf).sBuf).toNat
    (hashToScalar ((SHA512.model SHA512.Spec.compression).digest (hashTranscript (readBuf (input.args fdGlobals.reference.wf).sigBuf) (readBuf (input.args fdGlobals.reference.wf).pkBuf) (bytesOf (readWord (input.args fdGlobals.reference.wf).msgFits)))))) = true ↔ _
  simp only [decide_eq_true_eq, Bool.and_eq_true]
  exact agave_iff_firedancer_success_and_canonical hchecks

end
end Agave.Ed25519.Bridge.CrossClientReachableSource
