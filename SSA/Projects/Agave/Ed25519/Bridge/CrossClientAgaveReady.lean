import SSA.Projects.Agave.Ed25519.Bridge.AgaveReadyExecution
import SSA.Projects.Agave.Ed25519.Bridge.FiredancerScalarSourceCorrect
import SSA.Projects.Agave.Ed25519.Bridge.FiredancerParameterizedReady

/-! Cross-client execution through the closed Agave implementation. Agave has
only caller/global memory, hardware laws and bcmp as external boundaries; the
FD side retains its SHA call contracts and one actual-transcript digest equation. -/
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
variable (cg : Execution.Challenge.Globals) (sg : ScalarWide.Globals)
variable (scg : SHA512Finalization.CompressionGlobals)
variable (ddg : Encoding.Decompress.Execution.Decode.Globals)
variable (dsg : Encoding.Decompress.Execution.SqrtRatio.Globals)
variable (hbcmp : Dalek.CompareContract remaining.compareBytes)
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
variable (hserial : Ready serialGlobals d2 initial)
variable (havxGlobals : DoubleBase.ExecutionAvx2.GlobalsReady avx2Globals initial)
variable (hseparate : Separate serialGlobals d2 dg.address1)
variable (havxSeparate : avx2Globals.address2.id ≠ dg.address1.id)
variable (hdigest : firedancerDigest calls
  (some { length := 256, bytes := 0#_ }) 0
  (readBuf (input.args fdGlobals.reference.wf).sigBuf)
  (readBuf (input.args fdGlobals.reference.wf).pkBuf)
  (bytesOf (readWord (input.args fdGlobals.reference.wf).msgFits)) =
  some ((Agave.Ed25519.SHA512.model Agave.Ed25519.SHA512.Spec.compression).digest (hashTranscript
    (readBuf (input.args fdGlobals.reference.wf).sigBuf)
    (readBuf (input.args fdGlobals.reference.wf).pkBuf)
    (bytesOf (readWord (input.args fdGlobals.reference.wf).msgFits)))))


include hhardware hbcmp hserial havxGlobals hseparate havxSeparate hinit happend hfinish
  hcaller hagaveGlobals hdigest

/-- Both actual clients return defined results, with the exact canonical-R
policy difference. No Agave execution, decoder, prefix or SHA contract is assumed. -/
theorem agaveReady_crossClient_runs :
    ∃ (agaveFinal : LeanMLIR.RIR.GlobalState) (fdFinal : LeanMLIR.GlobalState)
      (b : Bool) (ret : BitVec 32),
      (Wrapper.program (AgaveReady.wrapper remaining dg hardware serialGlobals d2 panic avx2Panic avx2Globals cg sg scg ddg dsg)).call
        i.args initial = .value (Wrapper.boolResult b, agaveFinal) ∧
      firedancerRun programs fdMessage fdSize fdSignature fdPublicKey
        (firedancerFreshSha fdState) (firedancerWithSha fdState) =
        .value (.cons (.value ret) .nil, fdFinal) ∧
      b = decide (ret = FD_ED25519_SUCCESS ∧
        CanonicalY (readBuf (input.args fdGlobals.reference.wf).sigBuf)) := by
  let a := readBuf (input.args fdGlobals.reference.wf).pkBuf
  let r := readBuf (input.args fdGlobals.reference.wf).sigBuf
  let s := readBuf (input.args fdGlobals.reference.wf).sBuf
  let message := bytesOf (readWord (input.args fdGlobals.reference.wf).msgFits)
  let sha := Agave.Ed25519.SHA512.model Agave.Ed25519.SHA512.Spec.compression
  obtain ⟨agaveFinal, hagaveRun⟩ := AgaveReady.call_strict
    remaining dg hardware serialGlobals d2 panic avx2Panic avx2Globals cg sg scg ddg dsg hhardware hbcmp
    i initial a r s message hcaller hagaveGlobals hserial havxGlobals hseparate havxSeparate
  obtain ⟨words, hwords, hvalue⟩ := firedancerSourceReduce_correct (sha.digest (hashTranscript r a message))
  obtain ⟨fdFinal, ret, hfdRun, hchecks⟩ := firedancerParameterized_ready_executionRefines
    programs fdState fdMessage fdSize fdSignature fdPublicKey kbits input fdGlobals calls finishBlock
    hinit happend hfinish (sha.digest (hashTranscript r a message)) words
    (by rw [firedancerFreshSha_live]; exact hdigest) hwords
  have hscalar : firedancerReducedScalar words = messageChallenge sha.digest r a message :=
    firedancerReducedScalar_eq_hashToScalar _ words hvalue
  rw [hscalar] at hchecks
  refine ⟨agaveFinal, fdFinal, AgaveReady.strictVerify a r s message, ret, hagaveRun, hfdRun, ?_⟩
  apply Bool.eq_iff_iff.mpr
  change decide (AgaveStrictAccept a r s.toNat (messageChallenge sha.digest r a message)) = true ↔ _
  simp only [decide_eq_true_eq]
  exact agave_iff_firedancer_success_and_canonical hchecks

/-- Canonical R removes the sole acceptance-policy difference. -/
theorem agaveReady_crossClient_runs_of_canonical
    (hcanonical : CanonicalY (readBuf (input.args fdGlobals.reference.wf).sigBuf)) :
    ∃ (agaveFinal : LeanMLIR.RIR.GlobalState) (fdFinal : LeanMLIR.GlobalState)
      (b : Bool) (ret : BitVec 32),
      (Wrapper.program (AgaveReady.wrapper remaining dg hardware serialGlobals d2 panic avx2Panic avx2Globals cg sg scg ddg dsg)).call
        i.args initial = .value (Wrapper.boolResult b, agaveFinal) ∧
      firedancerRun programs fdMessage fdSize fdSignature fdPublicKey
        (firedancerFreshSha fdState) (firedancerWithSha fdState) =
        .value (.cons (.value ret) .nil, fdFinal) ∧
      b = decide (ret = FD_ED25519_SUCCESS) := by
  obtain ⟨agaveFinal, fdFinal, b, ret, ha, hf, hb⟩ :=
    agaveReady_crossClient_runs remaining dg hardware hhardware
      serialGlobals d2 panic avx2Panic avx2Globals cg sg scg ddg dsg
      hbcmp i initial programs fdState fdMessage fdSize fdSignature fdPublicKey kbits input fdGlobals
      calls finishBlock hinit happend hfinish hcaller hagaveGlobals hserial havxGlobals hseparate havxSeparate hdigest
  refine ⟨agaveFinal, fdFinal, b, ret, ha, hf, hb.trans ?_⟩
  simp only [hcanonical, and_true]

end
end Agave.Ed25519.Bridge
