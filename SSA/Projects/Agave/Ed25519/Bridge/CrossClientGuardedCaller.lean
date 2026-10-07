import SSA.Projects.Agave.Ed25519.Bridge.CrossClientParameterizedReadyUnder
import SSA.Projects.Agave.Ed25519.Proof.Verifier.LinkedColdLeavesGuarded
import SSA.Projects.Agave.Ed25519.Proof.Verifier.Bridge.ColdInputPackage

/-! Compose the prepared FD source proof with Agave's raw caller-memory
adapter. All constructor calls, coordinate readback, wrapper copies and local
global-readiness facts follow from the input/initializer records and decoder
contract plus its exact caller-block frame. Backend readiness is demanded only
after the public-key small-order check passes. `CrossClientReady` supplies the
available linked Agave implementation witnesses. -/
namespace Agave.Ed25519.Bridge
open Verifier Verifier.Execution Firedancer Firedancer.Common
open LeanMLIR.RIR (Vals EffectM)
attribute [local instance] Classical.propDecidable

section
variable (remaining : Dalek.Primitives) (dg : Dalek.Globals)
variable (compressCall : Vals [.ptr, .ptr, .bv 64] → EffectM (Vals []))
variable (compression : Agave.Ed25519.SHA512.Compression)
variable (cg : Execution.Challenge.Globals) (sg : ScalarWide.Globals)
variable (scg : SHA512Finalization.CompressionGlobals)
variable (ddg : Encoding.Decompress.Execution.Decode.Globals)
variable (dsg : Encoding.Decompress.Execution.SqrtRatio.Globals)
variable (decode : Bytes32 → Option ValidPoint) (timesEight : ValidPoint → ValidPoint)
variable (hdecode : ValidPoint.DecoderCorrect decode)
variable (serialReady avx2Ready : Dalek.BackendReadyPredicate)
variable (hleaves : ResidualLeaves.NonDecoderContractsUnder remaining dg serialReady avx2Ready
  decode timesEight)
variable (hdecodeRun : Dalek.DecompressContractUnder (Encoding.Decompress.Execution.Ready ddg dsg)
  (Encoding.Decompress.Execution.linkedProgram ddg dsg).call
  (ValidPoint.layout timesEight) (ValidPoint.shared decode))
variable (hcompress : SHA512Finalization.CompressContractUnder scg compressCall compression)
variable (hwide : ScalarWide.ExecutionObligation sg)
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
variable (hbackend : LinkedColdLeavesGuarded.BackendInputs (LinkedColdLeaves.keyPrimitives ddg dsg)
  (LinkedColdLeaves.primitives remaining compressCall sg cg ddg dsg) dg scg serialReady avx2Ready decode i initial
  (readBuf (input.args fdGlobals.reference.wf).pkBuf)
  (readBuf (input.args fdGlobals.reference.wf).sBuf)
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


include hdecode hleaves hdecodeRun hcompress hwide hinit happend hfinish hcaller hagaveGlobals hframe hbackend hdigest

/-- Prepared FD execution composes with any caller-supplied Agave leaf proofs.
All FD execution and challenge-equality witnesses are constructed. -/
theorem parameterizedCaller_guarded_cold_crossClient_observations :
    Execution.observe
      (linkedWrapper (LinkedColdLeaves.keyPrimitives ddg dsg)
        (LinkedColdLeaves.primitives remaining
          compressCall sg cg ddg dsg) dg Signature.program.call)
      i initial =
      (firedancerObserve programs fdMessage fdSize fdSignature
        fdPublicKey (firedancerFreshSha fdState) (firedancerWithSha fdState)).map
        (fun ret => decide (ret = FD_ED25519_SUCCESS) &&
          decide (CanonicalY (readBuf (input.args fdGlobals.reference.wf).sigBuf))) := by
  let a := readBuf (input.args fdGlobals.reference.wf).pkBuf
  let r := readBuf (input.args fdGlobals.reference.wf).sigBuf
  let s := readBuf (input.args fdGlobals.reference.wf).sBuf
  let message := bytesOf (readWord (input.args fdGlobals.reference.wf).msgFits)
  let sha := Agave.Ed25519.SHA512.model compression
  have hagave := LinkedColdLeavesGuarded.observe (LinkedColdLeaves.keyPrimitives ddg dsg)
    remaining dg compressCall compression cg sg scg ddg dsg decode timesEight serialReady avx2Ready
    hleaves hdecodeRun hcompress hwide i initial a r s message
    ⟨ColdInput.inputs_of_linked_decoder dg cg sg scg ddg dsg decode timesEight
      hdecodeRun i initial a r s message hcaller hagaveGlobals hframe, hbackend⟩
  obtain ⟨words, hwords, hvalue⟩ :=
    firedancerSourceReduce_correct (sha.digest (hashTranscript r a message))
  have hfd := firedancerParameterized_ready_executionRefines programs fdState fdMessage fdSize
    fdSignature fdPublicKey kbits input fdGlobals calls finishBlock hinit happend hfinish
    (sha.digest (hashTranscript r a message)) words
    (by rw [firedancerFreshSha_live]; exact hdigest) hwords
  have hscalar : firedancerReducedScalar words = messageChallenge sha.digest r a message :=
    firedancerReducedScalar_eq_hashToScalar _ words hvalue
  rw [hscalar] at hfd
  have hchallenge : (ResidualLeaves.scalarChallenge sha r a message).val = messageChallenge sha.digest r a message :=
    agave_scalarChallenge_eq_messageChallenge _ _ _ _
  have haccept : Execution.observe
      (linkedWrapper (LinkedColdLeaves.keyPrimitives ddg dsg)
        (LinkedColdLeaves.primitives remaining compressCall sg cg ddg dsg) dg Signature.program.call)
      i initial = some true ↔
      firedancerObserve programs fdMessage fdSize fdSignature fdPublicKey
        (firedancerFreshSha fdState) (firedancerWithSha fdState) = some FD_ED25519_SUCCESS ∧ CanonicalY r := by
    rw [hagave, Option.some.injEq]
    rw [verify_iff_firedancer_and_canonical_represented
      (ValidPoint.shared decode) ValidPoint.curve Fin.val (ValidPoint.shared_correct decode hdecode)
      ValidPoint.doubleBase id compress (fun _ _ _ _ _ => rfl) (fun _ => rfl)
      a r s (ResidualLeaves.scalarChallenge sha r a message) (CanonicalScalar.bound _)]
    rw [firedancerObserve_success_iff programs fdMessage fdSize fdSignature fdPublicKey
      (firedancerFreshSha fdState) (firedancerWithSha fdState) a r s _ hfd, ← hchallenge]
  obtain ⟨fdFinal, ret, hrun, _⟩ := hfd
  have hf : firedancerObserve programs fdMessage fdSize fdSignature fdPublicKey
      (firedancerFreshSha fdState) (firedancerWithSha fdState) = some ret := by
    unfold firedancerObserve
    rw [hrun]
    rfl
  rw [hagave, hf, Option.some.injEq, Option.some.injEq] at haccept
  rw [hagave, hf, Option.map_some, Option.some.injEq]
  apply Bool.eq_iff_iff.mpr
  simpa only [Bool.and_eq_true, decide_eq_true_eq] using haccept

/-- On canonical R, compare only Agave's Boolean with FD's success code. -/
theorem parameterizedCaller_guarded_cold_crossClient_of_canonical
    (hcanonical : CanonicalY (readBuf (input.args fdGlobals.reference.wf).sigBuf)) :
    Execution.observe
      (linkedWrapper (LinkedColdLeaves.keyPrimitives ddg dsg)
        (LinkedColdLeaves.primitives remaining
          compressCall sg cg ddg dsg) dg Signature.program.call)
      i initial =
      (firedancerObserve programs fdMessage fdSize fdSignature
        fdPublicKey (firedancerFreshSha fdState) (firedancerWithSha fdState)).map
        (fun ret => decide (ret = FD_ED25519_SUCCESS)) := by
  simpa only [hcanonical, decide_true, Bool.and_true] using
    parameterizedCaller_guarded_cold_crossClient_observations remaining dg compressCall compression cg sg scg ddg dsg
      decode timesEight hdecode serialReady avx2Ready hleaves hdecodeRun hcompress hwide i initial programs fdState fdMessage fdSize fdSignature
      fdPublicKey kbits input fdGlobals calls finishBlock hinit happend hfinish hcaller hagaveGlobals hframe hbackend
      hdigest

end
end Agave.Ed25519.Bridge
