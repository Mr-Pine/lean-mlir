import SSA.Projects.Agave.Ed25519.Proof.Verifier.LinkedColdLeavesUnder
import SSA.Projects.Agave.Ed25519.Bridge.FiredancerProgram

/-! Cross-client observation with the actual imported finalizer linked and
its Montgomery-table readiness scoped to the current invocation. -/
namespace Agave.Ed25519.Bridge
open Verifier Verifier.Execution Firedancer.Common
open LeanMLIR.RIR (Vals EffectM)
attribute [local instance] Classical.propDecidable
attribute [local irreducible] firedancerRefProgram firedancerRun

section
variable (kp : Key.Primitives) (remaining : Dalek.Primitives) (dg : Dalek.Globals)
variable (compressCall : Vals [.ptr, .ptr, .bv 64] → EffectM (Vals []))
variable (compression : Agave.Ed25519.SHA512.Compression)
variable (cg : Execution.Challenge.Globals) (sg : ScalarWide.Globals)
variable (scg : SHA512Finalization.CompressionGlobals)
variable (ddg : Encoding.Decompress.Execution.Decode.Globals)
variable (dsg : Encoding.Decompress.Execution.SqrtRatio.Globals)
variable (decode : Bytes32 → Option ValidPoint) (timesEight : ValidPoint → ValidPoint)
variable (hdecode : ValidPoint.DecoderCorrect decode)
variable (serialReady avx2Ready : Dalek.BackendReadyPredicate)
variable (hleaves : ResidualLeaves.NonDecoderContractsUnder remaining dg serialReady avx2Ready decode timesEight)
variable (hdecodeRun : Dalek.DecompressContractUnder (Encoding.Decompress.Execution.Ready ddg dsg)
  (Encoding.Decompress.Execution.linkedProgram ddg dsg).call
  (ValidPoint.layout timesEight) (ValidPoint.shared decode))
variable (hcompress : SHA512Finalization.CompressContractUnder scg compressCall compression)
variable (hwide : ScalarWide.ExecutionObligation sg)
variable (i : Invocation) (initial : LeanMLIR.RIR.GlobalState)
variable (a r s : Bytes32) (message : List (BitVec 8))
variable (hinput : LinkedColdLeavesUnder.Inputs kp (LinkedColdLeaves.primitives remaining compressCall sg cg ddg dsg) dg cg sg scg ddg dsg serialReady avx2Ready decode timesEight i initial a r s message)
variable (fdPrograms : FiredancerShaPrograms)
variable (fdMessage : LeanMLIR.Pointer) (fdSize : BitVec 64)
variable (fdSignature fdPublicKey fdSha : LeanMLIR.Pointer) (fdState : LeanMLIR.GlobalState)
variable (fdChallenge : Nat)
variable (hfd : FiredancerExecutionRefines fdPrograms fdMessage fdSize fdSignature fdPublicKey fdSha
  fdState a r s fdChallenge)
variable (hchallenge : (ResidualLeaves.scalarChallenge
  (Agave.Ed25519.SHA512.model compression) r a message).val = fdChallenge)

include hdecode hleaves hdecodeRun hcompress hwide hinput hfd hchallenge

theorem contextual_cold_crossClient_acceptance :
    Execution.observe
      (linkedWrapper kp (LinkedColdLeavesUnder.primitives remaining compressCall sg cg ddg dsg)
        dg Signature.program.call) i initial = some true ↔
      firedancerObserve fdPrograms fdMessage fdSize fdSignature fdPublicKey fdSha fdState =
        some FD_ED25519_SUCCESS ∧ CanonicalY r := by
  rw [LinkedColdLeavesUnder.observe kp remaining dg compressCall compression cg sg scg ddg dsg decode
    timesEight serialReady avx2Ready hleaves hdecodeRun hcompress hwide i initial a r s message hinput, Option.some.injEq]
  rw [verify_iff_firedancer_and_canonical_represented
    (ValidPoint.shared decode) ValidPoint.curve Fin.val (ValidPoint.shared_correct decode hdecode)
    ValidPoint.doubleBase id compress (fun _ _ _ _ _ => rfl) (fun _ => rfl)
    a r s (ResidualLeaves.scalarChallenge (Agave.Ed25519.SHA512.model compression) r a message)
    (CanonicalScalar.bound _)]
  rw [firedancerObserve_success_iff fdPrograms fdMessage fdSize fdSignature fdPublicKey fdSha
    fdState a r s fdChallenge hfd, ← hchallenge]

/-- The finalizer is an imported body, not a universal semantic premise.
Only SHA compression and the actual wide reducer under initialized globals
remain on the hashing side of this composed observation theorem. -/
theorem contextual_cold_crossClient_observations :
    Execution.observe
      (linkedWrapper kp (LinkedColdLeavesUnder.primitives remaining compressCall sg cg ddg dsg)
        dg Signature.program.call) i initial =
      (firedancerObserve fdPrograms fdMessage fdSize fdSignature fdPublicKey fdSha fdState).map
        (fun ret => decide (ret = FD_ED25519_SUCCESS) && decide (CanonicalY r)) := by
  have haccept := contextual_cold_crossClient_acceptance kp remaining dg compressCall compression
    cg sg scg ddg dsg decode timesEight hdecode serialReady avx2Ready hleaves hdecodeRun hcompress hwide i initial a r s message hinput
    fdPrograms fdMessage fdSize fdSignature fdPublicKey fdSha fdState fdChallenge hfd hchallenge
  have ha := LinkedColdLeavesUnder.observe kp remaining dg compressCall compression cg sg scg ddg dsg decode
    timesEight serialReady avx2Ready hleaves hdecodeRun hcompress hwide i initial a r s message hinput
  obtain ⟨fdFinal, ret, hrun, _⟩ := hfd
  have hf : firedancerObserve fdPrograms fdMessage fdSize fdSignature fdPublicKey fdSha
      fdState = some ret := by
    unfold firedancerObserve
    rw [hrun]
    rfl
  rw [ha, hf, Option.some.injEq, Option.some.injEq] at haccept
  rw [ha, hf, Option.map_some, Option.some.injEq]
  apply Bool.eq_iff_iff.mpr
  simpa only [Bool.and_eq_true, decide_eq_true_eq] using haccept

theorem contextual_cold_crossClient_of_canonical (hcanonical : CanonicalY r) :
    Execution.observe
      (linkedWrapper kp (LinkedColdLeavesUnder.primitives remaining compressCall sg cg ddg dsg)
        dg Signature.program.call) i initial =
      (firedancerObserve fdPrograms fdMessage fdSize fdSignature fdPublicKey fdSha fdState).map
        (fun ret => decide (ret = FD_ED25519_SUCCESS)) := by
  simpa only [hcanonical, decide_true, Bool.and_true] using
    contextual_cold_crossClient_observations kp remaining dg compressCall compression cg sg scg ddg dsg decode
      timesEight hdecode serialReady avx2Ready hleaves hdecodeRun hcompress hwide i initial a r s message hinput
      fdPrograms fdMessage fdSize fdSignature fdPublicKey fdSha fdState fdChallenge hfd hchallenge

end
end Agave.Ed25519.Bridge
