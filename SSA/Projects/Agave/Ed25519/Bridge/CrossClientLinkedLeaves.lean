import SSA.Projects.Agave.Ed25519.Proof.Verifier.LinkedLeafExecution
import SSA.Projects.Agave.Ed25519.Bridge.FiredancerProgram
import SSA.Projects.Agave.Ed25519.Proof.Verifier.Acceptance

/-!
# Clean cross-client endpoint with Agave execution derived from leaves

The Agave wrapper, key constructor, Dalek verifier and challenge are the exact
RIR bodies. Their execution-refinement premise is replaced by named leaf
contracts and explicit caller/intermediate memory. The Firedancer endpoint is
the clean SHA-parameterized reference CFG; its execution refinement remains an
explicit assumption. Canonical R is an observable policy distinction.

This legacy `Nat` specialization is only a conditional composition theorem.
Its usual `BitVec.ofNat 256` scalar layout cannot instantiate the bidirectional
`ScalarParseContract` on an unbounded domain because encodings alias.
Use the bounded-scalar replacement for an inhabitable concrete endpoint.
-/
namespace Agave.Ed25519.Bridge
open Verifier
open Verifier.Execution
open Firedancer.Common

attribute [local irreducible] firedancerRefProgram firedancerRun

local instance (r : Bytes32) : Decidable (CanonicalY r) := by
  unfold CanonicalY
  infer_instance

section
variable {Result : Type}
variable (kp : Key.Primitives) (dp : Dalek.Primitives) (dg : Dalek.Globals)
variable (cp : Execution.Challenge.Primitives) (cg : Execution.Challenge.Globals) (sha : Execution.Challenge.Sha512Model)
variable (signatureFromBytes : LeanMLIR.RIR.Vals [.ptr, .ptr] → LeanMLIR.RIR.EffectM (LeanMLIR.RIR.Vals []))
variable (layout : Dalek.Layout CurvePoint Nat Result) (shared : Shared CurvePoint Nat)
variable (hshared : SharedCorrect shared)
variable (doubleBase : Nat → CurvePoint → Nat → Result)
variable (affine : Result → CurvePoint) (compressResult : Result → Bytes32)
variable (challenge : Bytes32 → Bytes32 → List (BitVec 8) → Nat)
variable (contracts : Dalek.LeafContracts dp dg layout shared doubleBase compressResult)
variable (hlink : dp.challengeScalar = (Execution.Challenge.program cp cg).call)
variable (hcompress : Execution.Challenge.CompressContract cp.sha512Compress sha)
variable (hscalar : Execution.Challenge.ScalarFromSha512Contract cp.scalarFromSha512 sha)
variable (hencoding : ∀ r a msg, layout.scalar (challenge r a msg) =
  Execution.Challenge.digestScalarBytes (sha.digest (Execution.Challenge.transcript r a msg)))
variable (hidentity : layout.identity = Dalek.identityBytes)
variable (hdouble : ∀ h minusA s, h < 2 ^ 255 → s < 2 ^ 255 →
  affine (doubleBase h minusA s) = h • minusA + s • base)
variable (hresultCompress : ∀ result, compressResult result = compress (affine result))
variable (i : Invocation) (initial : LeanMLIR.RIR.GlobalState)
variable (a r s : Bytes32) (message : List (BitVec 8))
variable (hinput : LinkedLeaves.Inputs kp signatureFromBytes dg cg layout shared i initial a r s message)
variable (fdPrograms : FiredancerShaPrograms)
variable (fdMessage : LeanMLIR.Pointer) (fdSize : BitVec 64)
variable (fdSignature fdPublicKey fdSha : LeanMLIR.Pointer) (fdState : LeanMLIR.GlobalState)
variable (fdChallenge : Nat)
variable (hfd : FiredancerExecutionRefines fdPrograms fdMessage fdSize fdSignature fdPublicKey fdSha
  fdState a r s fdChallenge)
variable (hchallenge : challenge r a message = fdChallenge)
variable (hbound : challenge r a message < 2 ^ 255)

include hshared contracts hlink hcompress hscalar hencoding hidentity
  hdouble hresultCompress hinput hfd hchallenge hbound

/-- Acceptance for the exact linked Agave bodies and the clean Firedancer CFG.
No Agave whole-program execution refinement is an assumed premise. -/
theorem linkedLeaves_crossClient_acceptance :
    Execution.observe (linkedWrapper kp dp dg signatureFromBytes) i initial = some true ↔
      firedancerObserve fdPrograms fdMessage fdSize fdSignature fdPublicKey fdSha fdState =
        some FD_ED25519_SUCCESS ∧ CanonicalY r := by
  rw [LinkedLeaves.observe kp dp dg cp cg sha signatureFromBytes layout shared doubleBase
    compressResult challenge contracts hlink hcompress hscalar hencoding hidentity
    i initial a r s message hinput, Option.some.injEq]
  rw [verify_iff_firedancer_and_canonical shared hshared doubleBase affine compressResult
    hdouble hresultCompress a r s (challenge r a message) hbound]
  rw [firedancerObserve_success_iff fdPrograms fdMessage fdSize fdSignature fdPublicKey fdSha
    fdState a r s fdChallenge hfd, ← hchallenge]

/-- Equality includes defined rejection, with the canonical-R policy exposed
as the exact additional Boolean check on Firedancer's return code. -/
theorem linkedLeaves_crossClient_observations :
    Execution.observe (linkedWrapper kp dp dg signatureFromBytes) i initial =
      (firedancerObserve fdPrograms fdMessage fdSize fdSignature fdPublicKey fdSha fdState).map
        (fun ret => decide (ret = FD_ED25519_SUCCESS) && decide (CanonicalY r)) := by
  have haccept := linkedLeaves_crossClient_acceptance kp dp dg cp cg sha signatureFromBytes
    layout shared hshared doubleBase affine compressResult challenge contracts hlink hcompress
    hscalar hencoding hidentity hdouble hresultCompress i initial a r s message hinput
    fdPrograms fdMessage fdSize fdSignature fdPublicKey fdSha fdState fdChallenge hfd hchallenge hbound
  have ha := LinkedLeaves.observe kp dp dg cp cg sha signatureFromBytes layout shared doubleBase
    compressResult challenge contracts hlink hcompress hscalar hencoding hidentity
    i initial a r s message hinput
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

omit hinput in
/-- The complete Boolean comparison with the signature constructor also linked
to its exact imported body. Per-input call assumptions now name only the
public-key decoder; the copy/Dalek post-state relation stays explicit. -/
theorem linkedLeaves_crossClient_exact_signature
    (hsignatureLink : signatureFromBytes = Signature.program.call)
    (hmemory : LinkedLeaves.ExactSignatureInputs kp dg cg layout shared i initial a r s message) :
    Execution.observe (linkedWrapper kp dp dg signatureFromBytes) i initial =
      (firedancerObserve fdPrograms fdMessage fdSize fdSignature fdPublicKey fdSha fdState).map
        (fun ret => decide (ret = FD_ED25519_SUCCESS) && decide (CanonicalY r)) := by
  exact linkedLeaves_crossClient_observations kp dp dg cp cg sha signatureFromBytes
    layout shared hshared doubleBase affine compressResult challenge contracts hlink hcompress
    hscalar hencoding hidentity hdouble hresultCompress i initial a r s message
    (LinkedLeaves.inputs_of_exact_signature signatureFromBytes hsignatureLink hmemory)
    fdPrograms fdMessage fdSize fdSignature fdPublicKey fdSha fdState fdChallenge hfd hchallenge hbound

end
end Agave.Ed25519.Bridge
