import SSA.Projects.Agave.Ed25519.Bridge.CrossClientBoundedLinkedLeaves
import SSA.Projects.Agave.Ed25519.Proof.Verifier.LinkedResidualLeaves

/-!
Composition of the exact wrapper, constructors, Dalek body, challenge CFG and
byte primitives, using valid machine point representatives and bounded scalars.
The mathematical double-base and canonical compression are fixed definitions.
Outstanding machine refinements remain explicit; none is declared proved here.
-/
namespace Agave.Ed25519.Bridge
open Verifier
open Verifier.Execution
open Firedancer.Common

attribute [local instance] Classical.propDecidable

section
variable (kp : Key.Primitives) (remaining : Dalek.Primitives) (dg : Dalek.Globals)
variable (cp : Execution.Challenge.Primitives) (cg : Execution.Challenge.Globals)
variable (sha : Execution.Challenge.Sha512Model)
variable (decode : Bytes32 → Option ValidPoint) (timesEight : ValidPoint → ValidPoint)
variable (hdecode : ValidPoint.DecoderCorrect decode)
variable (hleaves : ResidualLeaves.Contracts remaining dg decode timesEight)
variable (hshaCompress : Execution.Challenge.CompressContract cp.sha512Compress sha)
variable (hshaFinalize : Execution.Challenge.ScalarFromSha512Contract cp.scalarFromSha512 sha)
variable (i : Invocation) (initial : LeanMLIR.RIR.GlobalState)
variable (a r s : Bytes32) (message : List (BitVec 8))
variable (hinput : LinkedValidPayload.Inputs kp dg cg decode timesEight i initial a r s message)
variable (fdPrograms : FiredancerShaPrograms)
variable (fdMessage : LeanMLIR.Pointer) (fdSize : BitVec 64)
variable (fdSignature fdPublicKey fdSha : LeanMLIR.Pointer) (fdState : LeanMLIR.GlobalState)
variable (fdChallenge : Nat)
variable (hfd : FiredancerExecutionRefines fdPrograms fdMessage fdSize fdSignature fdPublicKey fdSha
  fdState a r s fdChallenge)
variable (hchallenge : (ResidualLeaves.scalarChallenge sha r a message).val = fdChallenge)

include hdecode hleaves hshaCompress hshaFinalize hinput hfd hchallenge

/-- Exact observation with the canonical-R policy check exposed. Point validity,
limb bounds and scalar range are carried by the value types; negation, scalar
parsing, double-base specification and result compression need no extra laws.

The outstanding Agave implementation obligations are the nine named Dalek
leaves, the SHA compression/finalization pair and the decoder/input package.
The separate existing-FD adapter can discharge `hfd` with its legacy SHA
bindings and exact proof dependencies separately audited. -/
theorem concreteLeaves_crossClient_observations :
    Execution.observe
      (linkedWrapper kp (ResidualLeaves.primitives remaining cp cg) dg Signature.program.call)
      i initial =
      (firedancerObserve fdPrograms fdMessage fdSize fdSignature fdPublicKey fdSha fdState).map
        (fun ret => decide (ret = FD_ED25519_SUCCESS) && decide (CanonicalY r)) := by
  exact linkedLeaves_bounded_crossClient_exact_signature kp
    (ResidualLeaves.primitives remaining cp cg) dg cp cg sha Signature.program.call
    (ValidPoint.layout timesEight) (ValidPoint.shared decode) ValidPoint.curve
    (ValidPoint.shared_correct decode hdecode) ValidPoint.doubleBase id compress
    (ResidualLeaves.scalarChallenge sha)
    (ResidualLeaves.Contracts.complete remaining dg cp cg decode timesEight hleaves)
    rfl hshaCompress hshaFinalize (ResidualLeaves.scalarChallenge_encoding sha)
    rfl (fun _ _ _ _ _ => rfl) (fun _ => rfl)
    i initial a r s message fdPrograms fdMessage fdSize fdSignature fdPublicKey fdSha
    fdState fdChallenge hfd hchallenge rfl
    (LinkedValidPayload.exactSignatureInputs_of_decoder kp dg cg decode timesEight
      i initial a r s message hinput)

/-- On canonical R encodings, both defined rejection and defined acceptance
are equal. This does not claim equality of the clients' error-code values. -/
theorem concreteLeaves_crossClient_of_canonical (hcanonical : CanonicalY r) :
    Execution.observe
      (linkedWrapper kp (ResidualLeaves.primitives remaining cp cg) dg Signature.program.call)
      i initial =
      (firedancerObserve fdPrograms fdMessage fdSize fdSignature fdPublicKey fdSha fdState).map
        (fun ret => decide (ret = FD_ED25519_SUCCESS)) := by
  simpa only [hcanonical, decide_true, Bool.and_true] using
    concreteLeaves_crossClient_observations kp remaining dg cp cg sha decode timesEight
      hdecode hleaves hshaCompress hshaFinalize i initial a r s message hinput
      fdPrograms fdMessage fdSize fdSignature fdPublicKey fdSha fdState fdChallenge hfd hchallenge

end
end Agave.Ed25519.Bridge
