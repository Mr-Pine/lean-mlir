import SSA.Projects.Agave.Ed25519.Proof.Verifier.Acceptance
import SSA.Projects.Agave.Ed25519.Bridge.FullInput

/-!
# Strict verifier control flow on complete message inputs

This composes the already explicit helper/backend contracts with the concrete
R || A || msg hash transcript and the existing Firedancer digest/reduction
interface. The digest model remains a parameter; `ChallengeRefines` is the
local cryptographic refinement not established by the pre-existing specs.
These theorems do not claim conformance of extracted RIR execution.
-/

namespace Agave.Ed25519.Verifier

open Bridge LeanMLIR SLLVM

/-- Agave's pure byte-input control-flow model supplied with the intended
hash-to-scalar specification on the original R and public-key bytes. -/
def verifyMessage {Result : Type} (shared : Shared CurvePoint Nat)
    (doubleBase : Nat → CurvePoint → Nat → Result) (compressResult : Result → Bytes32)
    (hash : HashBytes → BitVec 512) (a r s : Bytes32) (msg : HashBytes) : Bool :=
  verify shared doubleBase compressResult a r s (messageChallenge hash r a msg)

/-- Full input bridge: pure strict control flow to the existing Firedancer
digest/reduction pipeline and its acceptance equation. All implementation
refinements remain explicit hypotheses. -/
theorem verifyMessage_iff_firedancerFull_and_canonical {Result : Type}
    (shared : Shared CurvePoint Nat) (hshared : SharedCorrect shared)
    (doubleBase : Nat → CurvePoint → Nat → Result)
    (affine : Result → CurvePoint) (compressResult : Result → Bytes32)
    (hdouble : ∀ h minusA s, h < 2 ^ 255 → s < 2 ^ 255 →
      affine (doubleBase h minusA s) = h • minusA + s • base)
    (hcompress : ∀ result, compressResult result = compress (affine result))
    (calls : FiredancerHashCalls) (reduce : FiredancerReduce)
    (hash : HashBytes → BitVec 512) (blk : Option LiveBlock) (off : BitVec 64)
    (a r s : Bytes32) (msg : HashBytes)
    (hchallenge : ChallengeRefines calls reduce hash blk off r a msg) :
    verifyMessage shared doubleBase compressResult hash a r s msg = true ↔
      FiredancerFullAccept calls reduce blk off a r s msg ∧ CanonicalY r := by
  unfold verifyMessage
  have hh : messageChallenge hash r a msg < 2 ^ 255 :=
    hashToScalar_lt_255 (hash (hashTranscript r a msg))
  rw [verify_iff_strict_accept shared hshared doubleBase affine compressResult hdouble hcompress
    a r s (messageChallenge hash r a msg) hh]
  exact agaveFull_iff_firedancerFull_and_canonical
    calls reduce hash blk off a r s msg hchallenge

end Agave.Ed25519.Verifier
