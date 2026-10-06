import SSA.Projects.Agave.Ed25519.Proof.Verifier.Execution
import SSA.Projects.Agave.Ed25519.Proof.Verifier.Acceptance

/-! The acceptance bridge applied to an explicitly supplied execution
refinement of the exact RIR wrapper. `RefinesControlFlow` is not established by
this module; the theorem retains it as an undischarged premise. -/

namespace Agave.Ed25519.Verifier.Execution

open LeanMLIR.RIR Bridge
section

theorem observe_true_iff_strict_accept {Result : Type}
    (primitives : Wrapper.Primitives) (shared : Shared CurvePoint Nat)
    (hshared : SharedCorrect shared)
    (doubleBase : Nat → CurvePoint → Nat → Result)
    (affine : Result → CurvePoint) (compressResult : Result → Bytes32)
    (challenge : Bytes32 → Bytes32 → List (BitVec 8) → Nat)
    (environment : Invocation → GlobalState → Prop)
    (hexecution : RefinesControlFlow primitives shared doubleBase compressResult challenge environment)
    (hdouble : ∀ h minusA s, h < 2 ^ 255 → s < 2 ^ 255 →
      affine (doubleBase h minusA s) = h • minusA + s • base)
    (hcompress : ∀ result, compressResult result = compress (affine result))
    (i : Invocation) (state : GlobalState) (a r s : Bytes32) (message : List (BitVec 8))
    (hinput : Represents i state a r s message) (henv : environment i state)
    (hchallenge : challenge r a message < 2 ^ 255) :
    observe primitives i state = some true ↔
      AgaveStrictAccept a r s.toNat (challenge r a message) := by
  rw [hexecution i state a r s message hinput henv, Option.some.injEq]
  exact verify_iff_strict_accept shared hshared doubleBase affine compressResult
    hdouble hcompress a r s (challenge r a message) hchallenge

theorem observe_true_iff_firedancer_and_canonical {Result : Type}
    (primitives : Wrapper.Primitives) (shared : Shared CurvePoint Nat)
    (hshared : SharedCorrect shared)
    (doubleBase : Nat → CurvePoint → Nat → Result)
    (affine : Result → CurvePoint) (compressResult : Result → Bytes32)
    (challenge : Bytes32 → Bytes32 → List (BitVec 8) → Nat)
    (environment : Invocation → GlobalState → Prop)
    (hexecution : RefinesControlFlow primitives shared doubleBase compressResult challenge environment)
    (hdouble : ∀ h minusA s, h < 2 ^ 255 → s < 2 ^ 255 →
      affine (doubleBase h minusA s) = h • minusA + s • base)
    (hcompress : ∀ result, compressResult result = compress (affine result))
    (i : Invocation) (state : GlobalState) (a r s : Bytes32) (message : List (BitVec 8))
    (hinput : Represents i state a r s message) (henv : environment i state)
    (hchallenge : challenge r a message < 2 ^ 255) :
    observe primitives i state = some true ↔
      FiredancerAccept a r s.toNat (challenge r a message) ∧ CanonicalY r := by
  rw [hexecution i state a r s message hinput henv, Option.some.injEq]
  exact verify_iff_firedancer_and_canonical shared hshared doubleBase affine compressResult
    hdouble hcompress a r s (challenge r a message) hchallenge

end
end Agave.Ed25519.Verifier.Execution
