import SSA.Projects.Agave.Ed25519.Bridge.CrossClientExecution
import SSA.Projects.Agave.Ed25519.Bridge.PolicyWitness

/-!
Exact acceptance-agreement domain, independent of the active backend closure.
The execution theorems retain the committed bridge's machine refinements and
invocation-local challenge equality as parameters. The mathematical witness
is at challenge 1; it does not supply a SHA-512 preimage or a concrete run.
-/
namespace Agave.Ed25519.Bridge
open Verifier Firedancer.Common

attribute [local irreducible] firedancerRefProgram firedancerRun

/-- A noncanonical y field has only nineteen possible reduced coordinates.
This bound does not mean that all nineteen coordinates decode to curve points. -/
theorem noncanonical_encoded_y_lt_nineteen {r : Bytes32} {R : CurvePoint}
    (hr : Encodes r R) (hn : ¬ CanonicalY r) : R.y.val < 19 := by
  have hbits := (r.extractLsb' 0 255).isLt
  have hlo : _root_.p ≤ (r.extractLsb' 0 255).toNat := Nat.le_of_not_gt hn
  have hy := congrArg ZMod.val hr.1
  rw [ZMod.val_natCast] at hy
  have hmod : (r.extractLsb' 0 255).toNat % _root_.p =
      (r.extractLsb' 0 255).toNat - _root_.p := by
    apply Nat.mod_eq_sub_mod hlo |>.trans
    exact Nat.mod_eq_of_lt (by unfold _root_.p at *; omega)
  rw [hmod] at hy
  unfold _root_.p at *
  omega

/-- Noncanonical encodings really can decode to non-small-order points.
The existing kernel-checked y=3 witness rules out dismissing the policy gap
as an unreachable decoder branch. Hash-challenge reachability is separate. -/
theorem noncanonical_non_small_order_encoding_exists :
    ∃ r : Bytes32, ∃ R : CurvePoint,
      Encodes r R ∧ ¬ CanonicalY r ∧ (R.x, R.y) ∉ _root_.Ed25519.lowOrder :=
  ⟨witnessR, witnessPoint, witnessR_encodes, witnessR_noncanonical,
    witnessPoint_not_lowOrder⟩

/-- Exact pure agreement domain, including noncanonical inputs both reject. -/
theorem acceptance_agreement_iff (a r : Bytes32) (s challenge : Nat) :
    (AgaveStrictAccept a r s challenge ↔ FiredancerAccept a r s challenge) ↔
      CanonicalY r ∨ ¬ FiredancerAccept a r s challenge := by
  rw [agave_iff_firedancer_and_canonical]
  tauto

section

variable {Result : Type}
  (primitives : Verifier.Execution.Wrapper.Primitives)
  (shared : Shared CurvePoint Nat) (hshared : SharedCorrect shared)
  (doubleBase : Nat → CurvePoint → Nat → Result)
  (affine : Result → CurvePoint) (compressResult : Result → Bytes32)
  (challenge : Bytes32 → Bytes32 → List (BitVec 8) → Nat)
  (environment : Verifier.Execution.Invocation → LeanMLIR.RIR.GlobalState → Prop)
  (hagave : Verifier.Execution.RefinesControlFlow primitives shared
    doubleBase compressResult challenge environment)
  (hdouble : ∀ h minusA s, h < 2 ^ 255 → s < 2 ^ 255 →
    affine (doubleBase h minusA s) = h • minusA + s • base)
  (hcompress : ∀ result, compressResult result = compress (affine result))
  (invocation : Verifier.Execution.Invocation) (agaveState : LeanMLIR.RIR.GlobalState)
  (a r s : Bytes32) (message : List (BitVec 8))
  (hinput : Verifier.Execution.Represents invocation agaveState a r s message)
  (henv : environment invocation agaveState)
  (fdPrograms : FiredancerShaPrograms)
  (fdMessage : LeanMLIR.Pointer) (fdSize : BitVec 64)
  (fdSignature fdPublicKey fdSha : LeanMLIR.Pointer) (fdState : LeanMLIR.GlobalState)
  (fdChallenge : Nat)
  (hfd : FiredancerExecutionRefines fdPrograms fdMessage fdSize fdSignature fdPublicKey fdSha
    fdState a r s fdChallenge)
  (hchallenge : challenge r a message = fdChallenge)
  (hbound : challenge r a message < 2 ^ 255)

include hshared hagave hdouble hcompress hinput henv hfd hchallenge hbound

/-- Exact returned-Boolean disagreement. The explicit refinements ensure
that Agave rejection here is `some false`, rather than undefined execution. -/
theorem crossClient_reject_success_iff_noncanonical :
    (Verifier.Execution.observe primitives invocation agaveState = some false ∧
      firedancerObserve fdPrograms fdMessage fdSize fdSignature fdPublicKey fdSha fdState =
        some FD_ED25519_SUCCESS) ↔
      firedancerObserve fdPrograms fdMessage fdSize fdSignature fdPublicKey fdSha fdState =
        some FD_ED25519_SUCCESS ∧ ¬ CanonicalY r := by
  have haccept := crossClient_observe_acceptance primitives shared hshared doubleBase affine
    compressResult challenge environment hagave hdouble hcompress invocation agaveState
    a r s message hinput henv fdPrograms fdMessage fdSize fdSignature fdPublicKey fdSha
    fdState fdChallenge hfd hchallenge hbound
  have ha := hagave invocation agaveState a r s message hinput henv
  rw [ha] at haccept ⊢
  cases hresult : Verifier.verify shared doubleBase compressResult a r s (challenge r a message) <;>
    simp_all

/-- Equality of complete success observations holds exactly when R is
canonical or Firedancer rejects. No canonical-public-key premise is added. -/
theorem crossClient_observations_agree_iff :
    (Verifier.Execution.observe primitives invocation agaveState =
      (firedancerObserve fdPrograms fdMessage fdSize fdSignature fdPublicKey fdSha fdState).map
        (fun ret => decide (ret = FD_ED25519_SUCCESS))) ↔
      CanonicalY r ∨
        firedancerObserve fdPrograms fdMessage fdSize fdSignature fdPublicKey fdSha fdState ≠
          some FD_ED25519_SUCCESS := by
  have heq := crossClient_observations_equal_with_canonical_check primitives shared hshared doubleBase affine
    compressResult challenge environment hagave hdouble hcompress invocation agaveState
    a r s message hinput henv fdPrograms fdMessage fdSize fdSignature fdPublicKey fdSha
    fdState fdChallenge hfd hchallenge hbound
  obtain ⟨fdFinal, ret, hrun, _⟩ := hfd
  have hf : firedancerObserve fdPrograms fdMessage fdSize fdSignature fdPublicKey fdSha
      fdState = some ret := by
    unfold firedancerObserve
    rw [hrun]
    rfl
  rw [heq, hf]
  by_cases hc : CanonicalY r <;> by_cases hs : ret = FD_ED25519_SUCCESS <;>
    simp [hc, hs]

/-- In particular Agave cannot accept while Firedancer rejects. -/
theorem crossClient_no_agave_only_success :
    ¬ (Verifier.Execution.observe primitives invocation agaveState = some true ∧
      firedancerObserve fdPrograms fdMessage fdSize fdSignature fdPublicKey fdSha fdState ≠
        some FD_ED25519_SUCCESS) := by
  have haccept := crossClient_observe_acceptance primitives shared hshared doubleBase affine
    compressResult challenge environment hagave hdouble hcompress invocation agaveState
    a r s message hinput henv fdPrograms fdMessage fdSize fdSignature fdPublicKey fdSha
    fdState fdChallenge hfd hchallenge hbound
  rintro ⟨ha, hf⟩
  exact hf (haccept.mp ha).1

end
end Agave.Ed25519.Bridge
