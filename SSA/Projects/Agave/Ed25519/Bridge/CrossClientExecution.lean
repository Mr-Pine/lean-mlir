import SSA.Projects.Agave.Ed25519.Bridge.FiredancerProgram
import SSA.Projects.Agave.Ed25519.Proof.Verifier.ExecutionAcceptance

/-!
# Cross-client observations of the actual verifier programs

The Agave side is the extracted RIR wrapper; the Firedancer side is the
existing SLLVM reference CFG with explicit SHA program parameters. Both
execution refinements are retained as hypotheses. The FD refinement contains
termination and the existing return-path checks, not acceptance equivalence.

The clients' consumed challenge scalars need only agree for this invocation.
No global SHA equivalence, canonical public key, or acceptance hypothesis is
required. Error-code equality is not asserted. Poison remains `none` on both
sides and is excluded only by the explicit execution-refinement obligations.
-/

namespace Agave.Ed25519.Bridge

open Verifier
open Firedancer.Common

attribute [local irreducible] firedancerRefProgram firedancerRun

/-- The canonical-R policy check is the ordinary unsigned-coordinate bound. -/
instance canonicalYDecidable (r : BitVec 256) : Decidable (CanonicalY r) := by
  unfold CanonicalY
  infer_instance

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

/-- The precise acceptance relation between the two actual execution
observations, conditional on their transparent execution and local scalar
refinements. R canonicality is a conclusion of Agave acceptance. -/
theorem crossClient_observe_acceptance :
    Verifier.Execution.observe primitives invocation agaveState = some true ↔
      firedancerObserve fdPrograms fdMessage fdSize fdSignature fdPublicKey fdSha fdState =
        some FD_ED25519_SUCCESS ∧ CanonicalY r := by
  rw [Verifier.Execution.observe_true_iff_strict_accept primitives shared hshared doubleBase
    affine compressResult challenge environment hagave hdouble hcompress
    invocation agaveState a r s message hinput henv hbound]
  rw [firedancerObserve_success_iff fdPrograms fdMessage fdSize fdSignature fdPublicKey fdSha
    fdState a r s fdChallenge hfd, ← hchallenge]
  exact agave_iff_firedancer_and_canonical a r s.toNat (challenge r a message)

/-- Equality of the complete Boolean observations, including rejection. The
canonical-R policy is an explicit Boolean check on the FD result. Neither
side's undefined execution is converted into rejection. -/
theorem crossClient_observations_equal_with_canonical_check :
    Verifier.Execution.observe primitives invocation agaveState =
      (firedancerObserve fdPrograms fdMessage fdSize fdSignature fdPublicKey fdSha fdState).map
        (fun ret => decide (ret = FD_ED25519_SUCCESS) && decide (CanonicalY r)) := by
  have haccept := crossClient_observe_acceptance primitives shared hshared doubleBase affine
    compressResult challenge environment hagave hdouble hcompress invocation agaveState
    a r s message hinput henv fdPrograms fdMessage fdSize fdSignature fdPublicKey fdSha
    fdState fdChallenge hfd hchallenge hbound
  have ha := hagave invocation agaveState a r s message hinput henv
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

/-- Complete returned-Boolean equality on canonical R. Definedness comes
from the two execution refinements, without a new termination premise. -/
theorem crossClient_observations_equal_of_canonical (hcanonical : CanonicalY r) :
    Verifier.Execution.observe primitives invocation agaveState =
      (firedancerObserve fdPrograms fdMessage fdSize fdSignature fdPublicKey fdSha fdState).map
        (fun ret => decide (ret = FD_ED25519_SUCCESS)) := by
  have h := crossClient_observations_equal_with_canonical_check primitives shared hshared
    doubleBase affine compressResult challenge environment hagave hdouble hcompress
    invocation agaveState a r s message hinput henv fdPrograms fdMessage fdSize
    fdSignature fdPublicKey fdSha fdState fdChallenge hfd hchallenge hbound
  simpa only [hcanonical, decide_true, Bool.and_true] using h

/-- Equal acceptance on canonical R; the public key and signature scalar
remain arbitrary bytes. -/
theorem crossClient_observe_acceptance_of_canonical (hcanonical : CanonicalY r) :
    Verifier.Execution.observe primitives invocation agaveState = some true ↔
      firedancerObserve fdPrograms fdMessage fdSize fdSignature fdPublicKey fdSha fdState =
        some FD_ED25519_SUCCESS := by
  rw [crossClient_observe_acceptance primitives shared hshared doubleBase affine compressResult
    challenge environment hagave hdouble hcompress invocation agaveState a r s message hinput henv
    fdPrograms fdMessage fdSize fdSignature fdPublicKey fdSha fdState fdChallenge hfd
    hchallenge hbound, and_iff_left hcanonical]

/-- Without restricting R in advance, the only possible acceptance difference
is a Firedancer success with noncanonical R. This does not assert that a SHA
preimage for such an input exists. -/
theorem crossClient_firedancer_only_iff_noncanonical :
    (firedancerObserve fdPrograms fdMessage fdSize fdSignature fdPublicKey fdSha fdState =
        some FD_ED25519_SUCCESS ∧
      Verifier.Execution.observe primitives invocation agaveState ≠ some true) ↔
      firedancerObserve fdPrograms fdMessage fdSize fdSignature fdPublicKey fdSha fdState =
        some FD_ED25519_SUCCESS ∧ ¬ CanonicalY r := by
  simp only [ne_eq, crossClient_observe_acceptance primitives shared hshared doubleBase affine compressResult
    challenge environment hagave hdouble hcompress invocation agaveState a r s message hinput henv
    fdPrograms fdMessage fdSize fdSignature fdPublicKey fdSha fdState fdChallenge hfd
    hchallenge hbound]
  tauto

end

end Agave.Ed25519.Bridge
