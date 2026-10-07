import SSA.Projects.Agave.Ed25519.Bridge.CrossClientLinked
import SSA.Projects.Agave.Ed25519.Proof.Verifier.WrapperExecution

/-!
# Cross-client execution from local primitive contracts

The actual wrapper instruction proof discharges the former whole-wrapper
execution premise. Only its local key/signature/Dalek call and memory contracts
remain. They contain no equality about execution of the wrapper. The FD local
run/return checks, helper mathematics and SHA/scalar boundary remain explicit.
-/

namespace Agave.Ed25519.Bridge

open Verifier Firedancer.Common

attribute [local irreducible] firedancerRefProgram firedancerRun

section

variable {Result : Type}
  (primitives : Verifier.Execution.Wrapper.Primitives)
  (shared : Shared CurvePoint Nat) (hshared : SharedCorrect shared)
  (doubleBase : Nat → CurvePoint → Nat → Result)
  (affine : Result → CurvePoint) (compressResult : Result → Bytes32)
  (hdouble : ∀ h minusA s, h < 2 ^ 255 → s < 2 ^ 255 →
    affine (doubleBase h minusA s) = h • minusA + s • base)
  (hcompress : ∀ result, compressResult result = compress (affine result))
  (hash : HashBytes → BitVec 512)
  (invocation : Verifier.Execution.Invocation) (agaveState : LeanMLIR.RIR.GlobalState)
  (a r s : Bytes32) (message : HashBytes)
  (hcalls : Verifier.Execution.Wrapper.PrimitiveCalls primitives shared doubleBase
    compressResult (messageChallenge hash) invocation agaveState a r s message)
  (fdPrograms : FiredancerShaPrograms)
  (fdMessage : LeanMLIR.Pointer) (fdSize : BitVec 64)
  (fdSignature fdPublicKey fdSha : LeanMLIR.Pointer) (fdState : LeanMLIR.GlobalState)
  (fdChallenge : Nat)
  (hfd : FiredancerExecutionRefines fdPrograms fdMessage fdSize fdSignature fdPublicKey fdSha
    fdState a r s fdChallenge)
  (calls : FiredancerHashCalls) (reduce : FiredancerReduce)
  (hfdChallenge : firedancerChallenge calls reduce (fdState.mem.live? fdSha.id) fdSha.offset
    r a message = some fdChallenge)
  (hchallenge : ChallengeRefines calls reduce hash (fdState.mem.live? fdSha.id) fdSha.offset
    r a message)

include hshared hdouble hcompress hcalls hfd hfdChallenge hchallenge

/-- Exact returned-Boolean equality for full message inputs, proved from the
wrapper's individual primitive calls rather than a whole-wrapper refinement.
Undefined execution stays `none`; the supplied call contracts prove that the
actual wrapper returns. No universal Agave execution premise is needed. -/
theorem crossClient_fullInput_observations_of_primitive_calls :
    Verifier.Execution.observe primitives invocation agaveState =
      (firedancerObserve fdPrograms fdMessage fdSize fdSignature fdPublicKey fdSha fdState).map
        (fun ret => decide (ret = FD_ED25519_SUCCESS) && decide (CanonicalY r)) := by
  have ha := Verifier.Execution.Wrapper.observe_of_primitive_calls primitives shared
    doubleBase compressResult (messageChallenge hash) invocation agaveState a r s message hcalls
  have hsame : messageChallenge hash r a message = fdChallenge :=
    Option.some.inj (hchallenge.symm.trans hfdChallenge)
  have haccept : verify shared doubleBase compressResult a r s (messageChallenge hash r a message) =
      true ↔ firedancerObserve fdPrograms fdMessage fdSize fdSignature fdPublicKey fdSha fdState =
        some FD_ED25519_SUCCESS ∧ CanonicalY r := by
    rw [firedancerObserve_success_iff fdPrograms fdMessage fdSize fdSignature fdPublicKey fdSha
      fdState a r s fdChallenge hfd, ← hsame]
    exact verify_iff_firedancer_and_canonical shared hshared doubleBase affine compressResult
      hdouble hcompress a r s (messageChallenge hash r a message)
      (hashToScalar_lt_255 (hash (hashTranscript r a message)))
  obtain ⟨fdFinal, ret, hrun, _⟩ := hfd
  have hf : firedancerObserve fdPrograms fdMessage fdSize fdSignature fdPublicKey fdSha
      fdState = some ret := by
    unfold firedancerObserve
    rw [hrun]
    rfl
  rw [hf, Option.some.injEq] at haccept
  rw [ha, hf, Option.map_some, Option.some.injEq]
  apply Bool.eq_iff_iff.mpr
  simpa only [Bool.and_eq_true, decide_eq_true_eq] using haccept

/-- On canonical R the two actual runs return the same acceptance Boolean.
The input public key, scalar and message remain unrestricted. -/
theorem crossClient_fullInput_observations_of_primitive_calls_of_canonical
    (hcanonical : CanonicalY r) :
    Verifier.Execution.observe primitives invocation agaveState =
      (firedancerObserve fdPrograms fdMessage fdSize fdSignature fdPublicKey fdSha fdState).map
        (fun ret => decide (ret = FD_ED25519_SUCCESS)) := by
  have h := crossClient_fullInput_observations_of_primitive_calls primitives shared hshared
    doubleBase affine compressResult hdouble hcompress hash invocation agaveState a r s message
    hcalls fdPrograms fdMessage fdSize fdSignature fdPublicKey fdSha fdState fdChallenge hfd
    calls reduce hfdChallenge hchallenge
  simpa only [hcanonical, decide_true, Bool.and_true] using h

end

/-- The same strongest observation equality with the actual extracted key,
Dalek and challenge CFGs linked into the wrapper. The remaining local primitive
contracts must now be established for those exact bodies and their state. -/
theorem crossClient_linked_fullInput_observations_of_primitive_calls {Result : Type}
    (key : Verifier.Execution.Key.Primitives)
    (dalek : Verifier.Execution.Dalek.Primitives) (dg : Verifier.Execution.Dalek.Globals)
    (sha : Verifier.Execution.Challenge.Primitives) (cg : Verifier.Execution.Challenge.Globals)
    (signatureFromBytes : LeanMLIR.RIR.Vals [.ptr, .ptr] →
      LeanMLIR.RIR.EffectM (LeanMLIR.RIR.Vals []))
    (shared : Shared CurvePoint Nat) (hshared : SharedCorrect shared)
    (doubleBase : Nat → CurvePoint → Nat → Result)
    (affine : Result → CurvePoint) (compressResult : Result → Bytes32)
    (hdouble : ∀ h minusA s, h < 2 ^ 255 → s < 2 ^ 255 →
      affine (doubleBase h minusA s) = h • minusA + s • base)
    (hcompress : ∀ result, compressResult result = compress (affine result))
    (hash : HashBytes → BitVec 512)
    (invocation : Verifier.Execution.Invocation) (agaveState : LeanMLIR.RIR.GlobalState)
    (a r s : Bytes32) (message : HashBytes)
    (hcalls : Verifier.Execution.Wrapper.PrimitiveCalls
      (Verifier.Execution.linkedWrapper key (Verifier.Execution.linkedChallenge dalek sha cg)
        dg signatureFromBytes)
      shared doubleBase compressResult (messageChallenge hash) invocation agaveState a r s message)
    (fdPrograms : FiredancerShaPrograms)
    (fdMessage : LeanMLIR.Pointer) (fdSize : BitVec 64)
    (fdSignature fdPublicKey fdSha : LeanMLIR.Pointer) (fdState : LeanMLIR.GlobalState)
    (fdChallenge : Nat)
    (hfd : FiredancerExecutionRefines fdPrograms fdMessage fdSize fdSignature fdPublicKey fdSha
      fdState a r s fdChallenge)
    (calls : FiredancerHashCalls) (reduce : FiredancerReduce)
    (hfdChallenge : firedancerChallenge calls reduce (fdState.mem.live? fdSha.id) fdSha.offset
      r a message = some fdChallenge)
    (hchallenge : ChallengeRefines calls reduce hash (fdState.mem.live? fdSha.id) fdSha.offset
      r a message) :
    Verifier.Execution.observe
      (Verifier.Execution.linkedWrapper key (Verifier.Execution.linkedChallenge dalek sha cg)
        dg signatureFromBytes) invocation agaveState =
      (firedancerObserve fdPrograms fdMessage fdSize fdSignature fdPublicKey fdSha fdState).map
        (fun ret => decide (ret = FD_ED25519_SUCCESS) && decide (CanonicalY r)) := by
  exact crossClient_fullInput_observations_of_primitive_calls
    (Verifier.Execution.linkedWrapper key (Verifier.Execution.linkedChallenge dalek sha cg)
      dg signatureFromBytes)
    shared hshared doubleBase affine compressResult hdouble hcompress hash
    invocation agaveState a r s message hcalls
    fdPrograms fdMessage fdSize fdSignature fdPublicKey fdSha fdState fdChallenge hfd
    calls reduce hfdChallenge hchallenge

end Agave.Ed25519.Bridge
