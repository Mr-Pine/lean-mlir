import SSA.Projects.Agave.Ed25519.Bridge.CrossClientExecution
import SSA.Projects.Agave.Ed25519.Bridge.HashChallenge

/-!
# Complete byte-input execution bridge with explicit cryptographic boundary

The RIR and SLLVM execution obligations are separate from the local composed
SHA/scalar obligation. `ChallengeRefines` supplies the same scalar on the
original R || A || message transcript and the range required by Agave's
backend contract. It does not assert correctness of either SHA implementation.
-/

namespace Agave.Ed25519.Bridge

open Verifier Firedancer.Common

/-- Complete-input equivalence of the actual program observations, with the
canonical-R policy difference retained. All remaining execution/cryptographic
obligations are named hypotheses and no global hash equality is needed. -/
theorem crossClient_fullInput_observe_acceptance {Result : Type}
    (primitives : Verifier.Execution.Wrapper.Primitives)
    (shared : Shared CurvePoint Nat) (hshared : SharedCorrect shared)
    (doubleBase : Nat → CurvePoint → Nat → Result)
    (affine : Result → CurvePoint) (compressResult : Result → Bytes32)
    (hash : HashBytes → BitVec 512)
    (environment : Verifier.Execution.Invocation → LeanMLIR.RIR.GlobalState → Prop)
    (hagave : Verifier.Execution.RefinesControlFlow primitives shared
      doubleBase compressResult (messageChallenge hash) environment)
    (hdouble : ∀ h minusA s, h < 2 ^ 255 → s < 2 ^ 255 →
      affine (doubleBase h minusA s) = h • minusA + s • base)
    (hcompress : ∀ result, compressResult result = compress (affine result))
    (invocation : Verifier.Execution.Invocation) (agaveState : LeanMLIR.RIR.GlobalState)
    (a r s : Bytes32) (message : HashBytes)
    (hinput : Verifier.Execution.Represents invocation agaveState a r s message)
    (henv : environment invocation agaveState)
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
    Verifier.Execution.observe primitives invocation agaveState = some true ↔
      firedancerObserve fdPrograms fdMessage fdSize fdSignature fdPublicKey fdSha fdState =
        some FD_ED25519_SUCCESS ∧ CanonicalY r := by
  have hsame : messageChallenge hash r a message = fdChallenge :=
    Option.some.inj (hchallenge.symm.trans hfdChallenge)
  exact crossClient_observe_acceptance primitives shared hshared doubleBase affine compressResult
    (messageChallenge hash) environment hagave hdouble hcompress invocation agaveState
    a r s message hinput henv fdPrograms fdMessage fdSize fdSignature fdPublicKey fdSha fdState
    fdChallenge hfd hsame (hashToScalar_lt_255 (hash (hashTranscript r a message)))

end Agave.Ed25519.Bridge
