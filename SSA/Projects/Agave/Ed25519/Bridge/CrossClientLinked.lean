import SSA.Projects.Agave.Ed25519.Bridge.CrossClientFullInput

/-!
# Cross-client comparison with all three extracted Agave bodies linked

The wrapper's key constructor and Dalek verifier calls, and Dalek's challenge
call, are the actual imported RIR bodies. The signature copy and the named
cryptographic leaf primitives remain explicit. The concrete linked execution
refinement is still a premise; this specialization discharges program linking,
not the missing memory/helper proofs.
-/

namespace Agave.Ed25519.Bridge

open Verifier Firedancer.Common

/-- Complete-input acceptance for the linked Agave wrapper, key constructor,
Dalek verifier and challenge CFG against the actual FD reference CFG. All
remaining implementation premises and the canonical-R policy are explicit. -/
theorem crossClient_linked_fullInput_observe_acceptance {Result : Type}
    (key : Verifier.Execution.Key.Primitives)
    (dalek : Verifier.Execution.Dalek.Primitives) (dg : Verifier.Execution.Dalek.Globals)
    (sha : Verifier.Execution.Challenge.Primitives) (cg : Verifier.Execution.Challenge.Globals)
    (signatureFromBytes : LeanMLIR.RIR.Vals [.ptr, .ptr] →
      LeanMLIR.RIR.EffectM (LeanMLIR.RIR.Vals []))
    (shared : Shared CurvePoint Nat) (hshared : SharedCorrect shared)
    (doubleBase : Nat → CurvePoint → Nat → Result)
    (affine : Result → CurvePoint) (compressResult : Result → Bytes32)
    (hash : HashBytes → BitVec 512) (primitiveReady : LeanMLIR.RIR.GlobalState → Prop)
    (hagave : Verifier.Execution.LinkedRefinesControlFlow key dalek dg sha cg
      signatureFromBytes shared doubleBase compressResult (messageChallenge hash) primitiveReady)
    (hdouble : ∀ h minusA s, h < 2 ^ 255 → s < 2 ^ 255 →
      affine (doubleBase h minusA s) = h • minusA + s • base)
    (hcompress : ∀ result, compressResult result = compress (affine result))
    (invocation : Verifier.Execution.Invocation) (agaveState : LeanMLIR.RIR.GlobalState)
    (a r s : Bytes32) (message : HashBytes)
    (hinput : Verifier.Execution.Represents invocation agaveState a r s message)
    (henv : Verifier.Execution.LinkedEnvironment dg cg primitiveReady invocation agaveState)
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
        dg signatureFromBytes) invocation agaveState = some true ↔
      firedancerObserve fdPrograms fdMessage fdSize fdSignature fdPublicKey fdSha fdState =
        some FD_ED25519_SUCCESS ∧ CanonicalY r := by
  exact crossClient_fullInput_observe_acceptance
    (Verifier.Execution.linkedWrapper key (Verifier.Execution.linkedChallenge dalek sha cg)
      dg signatureFromBytes)
    shared hshared doubleBase affine compressResult hash
    (Verifier.Execution.LinkedEnvironment dg cg primitiveReady) hagave hdouble hcompress
    invocation agaveState a r s message hinput henv
    fdPrograms fdMessage fdSize fdSignature fdPublicKey fdSha fdState fdChallenge hfd
    calls reduce hfdChallenge hchallenge

end Agave.Ed25519.Bridge
