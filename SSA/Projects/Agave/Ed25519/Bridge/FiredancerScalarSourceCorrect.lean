import SSA.Projects.Agave.Ed25519.Bridge.FiredancerScalarUniversal
import SSA.Projects.Agave.Ed25519.Bridge.FiredancerScalarInvocation

/-! Eliminate the local source-reducer termination and arithmetic premises
using the checked proof for every 512-bit digest. -/
namespace Agave.Ed25519.Bridge
open Firedancer Firedancer.Common

theorem firedancerSourceReduce_correct (digest : BitVec 512) :
    ∃ words, firedancerSourceReduce digest = some words ∧
      (packWords words).toNat = hashToScalar digest := by
  obtain ⟨words, hwords⟩ := firedancerSourceReduce_returns_of_certificate digest
    (firedancerScalarCanonical digest)
  exact ⟨words, hwords, firedancerSourceReduce_value_of_certificate digest
    (firedancerScalarCanonical digest) words hwords⟩

/-- Any deterministic adapter satisfying the actual reducer call specification
inherits the universal arithmetic result; no adapter-identification premise is needed. -/
theorem firedancerReductionValueCorrect_of_call
    (reduce : FiredancerReduce) (hcall : ScalarReduceBy reduce) :
    Challenge.ReductionValueCorrect reduce := by
  intro digest words hwords
  have heq := (ScalarArithmetic.packed_eq hcall ScalarArithmetic.sourceReduce_by digest).trans
    (firedancerScalarCanonical digest)
  rw [hwords] at heq
  have hbytes : packWords words = Challenge.reducedBytes digest := Option.some.inj heq
  rw [hbytes, Challenge.reducedBytes_toNat]

/-- The stored invocation already contains its scalar call contract. -/
theorem FiredancerProofInvocation.challenge_eq_of_proved_reducer
    (v : FiredancerProofInvocation) (hash : HashBytes → BitVec 512)
    (hhash : Challenge.DigestBy ⟨v.init, v.append, v.finish⟩
      (v.state.mem.live? v.sha.id) v.sha.offset hash) :
    v.challenge = messageChallenge hash v.r v.a v.messageBytes :=
  v.challenge_eq_of_digestBy hash hhash
    (firedancerReductionValueCorrect_of_call v.reduce v.environment.scalarReduce)

end Agave.Ed25519.Bridge
