import SSA.Projects.Agave.Ed25519.Bridge.HashChallenge

/-!
# Full-input Agave / Firedancer acceptance bridge

The inputs here are arbitrary public-key bytes, both signature halves, and
message bytes. The Agave side uses an explicit digest model on R || A || msg
followed by mathematical reduction modulo the subgroup order. The Firedancer
side uses the existing state-dependent `ed25519Digest` and scalar-reduction
interfaces, including their possible failure to return and 255-bit masking.

The only cryptographic hypothesis is `ChallengeRefines` for this invocation.
No SHA-512 or scalar-reduction correctness is supplied by the existing
Firedancer specs; proving it requires an additional implementation refinement.
The acceptance predicates still need their separate execution refinements.
-/

namespace Agave.Ed25519.Bridge

open LeanMLIR SLLVM

/-- Strict Agave acceptance for complete byte inputs, relative to an explicit
digest model. The scalar half is interpreted as its encoded unsigned integer. -/
def AgaveFullAccept (hash : HashBytes → BitVec 512) (a r s : BitVec 256)
    (msg : HashBytes) : Prop :=
  AgaveStrictAccept a r s.toNat (messageChallenge hash r a msg)

/-- Firedancer's acceptance checks applied to the scalar obtained from its
actual digest/reduction specification. A nonreturning hash/reduction pipeline
has no accepting witness. -/
def FiredancerFullAccept (calls : FiredancerHashCalls) (reduce : FiredancerReduce)
    (blk : Option LiveBlock) (off : BitVec 64) (a r s : BitVec 256)
    (msg : HashBytes) : Prop :=
  ∃ challenge, firedancerChallenge calls reduce blk off r a msg = some challenge ∧
    FiredancerAccept a r s.toNat challenge

/-- Expand the full-input predicate into the exact digest and four-word
reduction witnesses named by both existing Firedancer verifier specs. -/
theorem firedancerFullAccept_iff_digest_reduction
    (calls : FiredancerHashCalls) (reduce : FiredancerReduce)
    (blk : Option LiveBlock) (off : BitVec 64) (a r s : BitVec 256) (msg : HashBytes) :
    FiredancerFullAccept calls reduce blk off a r s msg ↔
      ∃ digest words, firedancerDigest calls blk off r a msg = some digest ∧
        reduce digest = some words ∧
        FiredancerAccept a r s.toNat (firedancerReducedScalar words) := by
  constructor
  · rintro ⟨challenge, hpipeline, haccept⟩
    simp only [firedancerChallenge, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hpipeline
    obtain ⟨digest, hd, words, hw, rfl⟩ := hpipeline
    exact ⟨digest, words, hd, hw, haccept⟩
  · rintro ⟨digest, words, hd, hw, haccept⟩
    refine ⟨firedancerReducedScalar words, ?_, haccept⟩
    simp only [firedancerChallenge, hd, Option.bind_some, hw, Option.map_some]

/-- Refinement identifies the one scalar relevant to this invocation; there is
no global equality-of-implementations premise. -/
theorem firedancerFullAccept_iff_of_challenge_refines
    (calls : FiredancerHashCalls) (reduce : FiredancerReduce)
    (hash : HashBytes → BitVec 512) (blk : Option LiveBlock) (off : BitVec 64)
    (a r s : BitVec 256) (msg : HashBytes)
    (hchallenge : ChallengeRefines calls reduce hash blk off r a msg) :
    FiredancerFullAccept calls reduce blk off a r s msg ↔
      FiredancerAccept a r s.toNat (messageChallenge hash r a msg) := by
  unfold ChallengeRefines at hchallenge
  simp only [FiredancerFullAccept, hchallenge, Option.some.injEq]
  constructor
  · rintro ⟨challenge, heq, haccept⟩
    cases heq
    exact haccept
  · intro haccept
    exact ⟨_, rfl, haccept⟩

/-- The complete-input policy relationship. The public key need not be
canonically encoded. Canonical R is derived from strict acceptance. -/
theorem agaveFull_iff_firedancerFull_and_canonical
    (calls : FiredancerHashCalls) (reduce : FiredancerReduce)
    (hash : HashBytes → BitVec 512) (blk : Option LiveBlock) (off : BitVec 64)
    (a r s : BitVec 256) (msg : HashBytes)
    (hchallenge : ChallengeRefines calls reduce hash blk off r a msg) :
    AgaveFullAccept hash a r s msg ↔
      FiredancerFullAccept calls reduce blk off a r s msg ∧ CanonicalY r := by
  rw [firedancerFullAccept_iff_of_challenge_refines calls reduce hash blk off a r s msg hchallenge]
  exact agave_iff_firedancer_and_canonical a r s.toNat (messageChallenge hash r a msg)

/-- One-way inclusion has no canonical-encoding hypothesis on either R or A.
Only the explicit hash/reduction refinement remains. -/
theorem agaveFull_implies_firedancerFull
    (calls : FiredancerHashCalls) (reduce : FiredancerReduce)
    (hash : HashBytes → BitVec 512) (blk : Option LiveBlock) (off : BitVec 64)
    (a r s : BitVec 256) (msg : HashBytes)
    (hchallenge : ChallengeRefines calls reduce hash blk off r a msg)
    (haccept : AgaveFullAccept hash a r s msg) :
    FiredancerFullAccept calls reduce blk off a r s msg :=
  ((agaveFull_iff_firedancerFull_and_canonical
    calls reduce hash blk off a r s msg hchallenge).mp haccept).1

/-- Exact equivalence holds on the canonical-R input domain. -/
theorem agaveFull_iff_firedancerFull_of_canonical
    (calls : FiredancerHashCalls) (reduce : FiredancerReduce)
    (hash : HashBytes → BitVec 512) (blk : Option LiveBlock) (off : BitVec 64)
    (a r s : BitVec 256) (msg : HashBytes)
    (hchallenge : ChallengeRefines calls reduce hash blk off r a msg)
    (hcanonical : CanonicalY r) :
    AgaveFullAccept hash a r s msg ↔
      FiredancerFullAccept calls reduce blk off a r s msg := by
  rw [agaveFull_iff_firedancerFull_and_canonical
    calls reduce hash blk off a r s msg hchallenge, and_iff_left hcanonical]

/-- Every disagreement, under the same local cryptographic refinement, is
precisely a Firedancer-accepted input whose R bytes are noncanonical. This does
not assert existence of a SHA-512 preimage for the shared-challenge witness. -/
theorem firedancerFull_only_iff_noncanonical
    (calls : FiredancerHashCalls) (reduce : FiredancerReduce)
    (hash : HashBytes → BitVec 512) (blk : Option LiveBlock) (off : BitVec 64)
    (a r s : BitVec 256) (msg : HashBytes)
    (hchallenge : ChallengeRefines calls reduce hash blk off r a msg) :
    (FiredancerFullAccept calls reduce blk off a r s msg ∧ ¬ AgaveFullAccept hash a r s msg) ↔
      FiredancerFullAccept calls reduce blk off a r s msg ∧ ¬ CanonicalY r := by
  rw [agaveFull_iff_firedancerFull_and_canonical
    calls reduce hash blk off a r s msg hchallenge]
  tauto

end Agave.Ed25519.Bridge
