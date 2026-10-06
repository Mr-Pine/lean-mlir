import SSA.Projects.Agave.Ed25519.Bridge.Challenge

/-!
Reusable implementation obligations extending the existing `HashChallenge`
API. Hash-state refinement and scalar arithmetic remain separate:

* `DigestBy`: the existing init/append/fini chain returns the supplied
  one-shot digest on exactly R || A || M. This is the function-extensional
  hash premise; it has no scalar-reduction or verification conclusion.
* `ReductionValueCorrect`: a successful reducer output is the canonical
  little-endian residue modulo L. The existing `ScalarReduceBy` contract
  states determinism and a memory footprint, and does not imply this fact.

Neither obligation is asserted here. The local streaming theorem already in
`HashChallenge` implies the uniform `DigestBy` premise. A total reducer value
contract then implies `ChallengeRefines` for arbitrary message bytes.
-/

namespace Agave.Ed25519.Bridge.Challenge

open LeanMLIR SLLVM

/-- Uniform hash-output correctness on Ed25519 transcripts, for this initial
block and offset. No requirement on irrelevant inputs or final SHA state. -/
def DigestBy (calls : FiredancerHashCalls) (blk : Option LiveBlock)
    (off : BitVec 64) (hash : HashBytes → BitVec 512) : Prop :=
  ∀ (r a : BitVec 256) (msg : HashBytes),
    firedancerDigest calls blk off r a msg = some (hash (hashTranscript r a msg))

/-- The existing reusable streaming-state invariant proves this digest
contract. This does not assume the internal states of both SHA libraries agree. -/
theorem digestBy_of_stream
    {calls : FiredancerHashCalls} {blk : Option LiveBlock} {off : BitVec 64}
    {hash : HashBytes → BitVec 512}
    (hhash : HashTranscriptRefinement calls hash blk off) :
    DigestBy calls blk off hash :=
  firedancerDigest_eq_of_transcript_refinement calls hash blk off hhash

theorem DigestBy.congr {calls : FiredancerHashCalls} {blk : Option LiveBlock}
    {off : BitVec 64} {agaveHash firedancerHash : HashBytes → BitVec 512}
    (hby : DigestBy calls blk off firedancerHash)
    (heq : DigestAgreement agaveHash firedancerHash) :
    DigestBy calls blk off agaveHash := by
  intro r a msg
  rw [hby r a msg, heq r a msg]

/-- The missing arithmetic component of the current Firedancer reducer
contract, stated only on successful outputs. This implies neither termination
nor machine execution; it specifies the exact value of a returned scalar. -/
def ReductionValueCorrect (f : FiredancerReduce) : Prop :=
  ∀ digest words, f digest = some words →
    (Firedancer.Common.packWords words).toNat = hashToScalar digest

/-- A form suitable for arithmetic proofs establishing a range and modular
congruence separately. Congruence alone is insufficient because the verifier
multiplies arbitrary curve points, not just the prime-order subgroup. -/
def ReductionResidueCorrect (f : FiredancerReduce) : Prop :=
  ∀ digest words, f digest = some words →
    (Firedancer.Common.packWords words).toNat < subgroupOrder ∧
      (Firedancer.Common.packWords words).toNat % subgroupOrder = hashToScalar digest

theorem reductionValueCorrect_iff_residueCorrect (f : FiredancerReduce) :
    ReductionValueCorrect f ↔ ReductionResidueCorrect f := by
  constructor
  · intro h digest words hw
    rw [h digest words hw]
    exact ⟨hashToScalar_lt_order digest, Nat.mod_eq_of_lt (hashToScalar_lt_order digest)⟩
  · intro h digest words hw
    obtain ⟨hbound, hmod⟩ := h digest words hw
    exact hashToScalar_eq_of_canonical_congruent digest _ hbound hmod

/-- Equality of the exact challenge consumed by the existing Firedancer
specification. Its `% 2^255` is justified by a canonical reducer output, not
dropped as a definitional simplification. -/
theorem returned_challenge_eq
    {calls : FiredancerHashCalls} {f : FiredancerReduce}
    {blk : Option LiveBlock} {off : BitVec 64} {hash : HashBytes → BitVec 512}
    (hhash : DigestBy calls blk off hash) (hreduce : ReductionValueCorrect f)
    (r a : BitVec 256) (msg : HashBytes) (digest : BitVec 512) (words : Fin 4 → BitVec 64)
    (hdigest : firedancerDigest calls blk off r a msg = some digest)
    (hwords : f digest = some words) :
    firedancerReducedScalar words = messageChallenge hash r a msg := by
  have hd : digest = hash (hashTranscript r a msg) :=
    Option.some.inj (hdigest.symm.trans (hhash r a msg))
  rw [firedancerReducedScalar_eq_hashToScalar digest words (hreduce digest words hwords), hd]
  rfl

/-- Combine uniform digest correctness, reducer termination, and reducer
value correctness into the composed premise used by `FullInput.lean`.
No bound on the length or contents of the message is introduced. -/
theorem challengeRefines_of_digestBy_and_reduction
    {calls : FiredancerHashCalls} {f : FiredancerReduce}
    {blk : Option LiveBlock} {off : BitVec 64} {hash : HashBytes → BitVec 512}
    (hhash : DigestBy calls blk off hash)
    (htotal : ∀ digest, ∃ words, f digest = some words)
    (hreduce : ReductionValueCorrect f)
    (r a : BitVec 256) (msg : HashBytes) :
    ChallengeRefines calls f hash blk off r a msg := by
  obtain ⟨words, hw⟩ := htotal (hash (hashTranscript r a msg))
  exact challengeRefines_of_digest_and_reduction calls f hash blk off r a msg words
    (hhash r a msg) hw (hreduce _ words hw)

/-- The standard streaming invariant and a total, correct reducer discharge
the full-input bridge's explicit cryptographic premise. -/
theorem challengeRefines_of_stream_and_reduction
    {calls : FiredancerHashCalls} {f : FiredancerReduce}
    {blk : Option LiveBlock} {off : BitVec 64} {hash : HashBytes → BitVec 512}
    (hhash : HashTranscriptRefinement calls hash blk off)
    (htotal : ∀ digest, ∃ words, f digest = some words)
    (hreduce : ReductionValueCorrect f)
    (r a : BitVec 256) (msg : HashBytes) :
    ChallengeRefines calls f hash blk off r a msg :=
  challengeRefines_of_digestBy_and_reduction (digestBy_of_stream hhash) htotal hreduce r a msg

end Agave.Ed25519.Bridge.Challenge
