import SSA.Projects.Agave.Ed25519.Bridge.ChallengeBytes
import SSA.Projects.Agave.Ed25519.Bridge.HashChallenge

/-!
Exact byte-order and modular-arithmetic facts extending `HashChallenge`.
These are specification lemmas, not proofs of the SHA-512 compression function
or either executable scalar reducer.

The pinned `solana-ed25519` 0.2.4 source calls `challenge_scalar` in
`MLIR/source/src/ed_sigs/verification_key.rs`: update with the original R bytes,
then the stored original A bytes, then the message. `scalar_from_sha512` in
`ed_sigs.rs` copies all 64 digest bytes to `from_bytes_mod_order_wide`.

`DigestAgreement` is a premise only about two digest functions on these
transcripts. Equality on all possible SHA inputs is stronger than necessary.
All byte assembly, modulo arithmetic, output bounds, and acceptance-policy
transport below are proved without a cryptographic assumption.
-/

namespace Agave.Ed25519.Bridge.Challenge

theorem bytesOf_eq_firedancer {n : Nat} (w : BitVec (n * 8)) :
    bytesOf w = Firedancer.Common.bytesOf w := rfl

theorem bytesOf32_eq_inputBytes (w : BitVec 256) :
    bytesOf (n := 32) w = inputBytes w := rfl

/-- The existing transcript's point bytes denote precisely their full
256-bit little-endian values, including a noncanonical point encoding. -/
@[simp] theorem decodeLE_inputBytes (w : BitVec 256) :
    decodeLE (inputBytes w) = w.toNat :=
  decodeLE_bytesOf (n := 32) w

/-- Three updates preserve the original byte strings in the source order.
The message has arbitrary finite length and arbitrary byte contents. -/
theorem transcript_three_updates (r a : BitVec 256) (msg : HashBytes) :
    ((([] : HashBytes) ++ inputBytes r) ++ inputBytes a) ++ msg =
      hashTranscript r a msg := by
  simp [hashTranscript, List.append_assoc]

theorem transcript_chunk_message (r a : BitVec 256) (xs ys : HashBytes) :
    hashTranscript r a (xs ++ ys) = hashTranscript r a xs ++ ys := by
  simp [hashTranscript, List.append_assoc]

/-- Only agreement on the relevant inputs is required, for all R, A, and
messages. This premise does not mention scalar reduction or verification. -/
def DigestAgreement (agaveHash firedancerHash : HashBytes → BitVec 512) : Prop :=
  ∀ (r a : BitVec 256) (msg : HashBytes),
    agaveHash (hashTranscript r a msg) = firedancerHash (hashTranscript r a msg)

theorem digestAgreement_of_ext {agaveHash firedancerHash : HashBytes → BitVec 512}
    (h : ∀ bytes, agaveHash bytes = firedancerHash bytes) :
    DigestAgreement agaveHash firedancerHash :=
  fun r a msg => h (hashTranscript r a msg)

/-- The canonical 32-byte encoding of the existing hash-to-scalar spec. -/
def reducedBytes (digest : BitVec 512) : BitVec 256 :=
  BitVec.ofNat 256 (hashToScalar digest)

theorem hashToScalar_lt_256 (digest : BitVec 512) : hashToScalar digest < 2 ^ 256 :=
  (hashToScalar_lt_255 digest).trans (by decide)

@[simp] theorem reducedBytes_toNat (digest : BitVec 512) :
    (reducedBytes digest).toNat = hashToScalar digest := by
  exact Nat.mod_eq_of_lt (hashToScalar_lt_256 digest)

/-- Reduction is of the digest's little-endian bytes, not of a reversed
digest or a SHA internal word representation. -/
theorem hashToScalar_eq_decodeLE (digest : BitVec 512) :
    hashToScalar digest = decodeLE (bytesOf (n := 64) digest) % subgroupOrder := by
  rw [decodeLE_bytesOf]
  rfl

theorem reducedBytes_decodeLE (digest : BitVec 512) :
    decodeLE (bytesOf (n := 32) (reducedBytes digest)) =
      decodeLE (bytesOf (n := 64) digest) % subgroupOrder := by
  rw [decodeLE_bytesOf, reducedBytes_toNat, hashToScalar_eq_decodeLE]

/-- Firedancer's double-scalar specification masks its scalar to 255 bits.
A correctly reduced challenge is already below L < 2^255. -/
@[simp] theorem hashToScalar_mask255 (digest : BitVec 512) :
    hashToScalar digest % 2 ^ 255 = hashToScalar digest :=
  Nat.mod_eq_of_lt (hashToScalar_lt_255 digest)

@[simp] theorem reducedBytes_mask255 (digest : BitVec 512) :
    (reducedBytes digest).toNat % 2 ^ 255 = hashToScalar digest := by
  rw [reducedBytes_toNat, hashToScalar_mask255]

/-- A canonical representative and a congruence suffice to recover exact
integer equality, not merely equality modulo L. This reduces the arithmetic
obligations of either executable reducer to familiar separate properties. -/
theorem hashToScalar_eq_of_canonical_congruent (digest : BitVec 512) (out : Nat)
    (hbound : out < subgroupOrder) (hmod : out % subgroupOrder = hashToScalar digest) :
    out = hashToScalar digest := by
  rwa [Nat.mod_eq_of_lt hbound] at hmod

/-- Agave's radix-2^52 implementation splits the wide input after five
limbs, at bit 260. This identity fixes which half is multiplied by 2^260. -/
theorem hashToScalar_split260 (digest : BitVec 512) :
    hashToScalar digest =
      ((digest.toNat % 2 ^ 260) + 2 ^ 260 * (digest.toNat / 2 ^ 260)) %
        subgroupOrder := by
  rw [Nat.mod_add_div]
  rfl

/-- One invocation only needs equality of its two digests. -/
theorem messageChallenge_eq_of_digest_eq
    {agaveHash firedancerHash : HashBytes → BitVec 512}
    (r a : BitVec 256) (msg : HashBytes)
    (h : agaveHash (hashTranscript r a msg) = firedancerHash (hashTranscript r a msg)) :
    messageChallenge agaveHash r a msg = messageChallenge firedancerHash r a msg :=
  congrArg hashToScalar h

/-- Uniform challenge equality for every byte message follows from the
separate function-extensional SHA premise. -/
theorem messageChallenge_eq {agaveHash firedancerHash : HashBytes → BitVec 512}
    (h : DigestAgreement agaveHash firedancerHash) (r a : BitVec 256) (msg : HashBytes) :
    messageChallenge agaveHash r a msg = messageChallenge firedancerHash r a msg :=
  messageChallenge_eq_of_digest_eq r a msg (h r a msg)

/-- Transport the policy theorem between separately named hash functions.
The remaining premise is about digest outputs alone, never acceptance itself. -/
theorem strict_iff_firedancer_and_canonical
    {agaveHash firedancerHash : HashBytes → BitVec 512}
    (h : DigestAgreement agaveHash firedancerHash)
    (r a : BitVec 256) (msg : HashBytes) (s : Nat) :
    AgaveStrictAccept a r s (messageChallenge agaveHash r a msg) ↔
      FiredancerAccept a r s (messageChallenge firedancerHash r a msg) ∧ CanonicalY r := by
  rw [messageChallenge_eq h]
  exact agave_iff_firedancer_and_canonical a r s _

end Agave.Ed25519.Bridge.Challenge
