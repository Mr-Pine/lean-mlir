import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSpec
import SSA.Projects.Firedancer.Common.Spec.Scalar.fd_curve25519_scalar_reduce

/-!
# The full Ed25519 hash-to-scalar boundary

Agave's `ed_sigs/verification_key.rs::challenge_scalar` appends the original
32-byte R, original 32-byte public key, then the message to `Sha512::default()`.
`ed_sigs.rs::scalar_from_sha512` interprets the finalized 64 bytes through
`Scalar::from_bytes_mod_order_wide`. The mathematical specification of that
last operation is the little-endian digest integer modulo the subgroup order.

Firedancer's existing specification does **not** specify either SHA-512 or
reduction modulo the subgroup order. Its `ed25519Digest` chains state-dependent
partial functions and `ScalarReduceBy` only specifies determinism/footprint.
Moreover, its double-scalar specification uses the low 255 bits of the packed
reduction output. This module preserves all of those details.

No SHA-512 correctness is asserted here: `hash` is an explicit digest model.
`ChallengeRefines` is the remaining local, composed hash/reduction obligation.
The sufficient conditions below separate the digest and scalar obligations,
and show that the 255-bit mask disappears for a correctly reduced scalar.
-/

namespace Agave.Ed25519.Bridge

open LeanMLIR SLLVM

abbrev HashBytes := List (BitVec 8)

/-- The original input bytes, in address order. A `BitVec 256` stores byte 0
in its least significant eight bits. No point decoding/recompression occurs. -/
def inputBytes (w : BitVec 256) : HashBytes :=
  List.ofFn fun i : Fin 32 => w.extractLsb' (i * 8) 8

/-- The source-level transcript shared by both clients, including when A or R
has a noncanonical point encoding. -/
def hashTranscript (r a : BitVec 256) (msg : HashBytes) : HashBytes :=
  inputBytes r ++ inputBytes a ++ msg

theorem inputBytes_eq_firedancer (w : BitVec 256) :
    inputBytes w = Firedancer.Common.bytesOf (n := 32) w := rfl

/-- The byte lists in Firedancer's three `append` calls concatenate to exactly
the transcript passed to Agave's digest model. -/
theorem hashTranscript_eq_firedancer (r a : BitVec 256) (msg : HashBytes) :
    hashTranscript r a msg =
      Firedancer.Common.bytesOf (n := 32) r ++
        Firedancer.Common.bytesOf (n := 32) a ++ msg := rfl

theorem hashTranscript_length (r a : BitVec 256) (msg : HashBytes) :
    (hashTranscript r a msg).length = 64 + msg.length := by
  simp [hashTranscript, inputBytes] <;> omega

/-- The 64 digest bytes interpreted as a little-endian integer, reduced modulo
the scalar order. This is a mathematical specification, not a refinement proof
of either client's scalar-reduction implementation. -/
def hashToScalar (digest : BitVec 512) : Nat := digest.toNat % subgroupOrder

theorem hashToScalar_lt_order (digest : BitVec 512) :
    hashToScalar digest < subgroupOrder :=
  Nat.mod_lt _ (by norm_num [subgroupOrder])

theorem hashToScalar_lt_255 (digest : BitVec 512) :
    hashToScalar digest < 2 ^ 255 := by
  exact lt_trans (hashToScalar_lt_order digest) (by norm_num [subgroupOrder])

def messageChallenge (hash : HashBytes → BitVec 512)
    (r a : BitVec 256) (msg : HashBytes) : Nat :=
  hashToScalar (hash (hashTranscript r a msg))

/-- The three partial functions named by Firedancer's existing SHA contracts.
This record introduces neither a SHA implementation nor any correctness claim. -/
structure FiredancerHashCalls where
  init : Option LiveBlock → BitVec 64 → Option (Option LiveBlock)
  append : Option LiveBlock → BitVec 64 → HashBytes → Option (Option LiveBlock)
  finish : Option LiveBlock → BitVec 64 → Option LiveBlock → BitVec 64 →
    Option (BitVec 512)

abbrev FiredancerReduce := BitVec 512 → Option (Fin 4 → BitVec 64)

/-- The exact digest expression in both existing Firedancer verifier specs. -/
def firedancerDigest (calls : FiredancerHashCalls) (blk : Option LiveBlock)
    (off : BitVec 64) (r a : BitVec 256) (msg : HashBytes) : Option (BitVec 512) :=
  Firedancer.Common.ed25519Digest calls.init calls.append calls.finish blk off r a msg

/-- The exact scalar consumed by Firedancer's double-scalar specification.
The low-255-bit restriction is retained until scalar correctness removes it. -/
def firedancerReducedScalar (words : Fin 4 → BitVec 64) : Nat :=
  (Firedancer.Common.packWords words).toNat % 2 ^ 255

/-- The actual existing Firedancer digest/reduction contract composed into one
partial challenge computation, including its initial SHA state and offset. -/
def firedancerChallenge (calls : FiredancerHashCalls) (reduce : FiredancerReduce)
    (blk : Option LiveBlock) (off : BitVec 64) (r a : BitVec 256)
    (msg : HashBytes) : Option Nat :=
  (firedancerDigest calls blk off r a msg).bind fun digest =>
    (reduce digest).map firedancerReducedScalar

/-- The smallest local hash/reduction refinement used by the full-input bridge.
It requires termination and equality of the scalar actually consumed, rather
than equality of all intermediate digests or of all internal SHA states. -/
def ChallengeRefines (calls : FiredancerHashCalls) (reduce : FiredancerReduce)
    (hash : HashBytes → BitVec 512) (blk : Option LiveBlock) (off : BitVec 64)
    (r a : BitVec 256) (msg : HashBytes) : Prop :=
  firedancerChallenge calls reduce blk off r a msg = some (messageChallenge hash r a msg)

/-- A correctly reduced scalar fits below 2^255, so the mask in Firedancer's
double-scalar spec does not change it. No range hypothesis on the digest. -/
theorem firedancerReducedScalar_eq_hashToScalar
    (digest : BitVec 512) (words : Fin 4 → BitVec 64)
    (hreduce : (Firedancer.Common.packWords words).toNat = hashToScalar digest) :
    firedancerReducedScalar words = hashToScalar digest := by
  rw [firedancerReducedScalar, hreduce, Nat.mod_eq_of_lt (hashToScalar_lt_255 digest)]

/-- Pointwise digest equality and mathematical scalar reduction suffice for
the composed refinement. These are explicit hypotheses, not consequences of
the pre-existing SHA determinism or scalar footprint contracts. -/
theorem challengeRefines_of_digest_and_reduction
    (calls : FiredancerHashCalls) (reduce : FiredancerReduce)
    (hash : HashBytes → BitVec 512) (blk : Option LiveBlock) (off : BitVec 64)
    (r a : BitVec 256) (msg : HashBytes) (words : Fin 4 → BitVec 64)
    (hdigest : firedancerDigest calls blk off r a msg =
      some (hash (hashTranscript r a msg)))
    (hreduce : reduce (hash (hashTranscript r a msg)) = some words)
    (hscalar : (Firedancer.Common.packWords words).toNat =
      hashToScalar (hash (hashTranscript r a msg))) :
    ChallengeRefines calls reduce hash blk off r a msg := by
  simp only [ChallengeRefines, firedancerChallenge, hdigest, Option.bind_some,
    hreduce, Option.map_some, messageChallenge]
  exact congrArg some (firedancerReducedScalar_eq_hashToScalar _ words hscalar)

/-- A standard streaming-state refinement sufficient to identify the digest.
The represented transcript is independent of the physical SHA block; the
final digest is written into the fresh zeroed 64-byte local used by the actual
Firedancer digest specification. Only `init` concerns the given initial block. -/
structure HashTranscriptRefinement (calls : FiredancerHashCalls)
    (hash : HashBytes → BitVec 512) (blk : Option LiveBlock) (off : BitVec 64) where
  represents : Option LiveBlock → HashBytes → Prop
  init : ∃ b, calls.init blk off = some b ∧ represents b []
  append : ∀ b transcript chunk, represents b transcript →
    ∃ b', calls.append b off chunk = some b' ∧ represents b' (transcript ++ chunk)
  finish : ∀ b transcript, represents b transcript →
    calls.finish b off (some { length := 64, bytes := 0#_ }) 0 = some (hash transcript)

/-- Prove the complete transcript order through the real Firedancer digest
definition from the explicit streaming-state contract. SHA rounds themselves
are outside this theorem. -/
theorem firedancerDigest_eq_of_transcript_refinement
    (calls : FiredancerHashCalls) (hash : HashBytes → BitVec 512)
    (blk : Option LiveBlock) (off : BitVec 64)
    (hhash : HashTranscriptRefinement calls hash blk off)
    (r a : BitVec 256) (msg : HashBytes) :
    firedancerDigest calls blk off r a msg = some (hash (hashTranscript r a msg)) := by
  obtain ⟨b₀, hi, hb₀⟩ := hhash.init
  obtain ⟨b₁, hr, hb₁⟩ := hhash.append b₀ [] (inputBytes r) hb₀
  obtain ⟨b₂, ha, hb₂⟩ := hhash.append b₁ ([] ++ inputBytes r) (inputBytes a) hb₁
  obtain ⟨b₃, hm, hb₃⟩ :=
    hhash.append b₂ (([] ++ inputBytes r) ++ inputBytes a) msg hb₂
  have hf := hhash.finish b₃ ((([] ++ inputBytes r) ++ inputBytes a) ++ msg) hb₃
  simpa only [firedancerDigest, Firedancer.Common.ed25519Digest,
    ← inputBytes_eq_firedancer, hi, hr, ha, hm, Option.bind_some,
    List.nil_append, hashTranscript, List.append_assoc] using hf

end Agave.Ed25519.Bridge
