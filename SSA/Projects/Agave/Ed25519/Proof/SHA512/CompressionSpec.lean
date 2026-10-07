import SSA.Projects.Agave.Ed25519.Proof.SHA512.Padding

/-!
An independent SHA-512 compression specification (FIPS 180-4, §§4.1.3,
4.2.3 and 6.4.2). It uses an append-only message schedule and named working
words, rather than either Rust backend's rolling/vector schedule. All words
wrap modulo 2^64. This module specifies the algorithm; it does not assert
that an imported implementation executes it.
Normative source: https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.180-4.pdf
-/

namespace Agave.Ed25519.SHA512.Spec

open Agave.Ed25519.Bridge.Challenge

abbrev Word := BitVec 64

structure State where
  a : Word
  b : Word
  c : Word
  d : Word
  e : Word
  f : Word
  g : Word
  h : Word
  deriving DecidableEq

/-- FIPS 180-4 §4.2.3, in round order. -/
def constants : Vector Word 80 := #v[
  0x428a2f98d728ae22, 0x7137449123ef65cd, 0xb5c0fbcfec4d3b2f, 0xe9b5dba58189dbbc,
  0x3956c25bf348b538, 0x59f111f1b605d019, 0x923f82a4af194f9b, 0xab1c5ed5da6d8118,
  0xd807aa98a3030242, 0x12835b0145706fbe, 0x243185be4ee4b28c, 0x550c7dc3d5ffb4e2,
  0x72be5d74f27b896f, 0x80deb1fe3b1696b1, 0x9bdc06a725c71235, 0xc19bf174cf692694,
  0xe49b69c19ef14ad2, 0xefbe4786384f25e3, 0x0fc19dc68b8cd5b5, 0x240ca1cc77ac9c65,
  0x2de92c6f592b0275, 0x4a7484aa6ea6e483, 0x5cb0a9dcbd41fbd4, 0x76f988da831153b5,
  0x983e5152ee66dfab, 0xa831c66d2db43210, 0xb00327c898fb213f, 0xbf597fc7beef0ee4,
  0xc6e00bf33da88fc2, 0xd5a79147930aa725, 0x06ca6351e003826f, 0x142929670a0e6e70,
  0x27b70a8546d22ffc, 0x2e1b21385c26c926, 0x4d2c6dfc5ac42aed, 0x53380d139d95b3df,
  0x650a73548baf63de, 0x766a0abb3c77b2a8, 0x81c2c92e47edaee6, 0x92722c851482353b,
  0xa2bfe8a14cf10364, 0xa81a664bbc423001, 0xc24b8b70d0f89791, 0xc76c51a30654be30,
  0xd192e819d6ef5218, 0xd69906245565a910, 0xf40e35855771202a, 0x106aa07032bbd1b8,
  0x19a4c116b8d2d0c8, 0x1e376c085141ab53, 0x2748774cdf8eeb99, 0x34b0bcb5e19b48a8,
  0x391c0cb3c5c95a63, 0x4ed8aa4ae3418acb, 0x5b9cca4f7763e373, 0x682e6ff3d6b2b8a3,
  0x748f82ee5defb2fc, 0x78a5636f43172f60, 0x84c87814a1f0ab72, 0x8cc702081a6439ec,
  0x90befffa23631e28, 0xa4506cebde82bde9, 0xbef9a3f7b2c67915, 0xc67178f2e372532b,
  0xca273eceea26619c, 0xd186b8c721c0c207, 0xeada7dd6cde0eb1e, 0xf57d4f7fee6ed178,
  0x06f067aa72176fba, 0x0a637dc5a2c898a6, 0x113f9804bef90dae, 0x1b710b35131c471b,
  0x28db77f523047d84, 0x32caab7b40c72493, 0x3c9ebe0a15c9bebc, 0x431d67c49c100d4c,
  0x4cc5d4becb3e42b6, 0x597f299cfc657e2a, 0x5fcb6fab3ad6faec, 0x6c44198c4a475817]

def choose (x y z : Word) : Word := (x &&& y) ^^^ (~~~x &&& z)
def majority (x y z : Word) : Word :=
  (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)
def bigSigma0 (x : Word) : Word :=
  x.rotateRight 28 ^^^ x.rotateRight 34 ^^^ x.rotateRight 39
def bigSigma1 (x : Word) : Word :=
  x.rotateRight 14 ^^^ x.rotateRight 18 ^^^ x.rotateRight 41
def smallSigma0 (x : Word) : Word :=
  x.rotateRight 1 ^^^ x.rotateRight 8 ^^^ (x >>> 7)
def smallSigma1 (x : Word) : Word :=
  x.rotateRight 19 ^^^ x.rotateRight 61 ^^^ (x >>> 6)

/-- FIPS round, with its message word and constant kept separate. -/
def round (s : State) (word constant : Word) : State :=
  let t1 := s.h + bigSigma1 s.e + choose s.e s.f s.g + constant + word
  let t2 := bigSigma0 s.a + majority s.a s.b s.c
  ⟨t1 + t2, s.a, s.b, s.c, s.d + t1, s.e, s.f, s.g⟩

/-- Address-order input bytes form a big-endian message word. -/
def readWordBE (block : Bytes) (i : Nat) : Word :=
  (List.range 8).foldl
    (fun acc j => (acc <<< 8) ||| (block.getD (8 * i + j) 0).setWidth 64) 0

def messageWords (block : Bytes) : List Word :=
  (List.range 16).map (readWordBE block)

/-- Extend the full schedule, retaining every previous word for clarity.
The four indices are t-2, t-7, t-15 and t-16, where t=16+n. -/
def schedulePrefix (block : Bytes) : Nat → List Word
  | 0 => messageWords block
  | n + 1 =>
    let previous := schedulePrefix block n
    previous ++ [smallSigma1 (previous.getD (n + 14) 0) +
      previous.getD (n + 9) 0 + smallSigma0 (previous.getD (n + 1) 0) +
      previous.getD n 0]

@[simp] theorem schedulePrefix_length (block : Bytes) (n : Nat) :
    (schedulePrefix block n).length = 16 + n := by
  induction n with
  | zero => simp [schedulePrefix, messageWords]
  | succ n ih => simp [schedulePrefix, ih, Nat.add_assoc]

def schedule (block : Bytes) : List Word := schedulePrefix block 64

@[simp] theorem schedule_length (block : Bytes) : (schedule block).length = 80 := by
  simp [schedule]

/-- General round segment; the constant and schedule index advance together. -/
def roundsFrom (s : State) (words : List Word) (start : Nat) : Nat → State
  | 0 => s
  | n + 1 => round (roundsFrom s words start n)
      (words.getD (start + n) 0) (constants.toList.getD (start + n) 0)

/-- Cut-point composition, used to verify short pieces without unfolding
earlier rounds. This holds for arbitrary state, schedule, start and lengths. -/
theorem roundsFrom_add (s : State) (words : List Word) (start n k : Nat) :
    roundsFrom s words start (n + k) =
      roundsFrom (roundsFrom s words start n) words (start + n) k := by
  induction k with
  | zero => simp [roundsFrom]
  | succ k ih =>
    change round (roundsFrom s words start (n + k))
        (words.getD (start + (n + k)) 0) (constants.toList.getD (start + (n + k)) 0) =
      round (roundsFrom (roundsFrom s words start n) words (start + n) k)
        (words.getD ((start + n) + k) 0) (constants.toList.getD ((start + n) + k) 0)
    rw [ih, Nat.add_assoc]

def feedForward (initial final : State) : State :=
  ⟨initial.a + final.a, initial.b + final.b, initial.c + final.c,
   initial.d + final.d, initial.e + final.e, initial.f + final.f,
   initial.g + final.g, initial.h + final.h⟩

def compressBlock (initial : State) (block : Bytes) : State :=
  feedForward initial (roundsFrom initial (schedule block) 0 80)

/-- Native little-endian chaining-word storage, distinct from digest output
serialization and big-endian input message words. -/
def unpack (s : BitVec 512) : State :=
  ⟨s.extractLsb' 0 64, s.extractLsb' 64 64, s.extractLsb' 128 64,
   s.extractLsb' 192 64, s.extractLsb' 256 64, s.extractLsb' 320 64,
   s.extractLsb' 384 64, s.extractLsb' 448 64⟩

def pack (s : State) : BitVec 512 :=
  s.h ++ s.g ++ s.f ++ s.e ++ s.d ++ s.c ++ s.b ++ s.a

/-- FIPS 180-4 §5.3.5, declared independently of the extracted initializer. -/
def initial : State :=
  ⟨0x6a09e667f3bcc908, 0xbb67ae8584caa73b, 0x3c6ef372fe94f82b,
   0xa54ff53a5f1d36f1, 0x510e527fade682d1, 0x9b05688c2b3e6c1f,
   0x1f83d9abfb41bd6b, 0x5be0cd19137e2179⟩

/-- All eight native chaining words loaded by the exact caller agree with
the independently declared standard IV. -/
theorem extracted_initial_eq :
    unpack Agave.Ed25519.Verifier.Execution.Challenge.initialWords = initial := by
  decide +kernel

def compressBlockBytes (initial : BitVec 512) (block : Bytes) : BitVec 512 :=
  pack (compressBlock (unpack initial) block)

/-- The AVX2 backend's optimized Boolean expression is the specified Ch. -/
theorem choose_xor_form (x y z : Word) :
    z ^^^ (x &&& (y ^^^ z)) = choose x y z := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [choose, BitVec.getLsbD_xor, BitVec.getLsbD_and, BitVec.getLsbD_not,
    hi, decide_true, Bool.true_and]
  cases x.getLsbD i <;> cases y.getLsbD i <;> cases z.getLsbD i <;> decide

/-- Source-shaped scalar round used by the AVX2 leaf, whose schedule already
contains K[t]+W[t]. Keeping this tiny lemma separate avoids repeating Boolean
normalization and modular-addition reassociation at all eighty cut points. -/
def avxRound (s : State) (kw : Word) : State :=
  let t := kw + s.h + bigSigma1 s.e + (s.g ^^^ (s.e &&& (s.f ^^^ s.g)))
  ⟨t + bigSigma0 s.a + majority s.a s.b s.c,
    s.a, s.b, s.c, s.d + t, s.e, s.f, s.g⟩

theorem avxRound_eq_round (s : State) (word constant : Word) :
    avxRound s (constant + word) = round s word constant := by
  simp only [avxRound, round, choose_xor_form]
  congr 1 <;> ac_rfl

/-- Scalar software backend's addition order, stated separately from the
standard round so that only one reusable reassociation proof is needed. -/
def softRound (s : State) (word constant : Word) : State :=
  let t1 := bigSigma1 s.e + choose s.e s.f s.g + constant + word + s.h
  let t2 := bigSigma0 s.a + majority s.a s.b s.c
  ⟨t1 + t2, s.a, s.b, s.c, s.d + t1, s.e, s.f, s.g⟩

theorem softRound_eq_round (s : State) (word constant : Word) :
    softRound s word constant = round s word constant := by
  simp only [softRound, round]
  congr 1 <;> ac_rfl

theorem pack_unpack (s : BitVec 512) : pack (unpack s) = s := by
  simp only [pack, unpack]
  rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (by decide : 448 = 384 + 64),
    BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (by decide : 384 = 320 + 64),
    BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (by decide : 320 = 256 + 64),
    BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (by decide : 256 = 192 + 64),
    BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (by decide : 192 = 128 + 64),
    BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (by decide : 128 = 64 + 64),
    BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (by decide : 64 = 0 + 64)]
  simp

theorem unpack_pack (s : State) : unpack (pack s) = s := by
  cases s
  simp only [pack, unpack]
  congr 1 <;> repeat' (rw [BitVec.extractLsb'_append_eq_ite]; norm_num)

end Agave.Ed25519.SHA512.Spec
