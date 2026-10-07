import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.Pow22501
import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.SignWords
import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.Constants
import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.ToBytes

/-! Concrete limb-level square-root stages. The byte comparisons use the exact
canonical serializer proved for the imported to_bytes helper. Connecting each
stage to its original memory cut point is a separate execution obligation. -/
namespace Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio
open SerialFieldMul
open Pow22501 (TightWords)

/-- The actual serializer's canonical 256-bit result. -/
def canonicalWord (a : Words) : BitVec 256 := packedBytes (tightWords a)

theorem canonicalWord_value (a : Words) :
    (canonicalWord a).toNat = (wordValue a).val := by
  rw [canonicalWord, tightWords_canonical, wordValue_eq_serialValue]
  simp only [ZMod.val_natCast]
  rfl

/-- Canonical byte equality tests field equality, including unreduced inputs. -/
theorem canonicalWord_eq_iff (a b : Words) :
    canonicalWord a = canonicalWord b ↔ wordValue a = wordValue b := by
  constructor
  · intro h
    apply ZMod.val_injective
    rw [← canonicalWord_value a, ← canonicalWord_value b, h]
  · intro h
    apply BitVec.eq_of_toNat_eq
    rw [canonicalWord_value, canonicalWord_value, h]

def equalWords (a b : TightWords) : Bool := decide (canonicalWord a.limbs = canonicalWord b.limbs)

theorem equalWords_value (a b : TightWords) :
    equalWords a b = decide (wordValue a.limbs = wordValue b.limbs) := by
  simp only [equalWords, canonicalWord_eq_iff]

def oddWord (a : TightWords) : Bool := decide ((canonicalWord a.limbs).toNat % 2 = 1)

theorem oddWord_value (a : TightWords) :
    oddWord a = decide ((wordValue a.limbs).val % 2 = 1) := by
  rw [oddWord, canonicalWord_value]

def negativeWord (a : TightWords) : TightWords :=
  ⟨negativeWords a.limbs, negativeWords_tight a.limbs (SerialPoint.tight_bounded _ a.tight)⟩

theorem negativeWord_value (a : TightWords) :
    wordValue (negativeWord a).limbs = -wordValue a.limbs :=
  negativeWords_value a.limbs (SerialPoint.tight_bounded _ a.tight)

def sqrtM1Word : TightWords := ⟨sqrtM1Limbs, sqrtM1_tight⟩

theorem sqrtM1Word_value : wordValue sqrtM1Word.limbs = _root_.sqrtm1 := sqrtM1_value

/-- Calls after pow22501: two squarings of the first component, then x times it. -/
def powP58Word (x : TightWords) : TightWords :=
  x.mul ((Pow22501.wordChain x).1.square 2)

theorem powP58Word_value (x : TightWords) :
    wordValue (powP58Word x).limbs = Decompress.powP58 (wordValue x.limbs) := by
  have hp := congrArg Prod.fst (Pow22501.wordChain_value x)
  change wordValue (Pow22501.wordChain x).1.limbs =
    (Decompress.pow22501 (wordValue x.limbs)).1 at hp
  simp only [powP58Word, TightWords.mul_value, TightWords.square_value, hp,
    Decompress.powP58]

/-- Exact square/multiply call dependencies before any root comparison. -/
def wordCandidate (u v : TightWords) : TightWords :=
  let v3 := (v.square 1).mul v
  let v7 := (v3.square 1).mul v
  (u.mul v3).mul (powP58Word (u.mul v7))

theorem wordCandidate_value (u v : TightWords) :
    wordValue (wordCandidate u v).limbs = Decompress.candidate
      (wordValue u.limbs) (wordValue v.limbs) := by
  simp only [wordCandidate, TightWords.mul_value, TightWords.square_value,
    powP58Word_value, Decompress.candidate, show (2 : Nat) ^ 1 = 2 from rfl]

def wordCheck (u v : TightWords) : TightWords := v.mul ((wordCandidate u v).square 1)

theorem wordCheck_value (u v : TightWords) :
    wordValue (wordCheck u v).limbs = Decompress.check (wordValue u.limbs) (wordValue v.limbs) := by
  simp only [wordCheck, TightWords.mul_value, TightWords.square_value,
    wordCandidate_value, Decompress.check, show (2 : Nat) ^ 1 = 2 from rfl]

/-- Both comparisons used by the emitted correction mask are retained. -/
def wordCorrected (u v : TightWords) : TightWords :=
  if equalWords (wordCheck u v) (negativeWord u) ||
      equalWords (wordCheck u v) ((negativeWord u).mul sqrtM1Word) then
    sqrtM1Word.mul (wordCandidate u v)
  else wordCandidate u v

theorem wordCorrected_value (u v : TightWords) :
    wordValue (wordCorrected u v).limbs = Decompress.correctedRoot
      (wordValue u.limbs) (wordValue v.limbs) := by
  unfold wordCorrected
  simp only [equalWords_value, wordCheck_value, negativeWord_value,
    TightWords.mul_value, sqrtM1Word_value, Bool.or_eq_true, decide_eq_true_eq]
  split
  · rename_i h
    rw [TightWords.mul_value, sqrtM1Word_value, wordCandidate_value,
      Decompress.correctedRoot, if_pos h]
  · rename_i h
    rw [wordCandidate_value, Decompress.correctedRoot, if_neg h]

def wordNonnegative (a : TightWords) : TightWords :=
  if oddWord a then negativeWord a else a

theorem wordNonnegative_value (a : TightWords) :
    wordValue (wordNonnegative a).limbs = Decompress.nonnegative (wordValue a.limbs) := by
  unfold wordNonnegative
  simp only [oddWord_value, decide_eq_true_eq]
  split
  · rename_i h
    rw [negativeWord_value, Decompress.nonnegative, if_pos h]
  · rename_i h
    rw [Decompress.nonnegative, if_neg h]

/-- Returned choice and nonnegative root, expressed as concrete field words. -/
def wordSqrt (u v : TightWords) : Bool × TightWords :=
  (equalWords (wordCheck u v) u || equalWords (wordCheck u v) (negativeWord u),
    wordNonnegative (wordCorrected u v))

theorem wordSqrt_value (u v : TightWords) :
    ((wordSqrt u v).1, wordValue (wordSqrt u v).2.limbs) =
      Decompress.sqrtRatio (wordValue u.limbs) (wordValue v.limbs) := by
  apply Prod.ext
  · simp only [wordSqrt, equalWords_value, wordCheck_value, negativeWord_value,
      Decompress.sqrtRatio_fst]
    simp
  · simp only [wordSqrt, wordNonnegative_value, wordCorrected_value,
      Decompress.sqrtRatio_snd]

/-- Caller bounds are derived from every stage, including either conditional negation. -/
theorem wordSqrt_tight (u v : TightWords) :
    SerialPoint.Tight (unsigned (wordSqrt u v).2.limbs) := (wordSqrt u v).2.tight

end Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio
