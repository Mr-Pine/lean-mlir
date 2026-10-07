import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.SqrtWords

/-! Representation-preserving word specification for the imported decoder.
The output keeps the original parsed Y limbs. It is therefore deliberately not
a canonical serialization chosen only from an affine curve point. -/
namespace Agave.Ed25519.Encoding.Decompress.Execution.Decode
open SerialFieldMul
open Pow22501 (TightWords)

/-- Exact serial representation of the constant one. -/
def oneWord : TightWords :=
  ⟨![1#64, 0#64, 0#64, 0#64, 0#64], by
    intro i
    fin_cases i <;> decide⟩

theorem oneWord_value : wordValue oneWord.limbs = 1 := by
  norm_num [oneWord, wordValue, SerialPoint.value, decode, unsigned]
  rfl

def parsedWord (bytes : BitVec 256) : TightWords :=
  ⟨fromBytesWord bytes, fromBytesWord_tight bytes⟩

theorem parsedWord_value (bytes : BitVec 256) : wordValue (parsedWord bytes).limbs = y bytes :=
  fromBytesWord_value bytes

def subtractWord (a b : TightWords) : TightWords :=
  ⟨SerialPoint.subWord a.limbs b.limbs, by
    rw [SerialPoint.subWord_unsigned _ _ (SerialPoint.tight_bounded _ a.tight)
      (SerialPoint.tight_bounded _ b.tight)]
    exact (SerialPoint.sub_safe _ _ (SerialPoint.tight_bounded _ a.tight)
      (SerialPoint.tight_bounded _ b.tight)).2.2⟩

theorem subtractWord_value (a b : TightWords) :
    wordValue (subtractWord a b).limbs = wordValue a.limbs - wordValue b.limbs := by
  unfold wordValue
  rw [subtractWord, SerialPoint.subWord_unsigned _ _ (SerialPoint.tight_bounded _ a.tight)
    (SerialPoint.tight_bounded _ b.tight), SerialPoint.sub_value _ _ (SerialPoint.tight_bounded _ b.tight)]
  rfl

/-- The compiler increments multiplication limb zero without a reduction.
Its stronger multiplication output bound proves that this remains tight. -/
theorem mul_add_one_tight (a b : TightWords) :
    SerialPoint.Tight (unsigned
      (SerialPoint.addWord (machine a.limbs b.limbs) oneWord.limbs)) := by
  have ha := SerialPoint.tight_bounded _ a.tight
  have hb := SerialPoint.tight_bounded _ b.tight
  have ht := machine_tight a.limbs b.limbs ha hb
  have hzero : (machine a.limbs b.limbs 0).toNat < 2 ^ 51 := by
    change unsigned (machine a.limbs b.limbs) 0 < 2 ^ 51
    rw [machine_unsigned _ _ ha hb]
    simpa only [radix] using (mul_output_bounds _ _ ha hb).1 0 (by decide)
  intro i
  fin_cases i
  · change (machine a.limbs b.limbs 0 + 1#64).toNat < 2 ^ 52
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reduceMod]
    omega
  · simpa [SerialPoint.addWord, oneWord, unsigned] using ht 1
  · simpa [SerialPoint.addWord, oneWord, unsigned] using ht 2
  · simpa [SerialPoint.addWord, oneWord, unsigned] using ht 3
  · simpa [SerialPoint.addWord, oneWord, unsigned] using ht 4

def mulAddOneWord (a b : TightWords) : TightWords :=
  ⟨SerialPoint.addWord (machine a.limbs b.limbs) oneWord.limbs, mul_add_one_tight a b⟩

theorem mulAddOneWord_value (a b : TightWords) :
    wordValue (mulAddOneWord a b).limbs = wordValue a.limbs * wordValue b.limbs + 1 := by
  have hm := SerialPoint.tight_bounded _
    (machine_tight a.limbs b.limbs (SerialPoint.tight_bounded _ a.tight)
      (SerialPoint.tight_bounded _ b.tight))
  have hone := SerialPoint.tight_bounded _ oneWord.tight
  have hv : wordValue (mulAddOneWord a b).limbs =
      wordValue (machine a.limbs b.limbs) + wordValue oneWord.limbs := by
    unfold wordValue
    rw [mulAddOneWord, SerialPoint.addWord_unsigned _ _ hm hone, SerialPoint.add_value]
    rfl
  rw [hv, oneWord_value, machine_value _ _
    (SerialPoint.tight_bounded _ a.tight) (SerialPoint.tight_bounded _ b.tight)]

def curveDWord : TightWords := ⟨curveDLimbs, curveD_tight⟩

def numeratorWord (bytes : BitVec 256) : TightWords :=
  subtractWord ((parsedWord bytes).square 1) oneWord

def denominatorWord (bytes : BitVec 256) : TightWords :=
  mulAddOneWord ((parsedWord bytes).square 1) curveDWord

theorem numeratorWord_value (bytes : BitVec 256) :
    wordValue (numeratorWord bytes).limbs = numerator bytes := by
  simp only [numeratorWord, subtractWord_value, TightWords.square_value,
    parsedWord_value, oneWord_value, numerator, show (2 : Nat) ^ 1 = 2 from rfl]

theorem denominatorWord_value (bytes : BitVec 256) :
    wordValue (denominatorWord bytes).limbs = denominator bytes := by
  simp only [denominatorWord, mulAddOneWord_value, TightWords.square_value,
    parsedWord_value, curveDWord, curveD_value, denominator,
    show (2 : Nat) ^ 1 = 2 from rfl]
  ring

def wordStep1 (bytes : BitVec 256) : Bool × TightWords :=
  SqrtRatio.wordSqrt (numeratorWord bytes) (denominatorWord bytes)

theorem wordStep1_value (bytes : BitVec 256) :
    ((wordStep1 bytes).1, wordValue (wordStep1 bytes).2.limbs) = step1 bytes := by
  rw [wordStep1, SqrtRatio.wordSqrt_value, numeratorWord_value, denominatorWord_value]
  rfl

/-- Exact extended point representation; bounds are carried by each coordinate. -/
structure PointWords where
  X : TightWords
  Y : TightWords
  Z : TightWords
  T : TightWords

def pointWords (bytes : BitVec 256) (root : TightWords) : PointWords :=
  let X : TightWords := ⟨signedWords bytes[255] root.limbs,
    signedWords_tight bytes[255] root.limbs root.tight⟩
  let Y := parsedWord bytes
  ⟨X, Y, oneWord, X.mul Y⟩

def wordDecode (bytes : BitVec 256) : Option PointWords :=
  if (wordStep1 bytes).1 then some (pointWords bytes (wordStep1 bytes).2) else none

/-- Each scalar limb is stored little endian; limb zero comes first in memory. -/
def fieldPayload (a : Words) : BitVec 320 := a 4 ++ a 3 ++ a 2 ++ a 1 ++ a 0

/-- X/Y/Z/T are the exact four40-byte serial fields in the Rust payload. -/
def pointPayload (point : PointWords) : BitVec 1280 :=
  fieldPayload point.T.limbs ++ fieldPayload point.Z.limbs ++
    fieldPayload point.Y.limbs ++ fieldPayload point.X.limbs

/-- The concrete word decoder has precisely the mathematical decoder's success
predicate. No canonical-input, negative-zero, or small-order filter is added. -/
theorem wordDecode_acceptance (bytes : BitVec 256) :
    (wordDecode bytes).isSome = (Decompress.decompress bytes).isSome := by
  have hflag := congrArg Prod.fst (wordStep1_value bytes)
  change (wordStep1 bytes).1 = (step1 bytes).1 at hflag
  simp only [wordDecode, Decompress.decompress, hflag]
  split_ifs <;> rfl

/-- Field coordinates of the exact payload on the success path. -/
theorem pointWords_value (bytes : BitVec 256) :
    wordValue (pointWords bytes (wordStep1 bytes).2).X.limbs =
      (if bytes[255] then -(step1 bytes).2 else (step1 bytes).2) ∧
    wordValue (pointWords bytes (wordStep1 bytes).2).Y.limbs = y bytes ∧
    wordValue (pointWords bytes (wordStep1 bytes).2).Z.limbs = 1 ∧
    wordValue (pointWords bytes (wordStep1 bytes).2).T.limbs =
      (if bytes[255] then -(step1 bytes).2 else (step1 bytes).2) * y bytes := by
  have hroot := congrArg Prod.snd (wordStep1_value bytes)
  change wordValue (wordStep1 bytes).2.limbs = (step1 bytes).2 at hroot
  have hx : wordValue (pointWords bytes (wordStep1 bytes).2).X.limbs =
      (if bytes[255] then -(step1 bytes).2 else (step1 bytes).2) := by
    change wordValue (signedWords bytes[255] (wordStep1 bytes).2.limbs) = _
    rw [signedWords_value _ _ (SerialPoint.tight_bounded _ (wordStep1 bytes).2.tight), hroot]
  refine ⟨hx, parsedWord_value bytes, oneWord_value, ?_⟩
  change wordValue (((pointWords bytes (wordStep1 bytes).2).X).mul (parsedWord bytes)).limbs = _
  rw [TightWords.mul_value, hx, parsedWord_value]

end Agave.Ed25519.Encoding.Decompress.Execution.Decode
