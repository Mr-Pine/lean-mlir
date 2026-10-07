import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.Sign
import SSA.Projects.Agave.Ed25519.Proof.SerialPoint.PointWord

/-! Scalar words of the emitted conditional-negation network. The parallel
carry schedule is the existing proved serial subtraction schedule. -/
namespace Agave.Ed25519.Encoding.Decompress.Execution
open LeanMLIR.RIR
open SerialFieldMul

/-- The LLVM XOR/AND/XOR selection network, with a proved Choice mask. -/
def selectWord (flag : Bool) (original replacement : BitVec 64) : BitVec 64 :=
  ((replacement ^^^ original) &&&
    (if flag then BitVec.allOnes 64 else 0#64)) ^^^ original

theorem selectWord_eq (flag : Bool) (original replacement : BitVec 64) :
    selectWord flag original replacement = if flag then replacement else original := by
  cases flag
  · simp [selectWord]
  · change ((replacement ^^^ original) &&& BitVec.allOnes 64) ^^^ original = replacement
    rw [BitVec.and_allOnes, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

theorem selectWord_sign (byte : BitVec 8) (original replacement : BitVec 64) :
    ((replacement ^^^ original) &&& (0#64 - (byte >>> 7).setWidth 64)) ^^^ original =
      if byte[7] then replacement else original := by
  rw [sign_byte]
  cases byte[7]
  · simp
  · change ((replacement ^^^ original) &&& BitVec.allOnes 64) ^^^ original = replacement
    rw [BitVec.and_allOnes, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

/-- The compiler shortened the scalar low-limb bias by fifteen radix units.
Only its low51 bits are used, so the two subtraction words have equal masks. -/
theorem negative_low_mask (a : BitVec 64) :
    (2251799813684944#64 - a) &&& 2251799813685247#64 =
      (36028797018963664#64 - a) &&& 2251799813685247#64 := by
  have hlow : (2251799813684944#64 - a).setWidth 51 =
      (36028797018963664#64 - a).setWidth 51 := by
    simp only [BitVec.sub_eq_add_neg,
      BitVec.setWidth_add _ _ (by decide : 51 ≤ 64),
      BitVec.setWidth_neg_of_le (by decide : 51 ≤ 64)]
    rfl
  have hleft := BitVec.and_setWidth_allOnes 13 51 (2251799813684944#64 - a)
  have hright := BitVec.and_setWidth_allOnes 13 51 (36028797018963664#64 - a)
  change (2251799813684944#64 - a) &&& 2251799813685247#64 =
    0#13 ++ (2251799813684944#64 - a).setWidth 51 at hleft
  change (36028797018963664#64 - a) &&& 2251799813685247#64 =
    0#13 ++ (36028797018963664#64 - a).setWidth 51 at hright
  exact hleft.trans ((congrArg (fun b : BitVec 51 => 0#13 ++ b) hlow).trans hright.symm)

def zeroWords : Words := fun _ => 0#64

def negativeWords (a : Words) : Words := SerialPoint.subWord zeroWords a

/-- Pure scalar projection of the success block's vectorized negative candidate. -/
def emittedNegativeWords (a : Words) : Words := ![
  ((36028797018963952#64 - a 4) >>> 51) * 19#64 +
    ((2251799813684944#64 - a 0) &&& 2251799813685247#64),
  ((36028797018963664#64 - a 0) >>> 51) +
    ((36028797018963952#64 - a 1) &&& 2251799813685247#64),
  ((36028797018963952#64 - a 1) >>> 51) +
    ((36028797018963952#64 - a 2) &&& 2251799813685247#64),
  ((36028797018963952#64 - a 2) >>> 51) +
    ((36028797018963952#64 - a 3) &&& 2251799813685247#64),
  ((36028797018963952#64 - a 3) >>> 51) +
    ((36028797018963952#64 - a 4) &&& 2251799813685247#64)]

theorem emittedNegativeWords_eq (a : Words) : emittedNegativeWords a = negativeWords a := by
  funext i
  fin_cases i <;>
    simp [emittedNegativeWords, negativeWords, SerialPoint.subWord, SerialPoint.weakWord,
      SerialPoint.biasedSubWord, SerialPoint.bias, zeroWords, negative_low_mask]

theorem zeroWords_bounded : Bounded (unsigned zeroWords) := by
  intro i
  simp [unsigned, zeroWords]

theorem negativeWords_unsigned (a : Words) (ha : Bounded (unsigned a)) :
    unsigned (negativeWords a) = SerialPoint.sub (unsigned zeroWords) (unsigned a) :=
  SerialPoint.subWord_unsigned zeroWords a zeroWords_bounded ha

theorem negativeWords_tight (a : Words) (ha : Bounded (unsigned a)) :
    SerialPoint.Tight (unsigned (negativeWords a)) := by
  rw [negativeWords_unsigned a ha]
  exact (SerialPoint.sub_safe _ _ zeroWords_bounded ha).2.2

theorem negativeWords_value (a : Words) (ha : Bounded (unsigned a)) :
    wordValue (negativeWords a) = -wordValue a := by
  unfold wordValue
  rw [negativeWords_unsigned a ha, SerialPoint.sub_value _ _ ha]
  have hz : SerialPoint.value (unsigned zeroWords) = 0 := by
    simp [SerialPoint.value, decode, unsigned, zeroWords]
  rw [hz, zero_sub]
  rfl

/-- Applying the encoded sign to the even square-root candidate keeps the
caller bound and changes exactly the field sign. -/
def signedWords (flag : Bool) (a : Words) : Words :=
  fun i => selectWord flag (a i) (emittedNegativeWords a i)

theorem signedWords_eq (flag : Bool) (a : Words) :
    signedWords flag a = if flag then negativeWords a else a := by
  funext i
  simp only [signedWords, selectWord_eq, emittedNegativeWords_eq]
  cases flag <;> rfl

theorem signedWords_value (flag : Bool) (a : Words) (ha : Bounded (unsigned a)) :
    wordValue (signedWords flag a) = if flag then -wordValue a else wordValue a := by
  rw [signedWords_eq]
  cases flag <;> simp only [Bool.false_eq_true, ite_false, ite_true, negativeWords_value a ha]

theorem signedWords_tight (flag : Bool) (a : Words)
    (ha : SerialPoint.Tight (unsigned a)) :
    SerialPoint.Tight (unsigned (signedWords flag a)) := by
  rw [signedWords_eq]
  cases flag
  · exact ha
  · exact negativeWords_tight a (SerialPoint.tight_bounded _ ha)

end Agave.Ed25519.Encoding.Decompress.Execution
