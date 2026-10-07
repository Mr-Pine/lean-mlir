import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.SignWords

/-! Scalar projections of the two vector arithmetic regions in decoder bb0.
The source's bias/carry network is identified with the proved subtraction
schedule, and the denominator increment retains its exact word representation. -/
namespace Agave.Ed25519.Encoding.Decompress.Execution.Decode
open SerialFieldMul

def oneLimbs : Words := ![1#64, 0#64, 0#64, 0#64, 0#64]

def numeratorBias (a : Words) : Words := ![
  a 0 + 36028797018963663#64,
  a 1 + 36028797018963952#64,
  a 2 + 36028797018963952#64,
  a 3 + 36028797018963952#64,
  a 4 + 36028797018963952#64]

/-- The exact output of the emitted numerator carry network. -/
def numeratorMachine (a : Words) : Words := SerialPoint.weakWord (numeratorBias a)

theorem numeratorBias_eq (a : Words) :
    numeratorBias a = SerialPoint.biasedSubWord a oneLimbs := by
  have hzero : ∀ x : BitVec 64, x + 36028797018963663#64 =
      x + 36028797018963664#64 - 1#64 := by
    intro x
    rw [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  funext i
  fin_cases i <;> simp [numeratorBias, SerialPoint.biasedSubWord,
    SerialPoint.bias, oneLimbs, hzero]

theorem numeratorMachine_eq (a : Words) :
    numeratorMachine a = SerialPoint.subWord a oneLimbs := by
  rw [numeratorMachine, numeratorBias_eq]
  rfl

theorem oneLimbs_bounded : Bounded (unsigned oneLimbs) := by
  intro i
  fin_cases i <;> decide

theorem oneLimbs_value : wordValue oneLimbs = 1 := by
  norm_num [oneLimbs, wordValue, SerialPoint.value, decode, unsigned]
  rfl

theorem numeratorMachine_value (a : Words) (ha : Bounded (unsigned a)) :
    wordValue (numeratorMachine a) = wordValue a - 1 := by
  rw [numeratorMachine_eq]
  have heq : wordValue (SerialPoint.subWord a oneLimbs) =
      wordValue a - wordValue oneLimbs := by
    unfold wordValue
    rw [SerialPoint.subWord_unsigned _ _ ha oneLimbs_bounded,
      SerialPoint.sub_value _ _ oneLimbs_bounded]
    rfl
  rw [heq, oneLimbs_value]

theorem numeratorMachine_tight (a : Words) (ha : Bounded (unsigned a)) :
    SerialPoint.Tight (unsigned (numeratorMachine a)) := by
  rw [numeratorMachine_eq, SerialPoint.subWord_unsigned _ _ ha oneLimbs_bounded]
  exact (SerialPoint.sub_safe _ _ ha oneLimbs_bounded).2.2

/-- The source adds [1,0] to the first vector and copies all remaining limbs. -/
def denominatorMachine (a : Words) : Words := ![a 0 + 1#64, a 1, a 2, a 3, a 4]

theorem denominatorMachine_eq (a : Words) :
    denominatorMachine a = SerialPoint.addWord a oneLimbs := by
  funext i
  fin_cases i <;> simp [denominatorMachine, SerialPoint.addWord, oneLimbs]

theorem denominatorMachine_value (a : Words) (ha : Bounded (unsigned a)) :
    wordValue (denominatorMachine a) = wordValue a + 1 := by
  rw [denominatorMachine_eq]
  have heq : wordValue (SerialPoint.addWord a oneLimbs) =
      wordValue a + wordValue oneLimbs := by
    unfold wordValue
    rw [SerialPoint.addWord_unsigned _ _ ha oneLimbs_bounded, SerialPoint.add_value]
    rfl
  rw [heq, oneLimbs_value]

/-- The stronger multiplication bound on limb zero justifies the increment. -/
theorem denominatorMachine_tight (a : Words)
    (ha : SerialPoint.Tight (unsigned a)) (hzero : (a 0).toNat < 2 ^ 51) :
    SerialPoint.Tight (unsigned (denominatorMachine a)) := by
  intro i
  fin_cases i
  · change (a 0 + 1#64).toNat < 2 ^ 52
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reduceMod]
    omega
  · exact ha 1
  · exact ha 2
  · exact ha 3
  · exact ha 4

end Agave.Ed25519.Encoding.Decompress.Execution.Decode
