import SSA.Projects.Agave.Ed25519.Proof.Avx2PointAdd.Bounds
import SSA.Projects.RIR.Semantics.Operations.Scalar

/-! Scalar projections of the unflagged i32 add/sub instructions implementing
`negate_lazy` and `diff_sum`. These discharge arithmetic/poison obligations;
the physical vector instruction scheduling is proved separately. -/
namespace Agave.Ed25519.Avx2PointAdd
open Avx2FieldMul LeanMLIR.RIR

def word (x : Nat) : BitVec 32 := BitVec.ofNat 32 x

theorem reduced_lt_u32 {a : Limbs} (ha : reduced a) (i : Fin 10) : a i < 2^32 := by
  have h := (wide_input_safety (reduced_wide ha) i).1
  omega

theorem lazyNeg_word {a : Limbs} (ha : reduced a) (i : Fin 10) :
    word (twiceP i) - word (a i) = word (lazyNeg a i) :=
  BitVec.ofNat_sub_ofNat_of_le _ _ (reduced_lt_u32 ha i) (reduced_le_twiceP ha i)

theorem lazyDiff_word {a b : Limbs} (ha : reduced a) (i : Fin 10) :
    word (b i) + (word (twiceP i) - word (a i)) = word (lazyDiff a b i) := by
  rw [lazyNeg_word ha]
  exact (BitVec.ofNat_add _ _).symm

theorem lazySum_word (a b : Limbs) (i : Fin 10) :
    word (b i) + word (a i) = word (lazySum a b i) := by
  exact (BitVec.ofNat_add _ _).symm

theorem lazyDiff_word_toNat {a b : Limbs} (ha : reduced a) (hb : reduced b) (i : Fin 10) :
    (word (b i) + (word (twiceP i) - word (a i))).toNat = lazyDiff a b i := by
  rw [lazyDiff_word ha]
  exact Nat.mod_eq_of_lt (preparations_safe ha hb i).2.1

theorem lazySum_word_toNat {a b : Limbs} (ha : reduced a) (hb : reduced b) (i : Fin 10) :
    (word (b i) + word (a i)).toNat = lazySum a b i := by
  rw [lazySum_word]
  exact Nat.mod_eq_of_lt (preparations_safe ha hb i).2.2

/-- The actual RIR unflagged subtraction is non-poison for every tight input. -/
theorem rir_lazyNeg {a : Limbs} (ha : reduced a) (i : Fin 10) :
    Operation.sub {} (.value (word (twiceP i))) (.value (word (a i))) =
      .value (word (lazyNeg a i)) := by
  simp [Operation.sub, lazyNeg_word ha]

/-- The actual RIR unflagged additions produce the exact natural sums. -/
theorem rir_lazyDiff {a b : Limbs} (ha : reduced a) (i : Fin 10) :
    Operation.add {} (.value (word (b i)))
      (Operation.sub {} (.value (word (twiceP i))) (.value (word (a i)))) =
      .value (word (lazyDiff a b i)) := by
  rw [rir_lazyNeg ha]
  simp [Operation.add, word, ← BitVec.ofNat_add, lazyDiff]

theorem rir_lazySum (a b : Limbs) (i : Fin 10) :
    Operation.add {} (.value (word (b i))) (.value (word (a i))) =
      .value (word (lazySum a b i)) := by
  simp [Operation.add, lazySum_word]

end Agave.Ed25519.Avx2PointAdd
