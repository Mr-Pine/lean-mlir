import SSA.Projects.Agave.Ed25519.Proof.Avx2PointAdd.Refinement

/-! Arithmetic specification of the constructor's inline cached conversion.
The exact instruction-to-arithmetic connection is a separate obligation; none
of the theorems below asserts execution of the table constructor. -/
namespace Agave.Ed25519.Tables.Avx2Constructor.CacheArithmetic
open Avx2PointAdd PointArithmetic
abbrev Limbs := Avx2FieldMul.Limbs

def scaleColumns (c : Nat) (a : Limbs) : Limbs := fun i => c * a i
def scaleReduce (c : Nat) (a : Limbs) : Limbs := Reduce64.reduce (scaleColumns c a)

/-- The coefficient constants used by the five SIMD subtractions: 16p. -/
def sixteenP (i : Fin 10) : Nat :=
  if i = 0 then 1073741520 else if i.val % 2 = 0 then 1073741808 else 536870896

def negateColumns (a : Limbs) : Limbs := fun i => sixteenP i - a i

/-- The constructor propagates each incoming 32-bit carry once, in parallel. -/
def carry32 (z : Limbs) : Limbs := ![
  z 0 % 2^26 + 19 * (z 9 / 2^25),
  z 1 % 2^25 + z 0 / 2^26,
  z 2 % 2^26 + z 1 / 2^25,
  z 3 % 2^25 + z 2 / 2^26,
  z 4 % 2^26 + z 3 / 2^25,
  z 5 % 2^25 + z 4 / 2^26,
  z 6 % 2^26 + z 5 / 2^25,
  z 7 % 2^25 + z 6 / 2^26,
  z 8 % 2^26 + z 7 / 2^25,
  z 9 % 2^25 + z 8 / 2^26]

def negateReduce (a : Limbs) : Limbs := carry32 (negateColumns a)

theorem scaleColumns_bound (c : Nat) (hc : c ≤ 243332) {a : Limbs}
    (ha : wide a) : Reduce64.ColumnsBound (scaleColumns c a) := by
  intro i
  have hi := ha i
  have hm := Nat.mul_le_mul hc hi
  unfold scaleColumns
  unfold wideCap at hm
  split_ifs at hm <;> norm_num at hm ⊢ <;> omega

theorem scaleReduce_reduced (c : Nat) (hc : c ≤ 243332) {a : Limbs}
    (ha : wide a) : reduced (scaleReduce c a) := by
  intro i
  exact Reduce64.output_bounds _ (scaleColumns_bound c hc ha) i

theorem value_scaleColumns (c : Nat) (a : Limbs) :
    value (scaleColumns c a) = (c : K) * value a := by
  simp only [value, scaleColumns, Field.decode10, ← Finset.mul_sum, Nat.mul_assoc,
    Nat.cast_mul]

theorem value_scaleReduce (c : Nat) (a : Limbs) :
    value (scaleReduce c a) = (c : K) * value a := by
  have h := Reduce64.residue (scaleColumns c a)
  have he : value (scaleReduce c a) = value (scaleColumns c a) := by
    exact ((ZMod.natCast_eq_natCast_iff' _ _ _).mpr h).symm
  exact he.trans (value_scaleColumns c a)

theorem sixteenP_decode : Field.decode10 sixteenP = 16 * Field.p := by
  norm_num [Field.decode10, Field.exponent, sixteenP, Field.p, Fin.sum_univ_succ]

theorem reduced_le_sixteenP {a : Limbs} (ha : reduced a) (i : Fin 10) :
    a i ≤ sixteenP i := by
  have h := ha i
  unfold radix sixteenP at *
  split_ifs at * <;> norm_num at * <;> omega

theorem negateColumns_conservation {a : Limbs} (ha : reduced a) :
    Field.decode10 (negateColumns a) + Field.decode10 a = 16 * Field.p := by
  rw [← sixteenP_decode]
  unfold Field.decode10
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Nat.add_mul]
  congr 1
  exact Nat.sub_add_cancel (reduced_le_sixteenP ha i)

theorem value_negateColumns {a : Limbs} (ha : reduced a) :
    value (negateColumns a) = -value a := by
  have h := congrArg (fun n : Nat => (n : K)) (negateColumns_conservation ha)
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, ZMod.natCast_self,
    mul_zero] at h
  exact eq_neg_iff_add_eq_zero.mpr h

/-- Exact carry accounting, before reducing modulo the field prime. -/
theorem carry32_conservation (z : Limbs) :
    Field.decode10 z + (z 9 / 2^25) * 19 =
      Field.decode10 (carry32 z) + (z 9 / 2^25) * 2^255 := by
  have h0 := Nat.mod_add_div (z 0) (2^26)
  have h1 := Nat.mod_add_div (z 1) (2^25)
  have h2 := Nat.mod_add_div (z 2) (2^26)
  have h3 := Nat.mod_add_div (z 3) (2^25)
  have h4 := Nat.mod_add_div (z 4) (2^26)
  have h5 := Nat.mod_add_div (z 5) (2^25)
  have h6 := Nat.mod_add_div (z 6) (2^26)
  have h7 := Nat.mod_add_div (z 7) (2^25)
  have h8 := Nat.mod_add_div (z 8) (2^26)
  have h9 := Nat.mod_add_div (z 9) (2^25)
  simp only [Field.decode10, Field.exponent, carry32, Fin.sum_univ_succ,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.val_zero, Fin.val_succ]
  norm_num at *
  omega

theorem value_carry32 (z : Limbs) : value (carry32 z) = value z := by
  have h := carry32_conservation z
  rw [Field.two_pow_255] at h
  have he : Field.decode10 z = Field.decode10 (carry32 z) + (z 9 / 2^25) * Field.p := by
    nlinarith [h]
  unfold value
  rw [he]
  simp

theorem value_negateReduce {a : Limbs} (ha : reduced a) :
    value (negateReduce a) = -value a := by
  rw [negateReduce, value_carry32, value_negateColumns ha]

theorem negateColumns_bound (a : Limbs) (i : Fin 10) :
    negateColumns a i < 16 * radix i := by
  have h : sixteenP i - a i ≤ sixteenP i := Nat.sub_le _ _
  unfold negateColumns sixteenP radix at *
  split_ifs at * <;> norm_num at * <;> omega

theorem negateReduce_reduced (a : Limbs) : reduced (negateReduce a) := by
  intro i
  have h0 := negateColumns_bound a 0
  have h1 := negateColumns_bound a 1
  have h2 := negateColumns_bound a 2
  have h3 := negateColumns_bound a 3
  have h4 := negateColumns_bound a 4
  have h5 := negateColumns_bound a 5
  have h6 := negateColumns_bound a 6
  have h7 := negateColumns_bound a 7
  have h8 := negateColumns_bound a 8
  have h9 := negateColumns_bound a 9
  unfold radix at *
  fin_cases i <;> simp only [negateReduce, carry32, Matrix.cons_val_zero,
    Matrix.cons_val_succ, Fin.val_zero, Fin.val_succ]
  all_goals norm_num at *
  all_goals omega

/-- The four constant multiplications and the independently reduced D negation. -/
def cache (P : Point) : Point :=
  let Q := prepare P
  ⟨scaleReduce 121666 Q.X, scaleReduce 121666 Q.Y,
    scaleReduce 243332 Q.Z, negateReduce (scaleReduce 243330 Q.T)⟩

theorem cache_reduced {P : Point} (hP : pointReduced P) : pointReduced (cache P) := by
  have h := prepare_wide hP
  exact ⟨scaleReduce_reduced 121666 (by decide) h.1,
    scaleReduce_reduced 121666 (by decide) h.2.1,
    scaleReduce_reduced 243332 (by decide) h.2.2.1,
    negateReduce_reduced _⟩

/-- Field-level cached conversion including its exact scale and D sign. -/
theorem cache_value {P : Point} (hP : pointReduced P) :
    pointValue (cache P) = avx2Cache (pointValue P) := by
  have h := prepare_wide hP
  have ht : reduced (scaleReduce 243330 P.T) :=
    scaleReduce_reduced 243330 (by decide) h.2.2.2
  ext <;> simp [pointValue, cache, prepare, avx2Cache, value_scaleReduce,
    value_negateReduce ht, value_lazyDiff hP.1, value_lazySum] <;> ring

end Agave.Ed25519.Tables.Avx2Constructor.CacheArithmetic
