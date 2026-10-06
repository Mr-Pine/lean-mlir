import SSA.Projects.Agave.Ed25519.Proof.Avx2PointDouble.Arithmetic
import Mathlib.Data.ZMod.Basic

/-! Algebraic refinement of the coefficient schedule. The theorem here does
not replace the separately required execution of the five RIR observations. -/
namespace Agave.Ed25519.Avx2PointDouble

abbrev K := ZMod Field.p

def value (a : Limbs) : K := (Field.decode10 a : K)
def values (p : Coordinates) : PointArithmetic.Extended K :=
  ⟨value (p 0), value (p 1), value (p 2), value (p 3)⟩

theorem value_add (a b : Limbs) :
    value (fun i => a i + b i) = value a + value b := by
  simp only [value, Field.decode10, Nat.cast_sum, Nat.cast_mul, Nat.cast_add]
  simp only [add_mul, Finset.sum_add_distrib]

theorem value_twice (a : Limbs) : value (fun i => 2 * a i) = 2 * value a := by
  simp only [value, Field.decode10, Nat.cast_sum, Nat.cast_mul, Nat.cast_ofNat,
    mul_assoc, ← Finset.mul_sum]

theorem decode_twoP : Field.decode10 twoP = 2 * Field.p := by
  norm_num [Field.decode10, Field.exponent, twoP, radix, Field.p, Fin.sum_univ_succ]

theorem value_twoP : value twoP = 0 := by
  simp [value, decode_twoP]

theorem value_negate_lazy {a : Limbs} (ha : Reduced a) :
    value (fun i => twoP i - a i) = -value a := by
  have h : value (fun i => (twoP i - a i) + a i) = 0 := by
    have he : (fun i => (twoP i - a i) + a i) = twoP := by
      funext i
      exact Nat.sub_add_cancel (reduced_le_twoP ha i)
    rw [he, value_twoP]
  rw [value_add] at h
  exact eq_neg_of_add_eq_zero_left h

theorem value_product (a b : Limbs) :
    value (Avx2FieldMul.product a b) = value a * value b := by
  have h := congrArg (fun n : Nat => (n : K)) (Avx2FieldMul.product_mod a b)
  simpa only [ZMod.natCast_mod, Nat.cast_mul, value] using h

theorem value_square (a : Limbs) :
    value (Avx2SquareNegateD.output a false) = value a ^ 2 := by
  have h := congrArg (fun n : Nat => (n : K)) (Avx2SquareNegateD.square_result a)
  simpa only [Avx2SquareNegateD.decode_eq_decode10,
    (show Avx2SquareNegateD.modulus = Field.p from rfl), ZMod.natCast_mod,
    Nat.cast_pow, value] using h

theorem value_negative_square {a : Limbs} (ha : Avx2SquareNegateD.Bounded a) :
    value (Avx2SquareNegateD.output a true) = -(value a ^ 2) := by
  have h := congrArg (fun n : Nat => (n : K))
    (Avx2SquareNegateD.negative_square_result ha)
  have hz : value (Avx2SquareNegateD.output a true) + value a ^ 2 = 0 := by
    simpa only [Avx2SquareNegateD.decode_eq_decode10,
      (show Avx2SquareNegateD.modulus = Field.p from rfl), ZMod.natCast_mod,
      Nat.cast_add, Nat.cast_pow, Nat.cast_zero, value] using h
  exact eq_neg_of_add_eq_zero_left hz

theorem squareStage_values {p : Coordinates} (hp : PointBound p) :
    values (squareStage p) =
      ⟨(value (p 0))^2, (value (p 1))^2, (value (p 2))^2,
        -(value (p 0) + value (p 1))^2⟩ := by
  ext <;> simp only [values, squareStage, prepare, Matrix.cons_val]
  · exact value_square _
  · exact value_square _
  · exact value_square _
  · change value (Avx2SquareNegateD.output (prepare p 3) true) = _
    rw [value_negative_square (prepare_bounded hp 3)]
    change -(value (fun i => p 0 i + p 1 i)) ^ 2 = _
    rw [value_add]

theorem mix_values {q : Coordinates} (hq : PointBound q) :
    values (mix q) =
      ⟨value (q 0) + value (q 1), value (q 0) - value (q 1),
       value (q 0) + 2 * value (q 2) - value (q 1),
       value (q 0) + value (q 1) + value (q 3)⟩ := by
  ext <;> simp only [values, mix, Matrix.cons_val]
  · exact value_add _ _
  · rw [value_add, value_negate_lazy (hq 1), sub_eq_add_neg]
  · rw [value_add, value_add, value_twice, value_negate_lazy (hq 1), sub_eq_add_neg]
  · rw [value_add, value_add]

private def mixValues {F : Type} [CommRing F]
    (q : PointArithmetic.Extended F) : PointArithmetic.Extended F :=
  ⟨q.X + q.Y, q.X - q.Y, q.X + 2 * q.Z - q.Y, q.X + q.Y + q.T⟩

private def multiplyValues {F : Type} [CommRing F]
    (q : PointArithmetic.Extended F) : PointArithmetic.Extended F :=
  ⟨q.Z * q.T, q.X * q.Y, q.Z * q.Y, q.X * q.T⟩

private theorem product_values (q : Coordinates) :
    values (fun e => Avx2FieldMul.product (left q e) (right q e)) =
      multiplyValues (values (mix q)) := by
  ext <;> simp only [values, left, right, Matrix.cons_val,
    value_product, multiplyValues]

private theorem mixValues_square {F : Type} [CommRing F]
    (p : PointArithmetic.Extended F) :
    multiplyValues (mixValues ⟨p.X ^ 2, p.Y ^ 2, p.Z ^ 2, -(p.X + p.Y) ^ 2⟩) =
      PointArithmetic.avx2Double p := by
  ext <;> simp only [multiplyValues, mixValues, PointArithmetic.avx2Double,
    sub_eq_add_neg, add_assoc, add_comm, add_left_comm]

/-- Field interpretation of the whole natural-coefficient schedule agrees
with the independently stated AVX2 point formula. -/
theorem output_values {p : Coordinates} (hp : PointBound p) :
    values (output p) = PointArithmetic.avx2Double (values p) := by
  have hm : values (mix (squareStage p)) = mixValues (values (squareStage p)) :=
    mix_values (squareStage_bounded hp)
  calc
    values (output p) = multiplyValues (values (mix (squareStage p))) :=
      product_values (squareStage p)
    _ = multiplyValues (mixValues (values (squareStage p))) := congrArg multiplyValues hm
    _ = multiplyValues (mixValues
        ⟨(value (p 0))^2, (value (p 1))^2, (value (p 2))^2,
          -(value (p 0) + value (p 1))^2⟩) := by rw [squareStage_values hp]
    _ = PointArithmetic.avx2Double (values p) := mixValues_square (values p)

/-- The final scaling difference is exactly -1, as required for the serial
and AVX2 double-base loops to represent the same point. -/
theorem output_values_serial {p : Coordinates} (hp : PointBound p) :
    values (output p) = PointArithmetic.scale (-1)
      (PointArithmetic.serialDouble (values p)) := by
  rw [output_values hp, PointArithmetic.avx2Double_eq_scale_serialDouble]

end Agave.Ed25519.Avx2PointDouble
