import SSA.Projects.Agave.Ed25519.Proof.Avx2FieldMul.Word
import SSA.Projects.RIR.Semantics.Operations.Scalar

/-! Scalar overflow obligations for the actual RIR operation semantics.
These lemmas are intended for the four independent SIMD lanes. -/
namespace Agave.Ed25519.Avx2FieldMul
open LeanMLIR.RIR

theorem rir_mul_nuw (x y : BitVec 64)
    (h : x.toNat * y.toNat < 2 ^ 64) :
    Operation.mul { nuw := true } (.value x) (.value y) = .value (x * y) := by
  have hu : x.umulOverflow y = false := by
    simp only [BitVec.umulOverflow, decide_eq_false_iff_not]
    exact Nat.not_le_of_lt h
  simp [Operation.mul, hu]

theorem rir_add_nuw (x y : BitVec 64)
    (h : x.toNat + y.toNat < 2 ^ 64) :
    Operation.add { nuw := true } (.value x) (.value y) = .value (x + y) := by
  have hu : x.uaddOverflow y = false := by
    simp only [BitVec.uaddOverflow, decide_eq_false_iff_not]
    exact Nat.not_le_of_lt h
  simp [Operation.add, hu]

theorem rir_mul_nsw_nuw (x y : BitVec 64)
    (hx : x.toNat < 2 ^ 63) (hy : y.toNat < 2 ^ 63)
    (h : x.toNat * y.toNat < 2 ^ 63) :
    Operation.mul { nsw := true, nuw := true } (.value x) (.value y) =
      .value (x * y) := by
  have hix : x.toInt = (x.toNat : Int) := BitVec.toInt_eq_toNat_of_lt (by omega)
  have hiy : y.toInt = (y.toNat : Int) := BitVec.toInt_eq_toNat_of_lt (by omega)
  have hi : (x.toNat : Int) * (y.toNat : Int) < 2 ^ 63 := by exact_mod_cast h
  have hlo : ¬ (x.toNat : Int) * (y.toNat : Int) < -(2 ^ 63) := by
    have hp := Int.mul_nonneg (Int.natCast_nonneg x.toNat) (Int.natCast_nonneg y.toNat)
    omega
  have hu : x.umulOverflow y = false := by
    simp only [BitVec.umulOverflow, decide_eq_false_iff_not]
    omega
  have hs : x.smulOverflow y = false := by
    simp only [BitVec.smulOverflow, hix, hiy, Bool.or_eq_false_iff,
      decide_eq_false_iff_not]
    exact ⟨not_le_of_gt hi, hlo⟩
  simp [Operation.mul, hs, hu]

theorem rir_add_nsw_nuw (x y : BitVec 64)
    (h : x.toNat + y.toNat < 2 ^ 63) :
    Operation.add { nsw := true, nuw := true } (.value x) (.value y) =
      .value (x + y) := by
  have hix : x.toInt = (x.toNat : Int) := BitVec.toInt_eq_toNat_of_lt (by omega)
  have hiy : y.toInt = (y.toNat : Int) := BitVec.toInt_eq_toNat_of_lt (by omega)
  have hi : (x.toNat : Int) + (y.toNat : Int) < 2 ^ 63 := by exact_mod_cast h
  have hlo : ¬ (x.toNat : Int) + (y.toNat : Int) < -(2 ^ 63) := by omega
  have hu : x.uaddOverflow y = false := by
    simp only [BitVec.uaddOverflow, decide_eq_false_iff_not]
    omega
  have hs : x.saddOverflow y = false := by
    simp only [BitVec.saddOverflow, hix, hiy, Bool.or_eq_false_iff,
      decide_eq_false_iff_not]
    exact ⟨not_le_of_gt hi, hlo⟩
  simp [Operation.add, hs, hu]

end Agave.Ed25519.Avx2FieldMul
