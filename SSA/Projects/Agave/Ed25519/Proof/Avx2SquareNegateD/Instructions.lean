import SSA.Projects.RIR.Run.Vector
import Mathlib.Tactic.NormNum

/-! The overflow flags introduced by LLVM for unsigned widening products.
These lemmas are unconditional in the original u32 operands. -/

namespace Agave.Ed25519.Avx2SquareNegateD
open LeanMLIR.RIR
section

theorem wide_toNat (x : BitVec 32) : (x.setWidth 64).toNat = x.toNat := by
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt]
  exact lt_trans x.isLt (by norm_num)

theorem wide_product_lt (x y : BitVec 32) : x.toNat * y.toNat < 2^64 := by
  calc
    x.toNat * y.toNat ≤ (2^32-1)*(2^32-1) :=
      Nat.mul_le_mul (by have := x.isLt; omega) (by have := y.isLt; omega)
    _ < 2^64 := by norm_num

/-- LLVM's `mul nuw` is total when both inputs are zero-extended u32s. -/
theorem mul_wide_value (x y : BitVec 32) :
    Operation.mul {nuw := true} (.value (x.setWidth 64)) (.value (y.setWidth 64)) =
      .value (x.setWidth 64 * y.setWidth 64) := by
  have hu : (x.setWidth 64).umulOverflow (y.setWidth 64) = false := by
    simp only [BitVec.umulOverflow, wide_toNat, decide_eq_false_iff_not]
    exact Nat.not_le_of_lt (wide_product_lt x y)
  simp [Operation.mul, hu]

/-- The `19*x` preparation is also within the signed 64-bit range. -/
theorem mul19_wide_value (x : BitVec 32) :
    Operation.mul {nsw := true, nuw := true} (.value (x.setWidth 64)) (.value 19#64) =
      .value (x.setWidth 64 * 19#64) := by
  have hx := x.isLt
  have hsign : (x.setWidth 64).toInt = (x.toNat : Int) := by
    rw [BitVec.toInt_eq_toNat_of_lt, wide_toNat]
    rw [wide_toNat]
    norm_num at hx ⊢
    omega
  have hu : (x.setWidth 64).umulOverflow 19#64 = false := by
    simp only [BitVec.umulOverflow, wide_toNat, BitVec.toNat_ofNat, decide_eq_false_iff_not]
    norm_num at hx ⊢
    omega
  have hs : (x.setWidth 64).smulOverflow 19#64 = false := by
    simp only [BitVec.smulOverflow, hsign, Bool.or_eq_false_iff,
      decide_eq_false_iff_not]
    norm_num at hx ⊢
    omega
  simp [Operation.mul, hs, hu]

end
end Agave.Ed25519.Avx2SquareNegateD
