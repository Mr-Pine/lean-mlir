module
public import Mathlib.Tactic

namespace Agave.Ed25519.SerialFieldMul
@[expose] public section

theorem wide_mul_nooverflow (a b : BitVec 64) :
    (a.setWidth 128).umulOverflow (b.setWidth 128) = false := by
  simp only [BitVec.umulOverflow, BitVec.toNat_setWidth_of_le (by decide : 64 ≤ 128),
    decide_eq_false_iff_not, not_le]
  have := Nat.mul_lt_mul_of_lt_of_lt a.isLt b.isLt
  norm_num at this ⊢
  exact this

theorem final_add_nooverflow (x y : BitVec 64) :
    (x >>> 51).uaddOverflow (y &&& 2251799813685247#64) = false ∧
    (x >>> 51).saddOverflow (y &&& 2251799813685247#64) = false := by
  have hx : (x >>> 51).toNat < 2^13 := by
    have h := x.isLt
    simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    norm_num at h ⊢
    omega
  have hy : (y &&& 2251799813685247#64).toNat < 2^51 := by
    simp only [BitVec.toNat_and, BitVec.toNat_ofNat]
    change y.toNat &&& (2^51-1) < 2^51
    rw [Nat.and_two_pow_sub_one_eq_mod]
    exact Nat.mod_lt _ (by decide)
  have hxi : (x >>> 51).toInt = ((x >>> 51).toNat : Int) :=
    BitVec.toInt_eq_toNat_of_lt (by norm_num at hx ⊢; omega)
  have hyi : (y &&& 2251799813685247#64).toInt =
      ((y &&& 2251799813685247#64).toNat : Int) :=
    BitVec.toInt_eq_toNat_of_lt (by norm_num at hy ⊢; omega)
  constructor
  · simp only [BitVec.uaddOverflow, decide_eq_false_iff_not, not_le]
    norm_num at hx hy ⊢
    omega
  · simp only [BitVec.saddOverflow, hxi, hyi]
    simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_and,
      BitVec.toNat_ofNat] at hx hy ⊢
    norm_num at hx hy ⊢
    omega

end
end Agave.Ed25519.SerialFieldMul
