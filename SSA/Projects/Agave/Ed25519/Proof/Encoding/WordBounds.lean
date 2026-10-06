import SSA.Projects.RIR.Semantics.Operations.Scalar
import Mathlib.Tactic

namespace Agave.Ed25519.Encoding.RIR

theorem add_nat_le (x y : BitVec 64) : (x+y).toNat ≤ x.toNat + y.toNat := by
  rw [BitVec.toNat_add]
  exact Nat.mod_le _ _

theorem mul_nat_le (x y : BitVec 64) : (x*y).toNat ≤ x.toNat * y.toNat := by
  rw [BitVec.toNat_mul]
  exact Nat.mod_le _ _

theorem and_nat_le_right (x y : BitVec 64) : (x &&& y).toNat ≤ y.toNat := by
  rw [BitVec.toNat_and]
  exact Nat.and_le_right

theorem shiftRight_bound (x : BitVec 64) (k bound : Nat) (hx : x.toNat ≤ bound) :
    (x >>> k).toNat ≤ bound / 2^k := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  exact Nat.div_le_div_right hx

theorem shiftLeft_bound (x : BitVec 64) (k bound : Nat) (hx : x.toNat ≤ bound) :
    (x <<< k).toNat ≤ bound * 2^k := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  exact (Nat.mod_le _ _).trans (Nat.mul_le_mul_right _ hx)

theorem or_bound (x y : BitVec 64) (bits : Nat)
    (hx : x.toNat < 2^bits) (hy : y.toNat < 2^bits) :
    (x ||| y).toNat ≤ 2^bits - 1 := by
  rw [BitVec.toNat_or]
  exact Nat.le_pred_of_lt (Nat.or_lt_two_pow hx hy)

theorem add_safe_of_bound (x y : BitVec 64) (a b : Nat)
    (hx : x.toNat ≤ a) (hy : y.toNat ≤ b) (hbound : a+b < 2^63) :
    x.saddOverflow y = false ∧ x.uaddOverflow y = false := by
  have hsum : x.toNat + y.toNat < 2^63 :=
    lt_of_le_of_lt (Nat.add_le_add hx hy) hbound
  have hxi := BitVec.toInt_eq_toNat_of_lt (x := x) (by norm_num at *; omega)
  have hyi := BitVec.toInt_eq_toNat_of_lt (x := y) (by norm_num at *; omega)
  simp only [BitVec.saddOverflow, BitVec.uaddOverflow, hxi, hyi,
    Bool.or_eq_false_iff, decide_eq_false_iff_not]
  norm_num at *
  omega

theorem mul_safe_of_bound (x y : BitVec 64) (a b : Nat)
    (hx : x.toNat ≤ a) (hy : y.toNat ≤ b)
    (ha : a < 2^63) (hb : b < 2^63) (hbound : a*b < 2^63) :
    x.smulOverflow y = false ∧ x.umulOverflow y = false := by
  have hmul : x.toNat * y.toNat < 2^63 :=
    lt_of_le_of_lt (Nat.mul_le_mul hx hy) hbound
  have hxi := BitVec.toInt_eq_toNat_of_lt (x := x) (by norm_num at *; omega)
  have hyi := BitVec.toInt_eq_toNat_of_lt (x := y) (by norm_num at *; omega)
  have hmulZ : (x.toNat : Int) * (y.toNat : Int) < 2^63 := by exact_mod_cast hmul
  have hnonneg : 0 ≤ (x.toNat : Int) * (y.toNat : Int) :=
    mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)
  simp only [BitVec.smulOverflow, BitVec.umulOverflow, hxi, hyi,
    Bool.or_eq_false_iff, decide_eq_false_iff_not]
  norm_num at *
  omega

theorem shift_unsigned_safe (x : BitVec 64) (k bound : Nat)
    (hx : x.toNat ≤ bound) (hbound : bound * 2^k < 2^64) :
    (x <<< k) >>> k = x := by
  have hm : x.toNat * 2^k < 2^64 :=
    lt_of_le_of_lt (Nat.mul_le_mul_right _ hx) hbound
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft,
    Nat.shiftLeft_eq, Nat.mod_eq_of_lt hm, Nat.shiftRight_eq_div_pow,
    Nat.mul_div_left _ (Nat.two_pow_pos _)]

theorem shift_signed_safe (x : BitVec 64) (k bound : Nat)
    (hx : x.toNat ≤ bound) (hbound : bound * 2^k < 2^63) :
    (x <<< k).sshiftRight k = x := by
  have hm : x.toNat * 2^k < 2^63 :=
    lt_of_le_of_lt (Nat.mul_le_mul_right _ hx) hbound
  have hm64 : x.toNat * 2^k < 2^64 := lt_trans hm (by decide)
  have hnat : (x <<< k).toNat = x.toNat * 2^k := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mod_eq_of_lt hm64]
  have hmsb : (x <<< k).msb = false := by
    rw [BitVec.msb_eq_false_iff_two_mul_lt, hnat]
    norm_num at hm ⊢
    omega
  rw [BitVec.sshiftRight_eq_of_msb_false hmsb]
  apply shift_unsigned_safe x k bound hx
  norm_num at hbound ⊢
  omega

end Agave.Ed25519.Encoding.RIR
