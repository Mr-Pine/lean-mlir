module

public import Mathlib.Tactic.NormNum
public import SSA.Projects.SLLVM.Dialect

/-!
# Registers that do not wrap

`overflow<none>` reduces away on its own; `nsw`/`nuw` leave a side condition.
One bound on the operands discharges it and makes the register's `toNat` the
exact `ℕ` result.
-/

@[expose] public section

namespace Firedancer

open LeanMLIR SLLVM

theorem toNat_add {w : ℕ} {u v : BitVec w} (h : u.toNat + v.toNat < 2 ^ w) :
    (u + v).toNat = u.toNat + v.toNat := by rw [BitVec.toNat_add, Nat.mod_eq_of_lt h]

theorem toNat_mul {w : ℕ} {u v : BitVec w} (h : u.toNat * v.toNat < 2 ^ w) :
    (u * v).toNat = u.toNat * v.toNat := by rw [BitVec.toNat_mul, Nat.mod_eq_of_lt h]

/-- A 128-bit product of zero-extended 64-bit values never overflows. -/
theorem umulOverflow_zeroExtend (a b : BitVec 64) :
    (BitVec.zeroExtend 128 a).umulOverflow (BitVec.zeroExtend 128 b) = false := by
  have ha : (BitVec.zeroExtend 128 a).toNat = a.toNat := BitVec.toNat_setWidth_of_le (by omega)
  have hb : (BitVec.zeroExtend 128 b).toNat = b.toNat := BitVec.toNat_setWidth_of_le (by omega)
  simp only [BitVec.umulOverflow, ha, hb, ge_iff_le, decide_eq_false_iff_not, not_le]
  calc
    a.toNat * b.toNat < 2 ^ 64 * 2 ^ 64 := Nat.mul_lt_mul_of_lt_of_lt a.isLt b.isLt
    _ = 2 ^ 128 := by norm_num

theorem saddOverflow_eq_false {u v : BitVec 64} (h : u.toNat + v.toNat < 2 ^ 63) :
    u.saddOverflow v = false := by
  have hu : u.toInt = (u.toNat : Int) := BitVec.toInt_eq_toNat_of_lt (by omega)
  have hv : v.toInt = (v.toNat : Int) := BitVec.toInt_eq_toNat_of_lt (by omega)
  simp only [BitVec.saddOverflow, hu, hv, Bool.or_eq_false_iff, decide_eq_false_iff_not, not_le,
    not_lt]
  omega

theorem uaddOverflow_eq_false {u v : BitVec 64} (h : u.toNat + v.toNat < 2 ^ 64) :
    u.uaddOverflow v = false := by
  simp only [BitVec.uaddOverflow, decide_eq_false_iff_not, not_le]
  omega

/-- Both operand bounds are needed: the product bound alone says nothing about
`u` when `v` is zero. -/
theorem smulOverflow_eq_false {u v : BitVec 64} (hu : u.toNat < 2 ^ 63) (hv : v.toNat < 2 ^ 63)
    (h : u.toNat * v.toNat < 2 ^ 63) : u.smulOverflow v = false := by
  have hu' : u.toInt = (u.toNat : Int) := BitVec.toInt_eq_toNat_of_lt (by omega)
  have hv' : v.toInt = (v.toNat : Int) := BitVec.toInt_eq_toNat_of_lt (by omega)
  simp only [BitVec.smulOverflow, hu', hv', Bool.or_eq_false_iff, decide_eq_false_iff_not, not_le,
    not_lt, ← Int.natCast_mul]
  omega

theorem umulOverflow_eq_false {u v : BitVec 64} (h : u.toNat * v.toNat < 2 ^ 64) :
    u.umulOverflow v = false := by
  simp only [BitVec.umulOverflow, decide_eq_false_iff_not, not_le]
  omega

/-- Both guards of an `nsw, nuw` add. -/
theorem add_no_overflow {u v : BitVec 64} (h : u.toNat + v.toNat < 2 ^ 63) :
    u.saddOverflow v = false ∧ u.uaddOverflow v = false :=
  ⟨saddOverflow_eq_false h, uaddOverflow_eq_false (by omega)⟩

end Firedancer
