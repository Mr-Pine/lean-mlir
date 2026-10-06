import Mathlib.Tactic.NormNum
import SSA.Projects.Agave.Ed25519.Proof.Reduce64.Words

namespace Agave.Ed25519.Reduce64

private theorem add_flags (x y : BitVec 64)
    (hx : x.toNat < 2^62) (hy : y.toNat < 2^62) :
    x.saddOverflow y = false ∧ x.uaddOverflow y = false := by
  have hxi := BitVec.toInt_eq_toNat_of_lt (x := x) (by norm_num at hx ⊢; omega)
  have hyi := BitVec.toInt_eq_toNat_of_lt (x := y) (by norm_num at hy ⊢; omega)
  simp only [BitVec.saddOverflow, BitVec.uaddOverflow, hxi, hyi]
  norm_num at hx hy ⊢
  omega

private theorem mul19_flags (x : BitVec 64) (hx : x.toNat < 2^40) :
    x.smulOverflow 19#64 = false ∧ x.umulOverflow 19#64 = false := by
  have hxi := BitVec.toInt_eq_toNat_of_lt (x := x) (by norm_num at hx ⊢; omega)
  simp only [BitVec.smulOverflow, BitVec.umulOverflow, hxi]
  norm_num at hx ⊢
  omega

/-! The compiler marks only these small carry and mask operations `nsw nuw`.
Their safety does not need input bounds: the preceding unflagged additions
may wrap, but each of these lemmas accepts arbitrary 64-bit operands.
Residue preservation separately requires `ColumnsBound`. -/

theorem carry_mask26_flags (x y : BitVec 64) :
    (x >>> 25).saddOverflow (y &&& 67108863#64) = false ∧
    (x >>> 25).uaddOverflow (y &&& 67108863#64) = false := by
  apply add_flags
  all_goals have hx := x.isLt
  all_goals have hy := y.isLt
  all_goals have hml := Nat.mod_le ((x.toNat / 2^25 % 2^26) * 19) (2^64)
  all_goals have hmh := Nat.mod_le ((x.toNat / 2^51) * 19) (2^64)
  all_goals have hsum := Nat.mod_le ((x.toNat / 2^51 * 19) % 2^64 + y.toNat % 2^25) (2^64)
  all_goals have hsum' := Nat.mod_le ((x.toNat / 2^51 * 19) + y.toNat % 2^25) (2^64)
  all_goals simp only [BitVec.toNat_add, BitVec.toNat_mul, Word.mask26_toNat,
    Word.mask25_toNat, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  all_goals norm_num at *
  all_goals omega

theorem carry_mask25_flags (x y : BitVec 64) :
    (x >>> 26).saddOverflow (y &&& 33554431#64) = false ∧
    (x >>> 26).uaddOverflow (y &&& 33554431#64) = false := by
  apply add_flags
  all_goals have hx := x.isLt
  all_goals have hy := y.isLt
  all_goals have hml := Nat.mod_le ((x.toNat / 2^25 % 2^26) * 19) (2^64)
  all_goals have hmh := Nat.mod_le ((x.toNat / 2^51) * 19) (2^64)
  all_goals have hsum := Nat.mod_le ((x.toNat / 2^51 * 19) % 2^64 + y.toNat % 2^25) (2^64)
  all_goals have hsum' := Nat.mod_le ((x.toNat / 2^51 * 19) + y.toNat % 2^25) (2^64)
  all_goals simp only [BitVec.toNat_add, BitVec.toNat_mul, Word.mask26_toNat,
    Word.mask25_toNat, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  all_goals norm_num at *
  all_goals omega

theorem low_mul19_flags (x : BitVec 64) :
    ((x >>> 25) &&& 67108863#64).smulOverflow 19#64 = false ∧
    ((x >>> 25) &&& 67108863#64).umulOverflow 19#64 = false := by
  apply mul19_flags
  simp only [Word.mask26_toNat]
  omega

theorem high_mul19_flags (x : BitVec 64) :
    (x >>> 51).smulOverflow 19#64 = false ∧
    (x >>> 51).umulOverflow 19#64 = false := by
  apply mul19_flags
  have hx := x.isLt
  simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  norm_num at *
  omega

theorem low_fold_flags (x y : BitVec 64) :
    (((x >>> 25) &&& 67108863#64) * 19#64).saddOverflow (y &&& 67108863#64) = false ∧
    (((x >>> 25) &&& 67108863#64) * 19#64).uaddOverflow (y &&& 67108863#64) = false := by
  apply add_flags
  all_goals have hx := x.isLt
  all_goals have hy := y.isLt
  all_goals have hml := Nat.mod_le ((x.toNat / 2^25 % 2^26) * 19) (2^64)
  all_goals have hmh := Nat.mod_le ((x.toNat / 2^51) * 19) (2^64)
  all_goals have hsum := Nat.mod_le ((x.toNat / 2^51 * 19) % 2^64 + y.toNat % 2^25) (2^64)
  all_goals have hsum' := Nat.mod_le ((x.toNat / 2^51 * 19) + y.toNat % 2^25) (2^64)
  all_goals simp only [BitVec.toNat_add, BitVec.toNat_mul, Word.mask26_toNat,
    Word.mask25_toNat, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  all_goals norm_num at *
  all_goals omega

theorem high_fold_flags (x y : BitVec 64) :
    ((x >>> 51) * 19#64).saddOverflow (y &&& 33554431#64) = false ∧
    ((x >>> 51) * 19#64).uaddOverflow (y &&& 33554431#64) = false := by
  apply add_flags
  all_goals have hx := x.isLt
  all_goals have hy := y.isLt
  all_goals have hml := Nat.mod_le ((x.toNat / 2^25 % 2^26) * 19) (2^64)
  all_goals have hmh := Nat.mod_le ((x.toNat / 2^51) * 19) (2^64)
  all_goals have hsum := Nat.mod_le ((x.toNat / 2^51 * 19) % 2^64 + y.toNat % 2^25) (2^64)
  all_goals have hsum' := Nat.mod_le ((x.toNat / 2^51 * 19) + y.toNat % 2^25) (2^64)
  all_goals simp only [BitVec.toNat_add, BitVec.toNat_mul, Word.mask26_toNat,
    Word.mask25_toNat, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  all_goals norm_num at *
  all_goals omega

theorem final_carry_flags (x y z : BitVec 64) :
    (((x >>> 51) * 19#64) + (y &&& 33554431#64)).saddOverflow (z >>> 26) = false ∧
    (((x >>> 51) * 19#64) + (y &&& 33554431#64)).uaddOverflow (z >>> 26) = false := by
  apply add_flags
  all_goals have hx := x.isLt
  all_goals have hy := y.isLt
  all_goals have hml := Nat.mod_le ((x.toNat / 2^25 % 2^26) * 19) (2^64)
  all_goals have hmh := Nat.mod_le ((x.toNat / 2^51) * 19) (2^64)
  all_goals have hsum := Nat.mod_le ((x.toNat / 2^51 * 19) % 2^64 + y.toNat % 2^25) (2^64)
  all_goals have hsum' := Nat.mod_le ((x.toNat / 2^51 * 19) + y.toNat % 2^25) (2^64)
  all_goals have hz := z.isLt
  all_goals simp only [BitVec.toNat_add, BitVec.toNat_mul, Word.mask26_toNat,
    Word.mask25_toNat, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  all_goals norm_num at *
  all_goals omega

end Agave.Ed25519.Reduce64
