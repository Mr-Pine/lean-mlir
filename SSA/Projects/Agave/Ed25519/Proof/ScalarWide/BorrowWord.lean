import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.ConditionalSubtract
import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.MontgomeryPart1

/-! Algebraic word bridge for one radix-52 subtraction step. All reasoning is
through bitvector integer observations and bounds; no bitblasting is used. -/

namespace Agave.Ed25519.Verifier.Execution.ScalarWide.Subtraction

/-- An arithmetic shift by 63 broadcasts a u64 word's sign bit. -/
theorem sign_mask (word : BitVec 64) :
    word.sshiftRight 63 = if word.msb then -1 else 0 := by
  apply BitVec.eq_of_toNat_eq
  have hw := word.isLt
  cases hm : word.msb with
  | false =>
      rw [BitVec.toNat_sshiftRight_of_msb_false hm]
      have hsign := BitVec.msb_eq_false_iff_two_mul_lt.mp hm
      simp only [hm, Bool.false_eq_true, ↓reduceIte, BitVec.toNat_ofNat]
      norm_num [Nat.shiftRight_eq_div_pow] at hw hsign ⊢
      omega
  | true =>
      rw [BitVec.toNat_sshiftRight_of_msb_true hm]
      have hsign := BitVec.msb_eq_true_iff_two_mul_ge.mp hm
      simp only [hm, ↓reduceIte]
      norm_num [Nat.shiftRight_eq_div_pow] at hw hsign ⊢
      omega

/-- A normalized limb subtraction has exactly the expected wrapped u64 value. -/
theorem limb_sub_toNat (a : BitVec 64) (b incoming : Nat)
    (ha : a.toNat < 2 ^ 52) (hb : b < 2 ^ 52) (hin : incoming ≤ 1) :
    (a - BitVec.ofNat 64 (b + incoming)).toNat =
      if a.toNat < b + incoming then 2 ^ 64 + a.toNat - (b + incoming)
      else a.toNat - (b + incoming) := by
  have hq : b + incoming < 2 ^ 64 := by norm_num at ha hb ⊢; omega
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hq]
  split_ifs <;> norm_num at ha hb ⊢ <;> omega

/-- The machine mask yields the mathematical difference digit, and its signed
high-bit shift yields exactly the outgoing borrow mask. -/
theorem limb_sub_digit (a : BitVec 64) (b incoming : Nat)
    (ha : a.toNat < 2 ^ 52) (hb : b < 2 ^ 52) (hin : incoming ≤ 1) :
    ((a - BitVec.ofNat 64 (b + incoming)) &&& 4503599627370495#64).toNat =
        (subtractDigit a.toNat b incoming).1 ∧
      (a - BitVec.ofNat 64 (b + incoming)).sshiftRight 63 =
        if (subtractDigit a.toNat b incoming).2 = 1 then -1 else 0 := by
  have hw := limb_sub_toNat a b incoming ha hb hin
  constructor
  · rw [ScalarMontgomeryMul.mask52_toNat, hw]
    unfold subtractDigit
    split_ifs <;> dsimp <;> norm_num at ha hb ⊢ <;> omega
  · rw [sign_mask]
    by_cases h : a.toNat < b + incoming
    · have hm : (a - BitVec.ofNat 64 (b + incoming)).msb = true := by
        apply BitVec.msb_eq_true_iff_two_mul_ge.mpr
        rw [hw, if_pos h]
        norm_num at ha hb ⊢
        omega
      simp [subtractDigit, h, hm]
    · have hm : (a - BitVec.ofNat 64 (b + incoming)).msb = false := by
        apply BitVec.msb_eq_false_iff_two_mul_lt.mpr
        rw [hw, if_neg h]
        norm_num at ha hb ⊢
        omega
      simp [subtractDigit, h, hm]

end Agave.Ed25519.Verifier.Execution.ScalarWide.Subtraction
