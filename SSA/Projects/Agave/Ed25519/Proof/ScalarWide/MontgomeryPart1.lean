import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.MontgomeryProduct
import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.Montgomery

/-! Word refinement of the exact `part1` cancellation step. The input bound
allows all later Montgomery sums and is established from radix-52 inputs by
the caller's arithmetic invariant. No multiplication or shift flag is erased. -/

namespace Agave.Ed25519.Verifier.Execution.ScalarMontgomeryMul

open LeanMLIR.RIR
open Agave.Ed25519.ScalarReduce32.Arithmetic

/-- The compiled truncation, wrapping u64 multiplication, and 52-bit mask. -/
def digitWord (sum : BitVec 128) : BitVec 64 :=
  (sum.setWidth 64 * 1439961107955227#64) &&& 4503599627370495#64

def carryWord (sum : BitVec 128) : BitVec 128 :=
  (sum + (digitWord sum).setWidth 128 * 671914833335277#128) >>> 52

theorem mask52_toNat (word : BitVec 64) :
    (word &&& 4503599627370495#64).toNat = word.toNat % 2 ^ 52 := by
  change word.toNat &&& (2 ^ 52 - 1) = _
  exact Nat.and_two_pow_sub_one_eq_mod _ _

/-- The intentional u64 wrapping multiply retains exactly the low 52 bits
needed by the natural Montgomery adjustment digit. -/
theorem digitWord_toNat (sum : BitVec 128) :
    (digitWord sum).toNat = adjustmentDigit sum.toNat := by
  rw [digitWord, mask52_toNat, BitVec.toNat_mul, BitVec.toNat_setWidth]
  change ((sum.toNat % 2 ^ 64 * 1439961107955227) % 2 ^ 64) % 2 ^ 52 =
    (sum.toNat * 1439961107955227) % 2 ^ 52
  have hd : 2 ^ 52 ∣ 2 ^ 64 := by decide +kernel
  rw [Nat.mod_mod_of_dvd _ hd]
  calc
    (sum.toNat % 2 ^ 64 * 1439961107955227) % 2 ^ 52 =
        ((sum.toNat % 2 ^ 64) % 2 ^ 52 * (1439961107955227 % 2 ^ 52)) % 2 ^ 52 :=
      Nat.mul_mod _ _ _
    _ = (sum.toNat % 2 ^ 52 * (1439961107955227 % 2 ^ 52)) % 2 ^ 52 := by
      rw [Nat.mod_mod_of_dvd _ hd]
    _ = (sum.toNat * 1439961107955227) % 2 ^ 52 := (Nat.mul_mod _ _ _).symm

theorem digitWord_bound (sum : BitVec 128) : (digitWord sum).toNat < 2 ^ 52 := by
  rw [digitWord_toNat]
  exact adjustmentDigit_bound _

/-- The source's `zext nneg` cannot poison a masked adjustment digit. -/
theorem digitWord_zext_nneg (sum : BitVec 128) :
    Operation.zext true (.value (digitWord sum)) =
      .value ((digitWord sum).setWidth 128) := by
  have hb := digitWord_bound sum
  have hm : (digitWord sum).msb = false := by
    apply BitVec.msb_eq_false_iff_two_mul_lt.mpr
    norm_num at hb ⊢
    omega
  simp [Operation.zext, hm]

/-- Each exact multiplication by a subgroup-order limb fits signed and
unsigned u128. This covers all three literal multiplication constants. -/
theorem adjustment_mul_flags (digit : BitVec 64) (constant : BitVec 128)
    (hd : digit.toNat < 2 ^ 52) (hc : constant.toNat < 2 ^ 52) :
    Operation.mul { nsw := true, nuw := true } (.value (digit.setWidth 128))
      (.value constant) = .value (digit.setWidth 128 * constant) := by
  have hp : digit.toNat * constant.toNat < 2 ^ 104 := by
    have h := Nat.mul_lt_mul_of_le_of_lt (Nat.le_of_lt hd) hc
      (by decide : 0 < 2 ^ 52)
    norm_num at h ⊢
    exact h
  have hwide : 2 * (digit.setWidth 128).toNat < 2 ^ 128 := by
    rw [BitVec.toNat_setWidth_of_le (by decide : 64 ≤ 128)]
    norm_num at hd ⊢
    omega
  have hdi : (digit.setWidth 128).toInt = (digit.toNat : Int) := by
    rw [BitVec.toInt_eq_toNat_of_lt hwide,
      BitVec.toNat_setWidth_of_le (by decide : 64 ≤ 128)]
  have hci : constant.toInt = (constant.toNat : Int) :=
    BitVec.toInt_eq_toNat_of_lt (by norm_num at hc ⊢; omega)
  have hu : (digit.setWidth 128).umulOverflow constant = false := by
    simp only [BitVec.umulOverflow, BitVec.toNat_setWidth_of_le (by decide : 64 ≤ 128)]
    norm_num at hp ⊢
    omega
  have hs : (digit.setWidth 128).smulOverflow constant = false := by
    simp only [BitVec.smulOverflow, hdi, hci, ← Int.natCast_mul]
    norm_num at hp ⊢
    omega
  simp [Operation.mul, hu, hs]

/-- Exact division/carry value of one compiled cancellation step. -/
theorem carryWord_toNat (sum : BitVec 128) (h : sum.toNat < 2 ^ 120) :
    (carryWord sum).toNat = adjustmentCarry sum.toNat := by
  have hd := digitWord_bound sum
  have hp : (digitWord sum).toNat * 671914833335277 < 2 ^ 104 := by
    norm_num at hd ⊢
    omega
  have hp128 : (digitWord sum).toNat * 671914833335277 < 2 ^ 128 :=
    hp.trans (by decide)
  have hmul : ((digitWord sum).setWidth 128 * 671914833335277#128).toNat =
      (digitWord sum).toNat * 671914833335277 := by
    rw [BitVec.toNat_mul, BitVec.toNat_setWidth_of_le (by decide : 64 ≤ 128)]
    exact Nat.mod_eq_of_lt hp128
  have hsum : sum.toNat + (digitWord sum).toNat * 671914833335277 < 2 ^ 128 := by
    norm_num at h hp ⊢
    omega
  rw [carryWord, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
    BitVec.toNat_add, hmul, Nat.mod_eq_of_lt hsum, digitWord_toNat]
  rfl

/-- A uniform bound propagated between the five adjustment rounds. -/
theorem adjustmentCarry_bound120 (sum : Nat) (h : sum < 2 ^ 120) :
    adjustmentCarry sum < 2 ^ 69 := by
  have hd := adjustmentDigit_bound sum
  unfold adjustmentCarry
  apply (Nat.div_lt_iff_lt_mul (by decide : 0 < radix)).mpr
  norm_num [radix] at h hd ⊢
  omega

end Agave.Ed25519.Verifier.Execution.ScalarMontgomeryMul
