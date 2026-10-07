import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.ProductFlags
import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.Arithmetic

namespace Agave.Ed25519.ScalarReduce32.Execution
open LeanMLIR.RIR
open Arithmetic

def cancellationDigit (sum : BitVec 128) : BitVec 64 :=
  (sum.setWidth 64 * 1439961107955227#64) &&& 4503599627370495#64

def cancellationCarry (sum : BitVec 128) : BitVec 128 :=
  ((cancellationDigit sum).setWidth 128 * 671914833335277#128 + sum) >>> 52

theorem cancellation_mask_toNat (word : BitVec 64) :
    (word &&& 4503599627370495#64).toNat = word.toNat % 2 ^ 52 := by
  change word.toNat &&& (2 ^ 52 - 1) = _
  exact Nat.and_two_pow_sub_one_eq_mod _ _

theorem cancellationDigit_bound (sum : BitVec 128) :
    (cancellationDigit sum).toNat < 2 ^ 52 := by
  rw [cancellationDigit, cancellation_mask_toNat]
  exact Nat.mod_lt _ (by decide)

/-- The intentional low-u64 wrapping multiply preserves the needed 52 bits. -/
theorem cancellationDigit_toNat (sum : BitVec 128) :
    (cancellationDigit sum).toNat = adjustmentDigit sum.toNat := by
  rw [cancellationDigit, cancellation_mask_toNat, BitVec.toNat_mul,
    BitVec.toNat_setWidth]
  change ((sum.toNat % 2 ^ 64 * 1439961107955227) % 2 ^ 64) % 2 ^ 52 =
    (sum.toNat * 1439961107955227) % 2 ^ 52
  have hd : 2 ^ 52 ∣ 2 ^ 64 := by decide +kernel
  rw [Nat.mod_mod_of_dvd _ hd]
  rw [Nat.mul_mod (sum.toNat % 2 ^ 64), Nat.mul_mod sum.toNat,
    Nat.mod_mod_of_dvd _ hd]

theorem cancellation_sum_bound (sum : BitVec 128) (h : sum.toNat < 2 ^ 120) :
    ((cancellationDigit sum).setWidth 128 * 671914833335277#128).toNat +
      sum.toNat < 2 ^ 127 := by
  obtain ⟨_, _, hn⟩ := product_constant_flags (cancellationDigit sum)
    671914833335277#128 (cancellationDigit_bound sum) (by decide)
  rw [hn]
  have hd := cancellationDigit_bound sum
  norm_num at h hd ⊢
  omega

theorem cancellationCarry_toNat (sum : BitVec 128) (h : sum.toNat < 2 ^ 120) :
    (cancellationCarry sum).toNat = adjustmentCarry sum.toNat := by
  obtain ⟨_, _, hp⟩ := product_constant_flags (cancellationDigit sum)
    671914833335277#128 (cancellationDigit_bound sum) (by decide)
  obtain ⟨_, _, hs⟩ := product_add_flags
    ((cancellationDigit sum).setWidth 128 * 671914833335277#128) sum
    (cancellation_sum_bound sum h)
  rw [cancellationCarry, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
    hs, hp, cancellationDigit_toNat]
  norm_num [adjustmentCarry, radix, Nat.add_comm]

end Agave.Ed25519.ScalarReduce32.Execution
