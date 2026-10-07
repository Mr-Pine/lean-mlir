import SSA.Projects.Firedancer.Common.Spec.Scalar.fd_curve25519_scalar_reduce
import Mathlib.Tactic

/-!
Integer arithmetic for the constants and carry rules in the committed
Firedancer radix-2^21 reducer. These lemmas describe the signed arithmetic;
they do not assert that every LLVM instruction avoids signed overflow.
-/

namespace Firedancer.Common.ScalarArithmetic

/-- `%3`, the source's 21-bit limb width. -/
def radix : Int := 2 ^ 21

/-- The six signed multiplication constants `%24` through `%29`. -/
def foldCoefficients : Int :=
  666643 + 470296 * radix + 654183 * radix ^ 2 -
    997805 * radix ^ 3 + 136657 * radix ^ 4 - 683901 * radix ^ 5

/-- The six literal coefficients represent the negative low part of L. -/
theorem foldCoefficients_exact :
    foldCoefficients = -(27742317777372353535851937790883648493 : Int) := by
  norm_num [foldCoefficients, radix]

/-- Replacing a digit twelve limbs above by the six source multiples subtracts
an exact integer multiple of L, including when that digit is negative. -/
theorem fold_identity (digit : Int) :
    digit * radix ^ 12 = digit * foldCoefficients + digit * (groupOrder : Int) := by
  norm_num [foldCoefficients, radix, groupOrder]
  ring

/-- No positivity assumption on `low` or `digit` is needed for modular folding. -/
theorem fold_preserves_residue (low digit : Int) :
    (low + digit * radix ^ 12) % (groupOrder : Int) =
      (low + digit * foldCoefficients) % (groupOrder : Int) := by
  rw [fold_identity]
  simp [Int.add_emod, Int.mul_emod]

/-- The rounded carries used before the source's final two carry passes. -/
def centeredCarry (digit : Int) : Int := (digit + 2 ^ 20) / radix

def centeredDigit (digit : Int) : Int := digit - radix * centeredCarry digit

theorem centeredDigit_eq_mod (digit : Int) :
    centeredDigit digit = (digit + 2 ^ 20) % radix - 2 ^ 20 := by
  have h := Int.emod_add_ediv_mul (digit + 2 ^ 20) radix
  unfold centeredDigit centeredCarry
  rw [Int.mul_comm radix]
  omega

/-- Each centered digit fits exactly in signed 21-bit range. -/
theorem centeredDigit_bounds (digit : Int) :
    -(2 ^ 20 : Int) ≤ centeredDigit digit ∧ centeredDigit digit < 2 ^ 20 := by
  rw [centeredDigit_eq_mod]
  have hlo := Int.emod_nonneg (digit + 2 ^ 20) (show radix ≠ 0 by norm_num [radix])
  have hhi := Int.emod_lt_of_pos (digit + 2 ^ 20) (show 0 < radix by norm_num [radix])
  norm_num [radix] at hlo hhi ⊢
  omega

/-- Carrying changes the representation, not the represented integer. -/
theorem centeredCarry_identity (digit next : Int) :
    centeredDigit digit + radix * (next + centeredCarry digit) = digit + radix * next := by
  unfold centeredDigit
  ring

/-- The final unrounded carry removes the bit-252 digit, then replaces it by
its six low multiples. This is the mathematical operation at `%410`-`%446`. -/
def finalFold (x : Int) : Int :=
  x % radix ^ 12 + (x / radix ^ 12) * foldCoefficients

/-- Exact quotient accounting for the last source fold. -/
theorem finalFold_identity (x : Int) :
    finalFold x = x - (x / radix ^ 12) * (groupOrder : Int) := by
  have h := Int.emod_add_ediv_mul x (radix ^ 12)
  have hf := fold_identity (x / radix ^ 12)
  unfold finalFold
  omega

/-- A centered value in one radix window becomes the canonical representative
in the final fold. Merely proving congruence would not establish this range. -/
theorem finalFold_canonical (x : Int)
    (hlo : -(radix ^ 12) ≤ x) (hhi : x < radix ^ 12) :
    0 ≤ finalFold x ∧ finalFold x < (groupOrder : Int) ∧
      finalFold x = x % (groupOrder : Int) := by
  rw [finalFold_identity]
  norm_num [radix, groupOrder] at hlo hhi ⊢
  omega

end Firedancer.Common.ScalarArithmetic
