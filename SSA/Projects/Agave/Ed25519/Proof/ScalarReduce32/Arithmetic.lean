import SSA.Projects.Agave.Ed25519.UpstreamMath.Canonicality
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.Ring

/-!
Arithmetic certificate lemmas for the imported 32-byte scalar reducer.

The constants below are the five limbs of `constants::R` and `constants::L`
in the pinned serial/u64 source. The Montgomery modulus is 2^260, whereas
`ell` is the subgroup order. These lemmas reduce the arithmetic verification
to the exact carry identity and the range of the five Montgomery digits.
They do not assert that the imported instructions establish that identity.
-/
namespace Agave.Ed25519.ScalarReduce32.Arithmetic
open Agave.Ed25519.UpstreamMath.Canonicality
set_option exponentiation.threshold 512

/-- Radix of the serial scalar representation. -/
def radix : Nat := 2^52

/-- Value of five little-endian limbs, with no implicit normalization. -/
def limbs (a b c d e : Nat) : Nat :=
  a + radix * b + radix^2 * c + radix^3 * d + radix^4 * e

/-- The full Montgomery modulus; not the source constant named `R`. -/
def montgomeryModulus : Nat := 2^260

/-- The literal source constant named `R`, already reduced modulo `ell`. -/
def sourceR : Nat :=
  limbs 4302102966953709 1049714374468698 4503599278581019
    4503599627370495 17592186044415

def lfactor : Nat := 1439961107955227

theorem sourceL_eq_ell : limbs 671914833335277 3916664325105025 1367801 0
    17592186044416 = ell := by decide +kernel

theorem sourceR_eq_mod : sourceR = montgomeryModulus % ell := by decide +kernel

theorem sourceR_lt_ell : sourceR < ell := by decide +kernel

theorem lfactor_identity : (671914833335277 * lfactor + 1) % radix = 0 := by
  decide +kernel

theorem montgomery_coprime : Nat.gcd ell montgomeryModulus = 1 := by decide +kernel

/-- Natural-number form of each `part1` adjustment digit. -/
def adjustmentDigit (sum : Nat) : Nat := (sum * lfactor) % radix

def adjustmentCarry (sum : Nat) : Nat :=
  (sum + adjustmentDigit sum * 671914833335277) / radix

theorem adjustmentDigit_bound (sum : Nat) : adjustmentDigit sum < radix :=
  Nat.mod_lt _ (by decide)

/-- Low-limb cancellation is valid for arbitrary nonnegative intermediate sums.
Word overflow and truncation must separately be discharged in the machine proof. -/
theorem adjustment_identity (sum : Nat) :
    sum + adjustmentDigit sum * 671914833335277 = radix * adjustmentCarry sum := by
  have hd : Nat.ModEq radix (adjustmentDigit sum) (sum * lfactor) :=
    Nat.mod_modEq _ _
  have hz : Nat.ModEq radix (1 + lfactor * 671914833335277) 0 := by
    decide +kernel
  have hzero : Nat.ModEq radix (sum + adjustmentDigit sum * 671914833335277) 0 := by
    calc
      _ ≡ sum + (sum * lfactor) * 671914833335277 [MOD radix] :=
        (hd.mul_right _).add_left _
      _ = sum * (1 + lfactor * 671914833335277) := by ring
      _ ≡ sum * 0 [MOD radix] := hz.mul_left _
      _ = 0 := Nat.mul_zero _
  have hmod : (sum + adjustmentDigit sum * 671914833335277) % radix = 0 := by
    simpa only [Nat.ModEq, Nat.zero_mod] using hzero
  have h := Nat.mod_add_div (sum + adjustmentDigit sum * 671914833335277) radix
  simpa only [hmod, Nat.zero_add, adjustmentCarry] using h.symm

/-- The single conditional subtraction at the end of Montgomery reduction. -/
def finish (y : Nat) : Nat := if y < ell then y else y - ell

theorem finish_eq_mod (y : Nat) (hy : y < 2 * ell) : finish y = y % ell := by
  have he := ell_pos
  unfold finish
  split_ifs with h
  · exact (Nat.mod_eq_of_lt h).symm
  · norm_num [ell] at *
    omega

/-- A carry identity plus bounded Montgomery digits entails the range needed
for one final subtraction, for every 256-bit input including high-bit-set ones. -/
theorem quotient_bound (x n y : Nat) (hx : x < 2^256)
    (hn : n < montgomeryModulus)
    (hcarry : y * montgomeryModulus = x * sourceR + n * ell) :
    y < 2 * ell := by
  have hr : sourceR < ell := sourceR_lt_ell
  have hxR : x < montgomeryModulus :=
    lt_trans hx (by decide)
  have ha : x * sourceR < montgomeryModulus * ell :=
    lt_of_le_of_lt (Nat.mul_le_mul_right sourceR (Nat.le_of_lt hxR))
      (Nat.mul_lt_mul_of_pos_left hr (by decide))
  have hb : n * ell < montgomeryModulus * ell :=
    Nat.mul_lt_mul_of_pos_right hn ell_pos
  have hc : y * montgomeryModulus < (2 * ell) * montgomeryModulus := by
    rw [hcarry]
    calc
      _ < montgomeryModulus * ell + montgomeryModulus * ell := Nat.add_lt_add ha hb
      _ = _ := by ring
  exact (Nat.mul_lt_mul_right (by decide : 0 < montgomeryModulus)).mp hc

/-- The exact carry identity is enough for modular correctness; cancellation
uses the proved coprimality of 2^260 and the subgroup order. -/
theorem quotient_mod (x n y : Nat)
    (hcarry : y * montgomeryModulus = x * sourceR + n * ell) :
    y % ell = x % ell := by
  apply Nat.ModEq.cancel_right_of_coprime montgomery_coprime
  change (y * montgomeryModulus) % ell = (x * montgomeryModulus) % ell
  rw [hcarry, sourceR_eq_mod]
  simp [Nat.add_mod, Nat.mul_mod]

/-- Canonical mathematical result of the Montgomery certificate. The machine
proof must produce `hcarry` from the imported, flagged word operations. -/
theorem finish_correct (x n y : Nat) (hx : x < 2^256)
    (hn : n < montgomeryModulus)
    (hcarry : y * montgomeryModulus = x * sourceR + n * ell) :
    finish y = x % ell ∧ finish y < ell := by
  rw [finish_eq_mod y (quotient_bound x n y hx hn hcarry), quotient_mod x n y hcarry]
  exact ⟨rfl, Nat.mod_lt x ell_pos⟩

end Agave.Ed25519.ScalarReduce32.Arithmetic
