import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.MontgomeryBounds

/-! Carry repacking of the unreduced Montgomery quotient. The top limb bound
comes from the whole quotient bound, rather than an unjustified u64 truncation. -/
namespace Agave.Ed25519.Verifier.Execution.ScalarMontgomeryMul

open Agave.Ed25519.Bridge
open Agave.Ed25519.ScalarReduce32.Arithmetic
set_option exponentiation.threshold 512

/-- Four high-column sums in source registers 163, 171, 177, and 183. -/
def upperSums (z : Fin 9 → Nat) (i : Fin 4) : Nat :=
  let t := cancellationSums z
  let n := fun i => adjustmentDigit (t i)
  match i.val with
  | 0 => adjustmentCarry (t 4) + z 5 + n 1 * 17592186044416 +
      n 3 * 1367801 + n 4 * 3916664325105025
  | 1 =>
      let q0 := adjustmentCarry (t 4) + z 5 + n 1 * 17592186044416 +
        n 3 * 1367801 + n 4 * 3916664325105025
      q0 / 2 ^ 52 + z 6 + n 2 * 17592186044416 + n 4 * 1367801
  | 2 =>
      let q0 := adjustmentCarry (t 4) + z 5 + n 1 * 17592186044416 +
        n 3 * 1367801 + n 4 * 3916664325105025
      let q1 := q0 / 2 ^ 52 + z 6 + n 2 * 17592186044416 + n 4 * 1367801
      q1 / 2 ^ 52 + z 7 + n 3 * 17592186044416
  | _ =>
      let q0 := adjustmentCarry (t 4) + z 5 + n 1 * 17592186044416 +
        n 3 * 1367801 + n 4 * 3916664325105025
      let q1 := q0 / 2 ^ 52 + z 6 + n 2 * 17592186044416 + n 4 * 1367801
      let q2 := q1 / 2 ^ 52 + z 7 + n 3 * 17592186044416
      q2 / 2 ^ 52 + z 8 + n 4 * 17592186044416

theorem upperSums_zero (z : Fin 9 → Nat) :
    upperSums z 0 = adjustmentCarry (cancellationSums z 4) + z 5 +
      adjustmentDigit (cancellationSums z 1) * 17592186044416 +
      adjustmentDigit (cancellationSums z 3) * 1367801 +
      adjustmentDigit (cancellationSums z 4) * 3916664325105025 := rfl

theorem upperSums_one (z : Fin 9 → Nat) :
    upperSums z 1 = upperSums z 0 / 2 ^ 52 + z 6 +
      adjustmentDigit (cancellationSums z 2) * 17592186044416 +
      adjustmentDigit (cancellationSums z 4) * 1367801 := rfl

theorem upperSums_two (z : Fin 9 → Nat) :
    upperSums z 2 = upperSums z 1 / 2 ^ 52 + z 7 +
      adjustmentDigit (cancellationSums z 3) * 17592186044416 := rfl

theorem upperSums_three (z : Fin 9 → Nat) :
    upperSums z 3 = upperSums z 2 / 2 ^ 52 + z 8 +
      adjustmentDigit (cancellationSums z 4) * 17592186044416 := rfl

/-- Repack four accumulated columns, preserving the final unmasked carry. -/
def repackUpper (q : Fin 4 → Nat) : Fin 5 → Nat :=
  ![q 0 % 2 ^ 52, q 1 % 2 ^ 52, q 2 % 2 ^ 52, q 3 % 2 ^ 52, q 3 / 2 ^ 52]

/-- Five quotient limbs before the conditional subtraction of L. -/
def quotientLimbs (z : Fin 9 → Nat) : Fin 5 → Nat := repackUpper (upperSums z)

private theorem repackUpper_value (q : Fin 4 → Nat) :
    limbValue (repackUpper q) =
      limbs (q 0 % 2 ^ 52) (q 1 % 2 ^ 52) (q 2 % 2 ^ 52)
        (q 3 % 2 ^ 52) (q 3 / 2 ^ 52) := rfl

private theorem schedule_upper (z : Fin 9 → Nat) :
    (reduceSchedule (z 0) (z 1) (z 2) (z 3) (z 4) (z 5) (z 6) (z 7) (z 8)).2 =
      upperHalf (z 5) (z 6) (z 7) (z 8)
        (adjustmentDigit (cancellationSums z 1)) (adjustmentDigit (cancellationSums z 2))
        (adjustmentDigit (cancellationSums z 3)) (adjustmentDigit (cancellationSums z 4))
        (adjustmentCarry (cancellationSums z 4)) := rfl

private theorem upper_carry_telescope
    (z5 z6 z7 z8 n1 n2 n3 n4 carry q0 q1 q2 q3 : Nat)
    (hq0 : q0 = carry + z5 + n1 * 17592186044416 + n3 * 1367801 +
      n4 * 3916664325105025)
    (hq1 : q1 = q0 / 2 ^ 52 + z6 + n2 * 17592186044416 + n4 * 1367801)
    (hq2 : q2 = q1 / 2 ^ 52 + z7 + n3 * 17592186044416)
    (hq3 : q3 = q2 / 2 ^ 52 + z8 + n4 * 17592186044416) :
    limbs (q0 % 2 ^ 52) (q1 % 2 ^ 52) (q2 % 2 ^ 52)
      (q3 % 2 ^ 52) (q3 / 2 ^ 52) = upperHalf z5 z6 z7 z8 n1 n2 n3 n4 carry := by
  have h0 := Nat.mod_add_div q0 (2 ^ 52)
  have h1 := Nat.mod_add_div q1 (2 ^ 52)
  have h2 := Nat.mod_add_div q2 (2 ^ 52)
  have h3 := Nat.mod_add_div q3 (2 ^ 52)
  norm_num [limbs, upperHalf, radix] at *
  omega

/-- All repacking carries telescope to the already certified quotient. -/
theorem quotientLimbs_value (z : Fin 9 → Nat) :
    limbValue (quotientLimbs z) =
      (reduceSchedule (z 0) (z 1) (z 2) (z 3) (z 4) (z 5) (z 6) (z 7) (z 8)).2 := by
  unfold quotientLimbs
  apply Eq.trans (repackUpper_value (upperSums z))
  apply Eq.trans _ (schedule_upper z).symm
  exact upper_carry_telescope (z 5) (z 6) (z 7) (z 8)
    (adjustmentDigit (cancellationSums z 1)) (adjustmentDigit (cancellationSums z 2))
    (adjustmentDigit (cancellationSums z 3)) (adjustmentDigit (cancellationSums z 4))
    (adjustmentCarry (cancellationSums z 4))
    (upperSums z 0) (upperSums z 1) (upperSums z 2) (upperSums z 3)
    (upperSums_zero z) (upperSums_one z) (upperSums_two z) (upperSums_three z)

private theorem top_limb_bound (x : Fin 5 → Nat)
    (h : limbValue x < 2 * subgroupOrder) : x 4 < 2 ^ 46 := by
  norm_num [limbValue, limbs, radix, subgroupOrder] at h ⊢
  omega

private theorem repackUpper_bounds (q : Fin 4 → Nat)
    (htop : repackUpper q 4 < 2 ^ 46) : ∀ i, repackUpper q i < 2 ^ 52 := by
  intro i
  fin_cases i
  · exact Nat.mod_lt _ (by decide)
  · exact Nat.mod_lt _ (by decide)
  · exact Nat.mod_lt _ (by decide)
  · exact Nat.mod_lt _ (by decide)
  · exact htop.trans (by decide)

/-- The quotient bound justifies the otherwise unmasked top-limb truncation. -/
theorem quotientLimbs_bounds (a b : Fin 5 → Nat)
    (ha : limbValue a < 2 ^ 260) (hb : limbValue b < subgroupOrder) :
    (∀ i, quotientLimbs (productColumns a b) i < 2 ^ 52) ∧
      quotientLimbs (productColumns a b) 4 < 2 ^ 46 := by
  have hc := productSchedule_certificate a b
  have hq := ScalarWide.montgomery_quotient_bound
    (limbValue a) (limbValue b) (productSchedule a b).1 (productSchedule a b).2
    ha hb hc.1 hc.2
  have he : limbValue (quotientLimbs (productColumns a b)) = (productSchedule a b).2 :=
    quotientLimbs_value (productColumns a b)
  have htop : quotientLimbs (productColumns a b) 4 < 2 ^ 46 := by
    exact top_limb_bound _ (he.symm ▸ hq)
  exact ⟨repackUpper_bounds (upperSums (productColumns a b)) htop, htop⟩

/-- The source truncation followed by its mask retains exactly one radix digit. -/
theorem trunc128_mask52 (word : BitVec 128) :
    ((word.setWidth 64) &&& 4503599627370495#64).toNat = word.toNat % 2 ^ 52 := by
  rw [mask52_toNat, BitVec.toNat_setWidth]
  exact Nat.mod_mod_of_dvd _ (by decide +kernel : 2 ^ 52 ∣ 2 ^ 64)

/-- The final high carry may be truncated only after its independent bound. -/
theorem final_carry_trunc (word : BitVec 128) (h : word.toNat / 2 ^ 52 < 2 ^ 64) :
    ((word >>> (52 : Nat)).setWidth 64).toNat = word.toNat / 2 ^ 52 := by
  rw [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
    Nat.mod_eq_of_lt h]

end Agave.Ed25519.Verifier.Execution.ScalarMontgomeryMul
