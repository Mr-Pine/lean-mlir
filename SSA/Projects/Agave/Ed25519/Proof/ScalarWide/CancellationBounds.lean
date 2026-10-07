import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.ProductBounds
import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.MontgomeryPart1

namespace Agave.Ed25519.Verifier.Execution.ScalarMontgomeryMul

open LeanMLIR.RIR
open Agave.Ed25519.ScalarReduce32.Arithmetic
set_option exponentiation.threshold 512

/-- The inputs of the five cancellation windows in the exact source order. -/
def cancellationSums (z : Fin 9 → Nat) (i : Fin 5) : Nat :=
  match i.val with
  | 0 => z 0
  | 1 =>
      let t0 := z 0
      adjustmentCarry t0 + z 1 + adjustmentDigit t0 * 3916664325105025
  | 2 =>
      let t0 := z 0
      let t1 := adjustmentCarry t0 + z 1 + adjustmentDigit t0 * 3916664325105025
      adjustmentCarry t1 + z 2 + adjustmentDigit t0 * 1367801 +
        adjustmentDigit t1 * 3916664325105025
  | 3 =>
      let t0 := z 0
      let t1 := adjustmentCarry t0 + z 1 + adjustmentDigit t0 * 3916664325105025
      let t2 := adjustmentCarry t1 + z 2 + adjustmentDigit t0 * 1367801 +
        adjustmentDigit t1 * 3916664325105025
      adjustmentCarry t2 + z 3 + adjustmentDigit t1 * 1367801 +
        adjustmentDigit t2 * 3916664325105025
  | _ =>
      let t0 := z 0
      let t1 := adjustmentCarry t0 + z 1 + adjustmentDigit t0 * 3916664325105025
      let t2 := adjustmentCarry t1 + z 2 + adjustmentDigit t0 * 1367801 +
        adjustmentDigit t1 * 3916664325105025
      let t3 := adjustmentCarry t2 + z 3 + adjustmentDigit t1 * 1367801 +
        adjustmentDigit t2 * 3916664325105025
      adjustmentCarry t3 + z 4 + adjustmentDigit t0 * 17592186044416 +
        adjustmentDigit t2 * 1367801 + adjustmentDigit t3 * 3916664325105025

/-- Each adjustment-limb contribution is also a bounded 104-bit product. -/
theorem adjustment_term_bound (sum constant : Nat) (hc : constant < 2 ^ 52) :
    adjustmentDigit sum * constant < 2 ^ 104 :=
  limb_product_bound _ _ (adjustmentDigit_bound sum) hc

private theorem cancellation_sum3_bound (c z p : Nat)
    (hc : c < 2 ^ 69) (hz : z < 2 ^ 107) (hp : p < 2 ^ 104) :
    c + z + p < 2 ^ 120 := by
  norm_num at *
  omega

private theorem cancellation_sum4_bound (c z p q : Nat)
    (hc : c < 2 ^ 69) (hz : z < 2 ^ 107)
    (hp : p < 2 ^ 104) (hq : q < 2 ^ 104) :
    c + z + p + q < 2 ^ 120 := by
  norm_num at *
  omega

private theorem cancellation_sum5_bound (c z p q r : Nat)
    (hc : c < 2 ^ 69) (hz : z < 2 ^ 107)
    (hp : p < 2 ^ 104) (hq : q < 2 ^ 104) (hr : r < 2 ^ 104) :
    c + z + p + q + r < 2 ^ 120 := by
  norm_num at *
  omega

private theorem cancellationSums_zero (z : Fin 9 → Nat) :
    cancellationSums z 0 = z 0 := rfl

private theorem cancellationSums_one (z : Fin 9 → Nat) :
    cancellationSums z 1 = adjustmentCarry (cancellationSums z 0) + z 1 +
      adjustmentDigit (cancellationSums z 0) * 3916664325105025 := rfl

private theorem cancellationSums_two (z : Fin 9 → Nat) :
    cancellationSums z 2 = adjustmentCarry (cancellationSums z 1) + z 2 +
      adjustmentDigit (cancellationSums z 0) * 1367801 +
      adjustmentDigit (cancellationSums z 1) * 3916664325105025 := rfl

private theorem cancellationSums_three (z : Fin 9 → Nat) :
    cancellationSums z 3 = adjustmentCarry (cancellationSums z 2) + z 3 +
      adjustmentDigit (cancellationSums z 1) * 1367801 +
      adjustmentDigit (cancellationSums z 2) * 3916664325105025 := rfl

private theorem cancellationSums_four (z : Fin 9 → Nat) :
    cancellationSums z 4 = adjustmentCarry (cancellationSums z 3) + z 4 +
      adjustmentDigit (cancellationSums z 0) * 17592186044416 +
      adjustmentDigit (cancellationSums z 2) * 1367801 +
      adjustmentDigit (cancellationSums z 3) * 3916664325105025 := rfl

private theorem cancellationSums_bound0 (z : Fin 9 → Nat) (hz : ∀ i, z i < 2 ^ 107) :
    cancellationSums z 0 < 2 ^ 120 := by
  rw [cancellationSums_zero]
  exact (hz 0).trans (by decide)

private theorem cancellationSums_bound1 (z : Fin 9 → Nat) (hz : ∀ i, z i < 2 ^ 107) :
    cancellationSums z 1 < 2 ^ 120 := by
  rw [cancellationSums_one]
  exact cancellation_sum3_bound _ _ _
    (adjustmentCarry_bound120 _ (cancellationSums_bound0 z hz)) (hz 1)
    (adjustment_term_bound _ 3916664325105025 (by decide))

private theorem cancellationSums_bound2 (z : Fin 9 → Nat) (hz : ∀ i, z i < 2 ^ 107) :
    cancellationSums z 2 < 2 ^ 120 := by
  rw [cancellationSums_two]
  exact cancellation_sum4_bound _ _ _ _
    (adjustmentCarry_bound120 _ (cancellationSums_bound1 z hz)) (hz 2)
    (adjustment_term_bound _ 1367801 (by decide))
    (adjustment_term_bound _ 3916664325105025 (by decide))

private theorem cancellationSums_bound3 (z : Fin 9 → Nat) (hz : ∀ i, z i < 2 ^ 107) :
    cancellationSums z 3 < 2 ^ 120 := by
  rw [cancellationSums_three]
  exact cancellation_sum4_bound _ _ _ _
    (adjustmentCarry_bound120 _ (cancellationSums_bound2 z hz)) (hz 3)
    (adjustment_term_bound _ 1367801 (by decide))
    (adjustment_term_bound _ 3916664325105025 (by decide))

private theorem cancellationSums_bound4 (z : Fin 9 → Nat) (hz : ∀ i, z i < 2 ^ 107) :
    cancellationSums z 4 < 2 ^ 120 := by
  rw [cancellationSums_four]
  exact cancellation_sum5_bound _ _ _ _ _
    (adjustmentCarry_bound120 _ (cancellationSums_bound3 z hz)) (hz 4)
    (adjustment_term_bound _ 17592186044416 (by decide))
    (adjustment_term_bound _ 1367801 (by decide))
    (adjustment_term_bound _ 3916664325105025 (by decide))

/-- All five cancellation inputs satisfy the bound required by the word
refinement, and each cancellation output has at most 69 bits. -/
theorem cancellationSums_bounds (z : Fin 9 → Nat) (hz : ∀ i, z i < 2 ^ 107) :
    ∀ i, cancellationSums z i < 2 ^ 120 ∧
      adjustmentCarry (cancellationSums z i) < 2 ^ 69 := by
  intro i
  have h : cancellationSums z i < 2 ^ 120 := by
    fin_cases i
    · exact cancellationSums_bound0 z hz
    · exact cancellationSums_bound1 z hz
    · exact cancellationSums_bound2 z hz
    · exact cancellationSums_bound3 z hz
    · exact cancellationSums_bound4 z hz
  exact ⟨h, adjustmentCarry_bound120 _ h⟩


end Agave.Ed25519.Verifier.Execution.ScalarMontgomeryMul
