import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.UpperPacking

/-! Bounds for the four high-column carry sums, independently of machine words. -/
namespace Agave.Ed25519.Verifier.Execution.ScalarMontgomeryMul

open Agave.Ed25519.ScalarReduce32.Arithmetic
set_option exponentiation.threshold 512

private theorem upper_sum3_bound (c z p : Nat)
    (hc : c < 2 ^ 69) (hz : z < 2 ^ 107) (hp : p < 2 ^ 104) :
    c + z + p < 2 ^ 120 := by
  norm_num at *
  omega

private theorem upper_sum4_bound (c z p q : Nat)
    (hc : c < 2 ^ 69) (hz : z < 2 ^ 107)
    (hp : p < 2 ^ 104) (hq : q < 2 ^ 104) :
    c + z + p + q < 2 ^ 120 := by
  norm_num at *
  omega

private theorem upper_sum5_bound (c z p q r : Nat)
    (hc : c < 2 ^ 69) (hz : z < 2 ^ 107)
    (hp : p < 2 ^ 104) (hq : q < 2 ^ 104) (hr : r < 2 ^ 104) :
    c + z + p + q + r < 2 ^ 120 := by
  norm_num at *
  omega

private theorem upper_carry_bound (q : Nat) (hq : q < 2 ^ 120) :
    q / 2 ^ 52 < 2 ^ 69 := by
  norm_num at hq ⊢
  omega

private theorem upperSums_bound0 (z : Fin 9 → Nat) (hz : ∀ i, z i < 2 ^ 107) :
    upperSums z 0 < 2 ^ 120 := by
  rw [upperSums_zero]
  exact upper_sum5_bound _ _ _ _ _ (cancellationSums_bounds z hz 4).2 (hz 5)
    (adjustment_term_bound _ _ (by decide))
    (adjustment_term_bound _ _ (by decide))
    (adjustment_term_bound _ _ (by decide))

private theorem upperSums_bound1 (z : Fin 9 → Nat) (hz : ∀ i, z i < 2 ^ 107) :
    upperSums z 1 < 2 ^ 120 := by
  rw [upperSums_one]
  exact upper_sum4_bound _ _ _ _ (upper_carry_bound _ (upperSums_bound0 z hz)) (hz 6)
    (adjustment_term_bound _ _ (by decide))
    (adjustment_term_bound _ _ (by decide))

private theorem upperSums_bound2 (z : Fin 9 → Nat) (hz : ∀ i, z i < 2 ^ 107) :
    upperSums z 2 < 2 ^ 120 := by
  rw [upperSums_two]
  exact upper_sum3_bound _ _ _ (upper_carry_bound _ (upperSums_bound1 z hz)) (hz 7)
    (adjustment_term_bound _ _ (by decide))

private theorem upperSums_bound3 (z : Fin 9 → Nat) (hz : ∀ i, z i < 2 ^ 107) :
    upperSums z 3 < 2 ^ 120 := by
  rw [upperSums_three]
  exact upper_sum3_bound _ _ _ (upper_carry_bound _ (upperSums_bound2 z hz)) (hz 8)
    (adjustment_term_bound _ _ (by decide))

/-- Every upper repacking sum fits u128 and each carry is below 2^69. -/
theorem upperSums_bounds (z : Fin 9 → Nat) (hz : ∀ i, z i < 2 ^ 107) :
    ∀ i, upperSums z i < 2 ^ 120 ∧ upperSums z i / 2 ^ 52 < 2 ^ 69 := by
  intro i
  have h : upperSums z i < 2 ^ 120 := by
    fin_cases i
    · exact upperSums_bound0 z hz
    · exact upperSums_bound1 z hz
    · exact upperSums_bound2 z hz
    · exact upperSums_bound3 z hz
  exact ⟨h, upper_carry_bound _ h⟩

end Agave.Ed25519.Verifier.Execution.ScalarMontgomeryMul
