import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.MontgomerySchedule

/-! Uniform positive-sum bounds for the actual scalar Montgomery schedule.
These bounds discharge overflow obligations once a source instruction's word
has been related to its indicated natural partial sum. -/
namespace Agave.Ed25519.Verifier.Execution.ScalarMontgomeryMul

open LeanMLIR.RIR
open Agave.Ed25519.ScalarReduce32.Arithmetic
set_option exponentiation.threshold 512

/-- Any product of normalized limbs fits in 104 bits. -/
theorem limb_product_bound (a b : Nat) (ha : a < 2 ^ 52) (hb : b < 2 ^ 52) :
    a * b < 2 ^ 104 := by
  have h := Nat.mul_lt_mul_of_le_of_lt (Nat.le_of_lt ha) hb
    (by decide : 0 < 2 ^ 52)
  norm_num at h ⊢
  exact h

/-- No multiplication column contains more than five 104-bit products. -/
theorem productColumns_bound (a b : Fin 5 → Nat)
    (ha : ∀ i, a i < 2 ^ 52) (hb : ∀ i, b i < 2 ^ 52) :
    ∀ i, productColumns a b i < 2 ^ 107 := by
  intro i
  fin_cases i
  · dsimp [productColumns]
    have h00 := limb_product_bound (a 0) (b 0) (ha 0) (hb 0)
    norm_num at h00 ⊢
    omega
  · dsimp [productColumns]
    have h01 := limb_product_bound (a 0) (b 1) (ha 0) (hb 1)
    have h10 := limb_product_bound (a 1) (b 0) (ha 1) (hb 0)
    norm_num at h01 h10 ⊢
    omega
  · dsimp [productColumns]
    have h02 := limb_product_bound (a 0) (b 2) (ha 0) (hb 2)
    have h11 := limb_product_bound (a 1) (b 1) (ha 1) (hb 1)
    have h20 := limb_product_bound (a 2) (b 0) (ha 2) (hb 0)
    norm_num at h02 h11 h20 ⊢
    omega
  · dsimp [productColumns]
    have h03 := limb_product_bound (a 0) (b 3) (ha 0) (hb 3)
    have h12 := limb_product_bound (a 1) (b 2) (ha 1) (hb 2)
    have h21 := limb_product_bound (a 2) (b 1) (ha 2) (hb 1)
    have h30 := limb_product_bound (a 3) (b 0) (ha 3) (hb 0)
    norm_num at h03 h12 h21 h30 ⊢
    omega
  · dsimp [productColumns]
    have h04 := limb_product_bound (a 0) (b 4) (ha 0) (hb 4)
    have h13 := limb_product_bound (a 1) (b 3) (ha 1) (hb 3)
    have h22 := limb_product_bound (a 2) (b 2) (ha 2) (hb 2)
    have h31 := limb_product_bound (a 3) (b 1) (ha 3) (hb 1)
    have h40 := limb_product_bound (a 4) (b 0) (ha 4) (hb 0)
    norm_num at h04 h13 h22 h31 h40 ⊢
    omega
  · dsimp [productColumns]
    have h14 := limb_product_bound (a 1) (b 4) (ha 1) (hb 4)
    have h23 := limb_product_bound (a 2) (b 3) (ha 2) (hb 3)
    have h32 := limb_product_bound (a 3) (b 2) (ha 3) (hb 2)
    have h41 := limb_product_bound (a 4) (b 1) (ha 4) (hb 1)
    norm_num at h14 h23 h32 h41 ⊢
    omega
  · dsimp [productColumns]
    have h24 := limb_product_bound (a 2) (b 4) (ha 2) (hb 4)
    have h33 := limb_product_bound (a 3) (b 3) (ha 3) (hb 3)
    have h42 := limb_product_bound (a 4) (b 2) (ha 4) (hb 2)
    norm_num at h24 h33 h42 ⊢
    omega
  · dsimp [productColumns]
    have h34 := limb_product_bound (a 3) (b 4) (ha 3) (hb 4)
    have h43 := limb_product_bound (a 4) (b 3) (ha 4) (hb 3)
    norm_num at h34 h43 ⊢
    omega
  · dsimp [productColumns]
    have h44 := limb_product_bound (a 4) (b 4) (ha 4) (hb 4)
    norm_num at h44 ⊢
    omega


end Agave.Ed25519.Verifier.Execution.ScalarMontgomeryMul
