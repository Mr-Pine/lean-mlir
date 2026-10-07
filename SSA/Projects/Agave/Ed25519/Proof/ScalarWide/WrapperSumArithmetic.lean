import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.WrapperSum
import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.MontgomerySchedule

/-! Natural interpretation of the wrapper addition and its final reduction. -/
namespace Agave.Ed25519.Verifier.Execution.ScalarWide
open Agave.Ed25519.Bridge
open Agave.Ed25519.ScalarReduce32.Arithmetic (limbs)
set_option exponentiation.threshold 512

def sumSums (a b : Fin 5 → Nat) : Fin 5 → Nat :=
  let t0 := a 0 + b 0
  let t1 := t0 / 2 ^ 52 + b 1 + a 1
  let t2 := a 2 + b 2 + t1 / 2 ^ 52
  let t3 := a 3 + b 3 + t2 / 2 ^ 52
  let t4 := a 4 + b 4 + t3 / 2 ^ 52
  ![t0, t1, t2, t3, t4]

theorem sumSums_bounds (a b : Fin 5 → Nat)
    (ha : ∀ i, a i < 2 ^ 52) (hb : ∀ i, b i < 2 ^ 52) :
    ∀ i, sumSums a b i < 2 ^ 53 ∧ sumSums a b i / 2 ^ 52 ≤ 1 := by
  let t := sumSums a b
  have h0 : t 0 < 2 ^ 53 ∧ t 0 / 2 ^ 52 ≤ 1 := by
    have ha0 := ha 0
    have hb0 := hb 0
    change a 0 + b 0 < 2 ^ 53 ∧ (a 0 + b 0) / 2 ^ 52 ≤ 1
    norm_num at *
    omega
  have h1 : t 1 < 2 ^ 53 ∧ t 1 / 2 ^ 52 ≤ 1 := by
    have ha1 := ha 1
    have hb1 := hb 1
    have hc := h0.2
    change t 0 / 2 ^ 52 + b 1 + a 1 < 2 ^ 53 ∧
      (t 0 / 2 ^ 52 + b 1 + a 1) / 2 ^ 52 ≤ 1
    norm_num at *
    omega
  have h2 : t 2 < 2 ^ 53 ∧ t 2 / 2 ^ 52 ≤ 1 := by
    have ha2 := ha 2
    have hb2 := hb 2
    have hc := h1.2
    change a 2 + b 2 + t 1 / 2 ^ 52 < 2 ^ 53 ∧
      (a 2 + b 2 + t 1 / 2 ^ 52) / 2 ^ 52 ≤ 1
    norm_num at *
    omega
  have h3 : t 3 < 2 ^ 53 ∧ t 3 / 2 ^ 52 ≤ 1 := by
    have ha3 := ha 3
    have hb3 := hb 3
    have hc := h2.2
    change a 3 + b 3 + t 2 / 2 ^ 52 < 2 ^ 53 ∧
      (a 3 + b 3 + t 2 / 2 ^ 52) / 2 ^ 52 ≤ 1
    norm_num at *
    omega
  have h4 : t 4 < 2 ^ 53 ∧ t 4 / 2 ^ 52 ≤ 1 := by
    have ha4 := ha 4
    have hb4 := hb 4
    have hc := h3.2
    change a 4 + b 4 + t 3 / 2 ^ 52 < 2 ^ 53 ∧
      (a 4 + b 4 + t 3 / 2 ^ 52) / 2 ^ 52 ≤ 1
    norm_num at *
    omega
  intro i
  fin_cases i <;> assumption

theorem sumSums_telescope (a b : Fin 5 → Nat) :
    let t := sumSums a b
    limbs (t 0 % 2 ^ 52) (t 1 % 2 ^ 52) (t 2 % 2 ^ 52)
      (t 3 % 2 ^ 52) (t 4 % 2 ^ 52) + (t 4 / 2 ^ 52) * 2 ^ 260 =
      ScalarMontgomeryMul.limbValue a + ScalarMontgomeryMul.limbValue b := by
  dsimp only
  have h0 := Nat.mod_add_div (sumSums a b 0) (2 ^ 52)
  have h1 := Nat.mod_add_div (sumSums a b 1) (2 ^ 52)
  have h2 := Nat.mod_add_div (sumSums a b 2) (2 ^ 52)
  have h3 := Nat.mod_add_div (sumSums a b 3) (2 ^ 52)
  have h4 := Nat.mod_add_div (sumSums a b 4) (2 ^ 52)
  simp only [sumSums, ScalarMontgomeryMul.limbValue, limbs,
    Agave.Ed25519.ScalarReduce32.Arithmetic.radix, Matrix.cons_val_zero,
    Matrix.cons_val_succ, Matrix.cons_val_fin_one] at *
  norm_num at *
  omega

theorem sumSums_value (a b : Fin 5 → Nat)
    (h : ScalarMontgomeryMul.limbValue a + ScalarMontgomeryMul.limbValue b < 2 ^ 260) :
    let t := sumSums a b
    limbs (t 0 % 2 ^ 52) (t 1 % 2 ^ 52) (t 2 % 2 ^ 52)
      (t 3 % 2 ^ 52) (t 4 % 2 ^ 52) =
      ScalarMontgomeryMul.limbValue a + ScalarMontgomeryMul.limbValue b := by
  have ht := sumSums_telescope a b
  dsimp only at *
  have hz : sumSums a b 4 / 2 ^ 52 = 0 := by
    norm_num at h ht ⊢
    omega
  simpa only [hz, Nat.zero_mul, Nat.add_zero] using ht

end Agave.Ed25519.Verifier.Execution.ScalarWide
