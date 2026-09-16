/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.Firedancer.Avx512.Spec.Field.fd_r43x6_mod_nearly_reduced_limbs
import Mathlib.Data.ZMod.Basic

/-!
# `fd_r43x6_mod_nearly_reduced_limbs` returns the canonical representative

Every theorem here assumes `MnrPre`, the nearly reduced contract of the header
spelled out on the six `long`s the macro is handed rather than on a vector;
`bcp_nearlyReduced` is what supplies it. Limb 5's `< 2^41` is not among its
conditions, since it follows from the bound on the packed value.

* **`mnrQ_spec`, the decision.** `q` is `0` or `1`, and it is `1` exactly when
  the input is at least `p`. This is where the packed bound is spent: `q` is
  bit 40 of limb 5 of `x + 19`, and it is a single bit only because `x < 2p`.

* **`decodeLimbs_mnr`, the value.** Exactly `q · p` comes off. `mnr_congr` is
  that in `ZMod p`; `decodeLimbs_mnr_eq_emod` is it together with the range,
  and says the output is `decodeLimbs y % p`.

* **`mnr_reduced`, the range.** The output is in the `reduced` class of the
  header's table, hence the unique representation of its element -- which is
  what a caller reading `!!(l0|…|l5)` off the end needs.

* **`mnr_chain_fitsLong` and `mnrA_nonneg`**, the `nsw` and `nuw` obligations
  of the emitted code. The `x + 19` chain is marked `nuw` and shifts with
  `lshr`, so it has to stay non-negative. The borrow chain after it is `nsw`
  alone and shifts with `ashr`: `mnrE y 0` is negative exactly when the
  conditional subtract fires, and the borrow travels down the limbs as `-1`.

The arithmetic is all `omega` once `R43x6.shiftRight_eq` has turned the shifts
into division; the borrow bound `mnrE y i ∈ [-1, 2^43)` is derived on the way
rather than stated.
-/

namespace Firedancer.Avx512

/-- The nearly reduced contract, as `fd_r43x6_mod_nearly_reduced_limbs` needs
it: limbs 0-4 in `[0,2^43)`, limb 5 non-negative, packed value below `2p`. -/
def MnrPre (y : Fin R43x6.limbCount → ℤ) : Prop :=
  (∀ i : Fin R43x6.limbCount, (i : ℕ) < 5 → 0 ≤ y i ∧ y i < 2 ^ 43) ∧
    0 ≤ y 5 ∧ R43x6.decodeLimbs y < 2 * (p : ℤ)

/-- `MnrPre` in the form the `omega` calls consume it. -/
private theorem MnrPre.bounds {y : Fin R43x6.limbCount → ℤ} (h : MnrPre y) :
    (0 ≤ y 0 ∧ y 0 < 2 ^ 43) ∧
      (0 ≤ y 1 ∧ y 1 < 2 ^ 43) ∧
      (0 ≤ y 2 ∧ y 2 < 2 ^ 43) ∧
      (0 ≤ y 3 ∧ y 3 < 2 ^ 43) ∧
      (0 ≤ y 4 ∧ y 4 < 2 ^ 43) ∧
      (0 ≤ y 5) ∧
      y 0 + 2 ^ 43 * y 1 + 2 ^ 86 * y 2 + 2 ^ 129 * y 3 + 2 ^ 172 * y 4 + 2 ^ 215 * y 5 <
        2 * (2 ^ 255 - 19) := by
  obtain ⟨h04, h50, hs⟩ := h
  simp only [R43x6.decodeLimbs_eq, p_int] at hs
  exact
    ⟨h04 0 (by decide), h04 1 (by decide), h04 2 (by decide), h04 3 (by decide), h04 4 (by decide),
      h50, hs⟩

/-! ## The decision -/

/-- **`q` is the top bit of `x + 19`**: `0` below `p` and `1` from `p` up. -/
theorem mnrQ_spec {y : Fin R43x6.limbCount → ℤ} (h : MnrPre y) :
    (mnrQ y = 0 ↔ R43x6.decodeLimbs y < (p : ℤ)) ∧
      (mnrQ y = 1 ↔ (p : ℤ) ≤ R43x6.decodeLimbs y) := by
  obtain ⟨h0, h1, h2, h3, h4, h5, hs⟩ := h.bounds
  simp only [R43x6.decodeLimbs_eq, p_int]
  simp only [mnrQ, mnrA, R43x6.limbs6_zero, R43x6.limbs6_one, R43x6.limbs6_two, R43x6.limbs6_three,
    R43x6.limbs6_four, R43x6.limbs6_five, R43x6.shiftRight_eq]
  omega

/-! ## The value -/

/-- **Exactly `q · p` comes off.** -/
theorem decodeLimbs_mnr {y : Fin R43x6.limbCount → ℤ} (h : MnrPre y) :
    R43x6.decodeLimbs (mnr y) =
      R43x6.decodeLimbs y - (if R43x6.decodeLimbs y < (p : ℤ) then 0 else (p : ℤ)) := by
  obtain ⟨h0, h1, h2, h3, h4, h5, hs⟩ := h.bounds
  simp only [mnr, mnrE, mnrA, mnrQ, R43x6.decodeLimbs_eq, R43x6.limbs6_zero, R43x6.limbs6_one,
    R43x6.limbs6_two, R43x6.limbs6_three, R43x6.limbs6_four, R43x6.limbs6_five, R43x6.shiftRight_eq,
    p_int]
  split <;> split <;> omega

/-- **The element is preserved.** -/
theorem mnr_congr {y : Fin R43x6.limbCount → ℤ} (h : MnrPre y) :
    ((R43x6.decodeLimbs (mnr y) : ℤ) : ZMod p) = ((R43x6.decodeLimbs y : ℤ) : ZMod p) := by
  refine intCast_eq_of_sub_mul (k := if R43x6.decodeLimbs y < (p : ℤ) then 0 else 1) ?_
  rw [decodeLimbs_mnr h]; split <;> ring

/-! ## The range -/

/-- **The output is reduced**, limb widths and packed value both: limbs 0-4
below `2^43`, limb 5 below `2^40`, and the value in `[0,p)`. -/
theorem mnr_reduced {y : Fin R43x6.limbCount → ℤ} (h : MnrPre y) :
    (∀ i : Fin R43x6.limbCount, (i : ℕ) < 5 → 0 ≤ mnr y i ∧ mnr y i < 2 ^ 43) ∧
      (0 ≤ mnr y 5 ∧ mnr y 5 < 2 ^ 40) ∧
      (0 ≤ R43x6.decodeLimbs (mnr y) ∧ R43x6.decodeLimbs (mnr y) < (p : ℤ)) := by
  have hv := decodeLimbs_mnr h
  obtain ⟨h0, h1, h2, h3, h4, h5, hs⟩ := h.bounds
  refine ⟨fun k hk => ?_, ?_, ?_, ?_⟩
  · simp only [mnr, mnrE, mnrA, mnrQ, R43x6.limbs6_zero, R43x6.limbs6_one, R43x6.limbs6_two,
      R43x6.limbs6_three, R43x6.limbs6_four, R43x6.limbs6_five, R43x6.shiftRight_eq]
    fin_cases k <;> simp_all <;> omega
  · simp only [mnr, mnrE, mnrA, mnrQ, R43x6.limbs6_zero, R43x6.limbs6_one, R43x6.limbs6_two,
      R43x6.limbs6_three, R43x6.limbs6_four, R43x6.limbs6_five, R43x6.shiftRight_eq]
    simp; split <;> omega
  · rw [hv]; simp only [R43x6.decodeLimbs_eq, p_int] at hs ⊢; split <;> omega
  · rw [hv]; simp only [R43x6.decodeLimbs_eq, p_int] at hs ⊢; split <;> omega

/-- **The output is the canonical representative.** The range and the value
together: `mnr` computes `decodeLimbs y % p` on the nose. -/
theorem decodeLimbs_mnr_eq_emod {y : Fin R43x6.limbCount → ℤ} (h : MnrPre y) :
    R43x6.decodeLimbs (mnr y) = R43x6.decodeLimbs y % (p : ℤ) := by
  have hnn := R43x6.decodeLimbs_nonneg (fun i hi => (h.1 i hi).1) h.2.1
  have hlt := h.2.2
  rw [decodeLimbs_mnr h, p_int] at *
  split <;> omega

/-! ## `nsw` and `nuw` -/

/-- Every value of the `x + 19` chain fits a `long`. -/
theorem mnrA_fitsLong {y : Fin R43x6.limbCount → ℤ} (h : MnrPre y) (i : Fin R43x6.limbCount) :
    R43x6.FitsLong (mnrA y i) := by
  obtain ⟨h0, h1, h2, h3, h4, h5, hs⟩ := h.bounds
  simp only [R43x6.FitsLong, mnrA, R43x6.limbs6_zero, R43x6.limbs6_one, R43x6.limbs6_two,
    R43x6.limbs6_three, R43x6.limbs6_four, R43x6.limbs6_five, R43x6.shiftRight_eq]
  fin_cases i <;> simp_all <;> omega

/-- Every value of the borrow chain fits a `long`. Limb 5 is not one of them:
the borrow chain has no limb 5, and `mnr_limb5_fitsLong` covers the value that
replaces it. -/
theorem mnrE_fitsLong {y : Fin R43x6.limbCount → ℤ} (h : MnrPre y) (i : Fin R43x6.limbCount) :
    R43x6.FitsLong (mnrE y i) := by
  obtain ⟨h0, h1, h2, h3, h4, h5, hs⟩ := h.bounds
  simp only [R43x6.FitsLong, mnrE, mnrA, mnrQ, R43x6.limbs6_zero, R43x6.limbs6_one,
    R43x6.limbs6_two, R43x6.limbs6_three, R43x6.limbs6_four, R43x6.limbs6_five, R43x6.shiftRight_eq]
  fin_cases i <;> simp_all <;> (try split) <;> omega

/-- The output's limb 5 fits a `long`. -/
theorem mnr_limb5_fitsLong {y : Fin R43x6.limbCount → ℤ} (h : MnrPre y) :
    R43x6.FitsLong (mnrA y 5 % 2 ^ 40 + (mnrE y 4 >>> 43)) := by
  obtain ⟨h0, h1, h2, h3, h4, h5, hs⟩ := h.bounds
  simp only [R43x6.FitsLong, mnrE, mnrA, mnrQ, R43x6.limbs6_zero, R43x6.limbs6_one,
    R43x6.limbs6_two, R43x6.limbs6_three, R43x6.limbs6_four, R43x6.limbs6_five, R43x6.shiftRight_eq]
  split <;> omega

/-- **No intermediate overflows a `long`.** Nothing here is anywhere near the
edge -- every value is below `2^44` in absolute value -- but the emitted code
marks the whole chain `nsw`, so it is still an obligation of the
denotation. -/
theorem mnr_chain_fitsLong {y : Fin R43x6.limbCount → ℤ} (h : MnrPre y) :
    ∀ v ∈ mnrChain y, R43x6.FitsLong v := by
  obtain ⟨h0, h1, h2, h3, h4, h5, hs⟩ := h.bounds
  intro v hv
  simp only [mnrChain, mnrE, mnrA, mnrQ, R43x6.limbs6_zero, R43x6.limbs6_one, R43x6.limbs6_two,
    R43x6.limbs6_three, R43x6.limbs6_four, R43x6.limbs6_five, R43x6.shiftRight_eq, List.mem_cons,
    List.not_mem_nil, or_false] at hv
  simp only [R43x6.FitsLong]
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    (try split) <;>
    omega

/-- **The `x + 19` chain is non-negative.** Its adds are the ones the emitted
code marks `nuw` on top of `nsw`, and its shifts are `lshr` rather than
`ashr`, so this is what both of those need. The borrow chain that follows is
deliberately not covered: `mnrE y 0` is negative exactly when the conditional
subtract fires, and `mnrE y 1`-`mnrE y 4` are `-1` while the borrow
propagates, which is why the emitted code shifts them with `ashr` and marks
them `nsw` alone. -/
theorem mnrA_nonneg {y : Fin R43x6.limbCount → ℤ} (h : MnrPre y) : ∀ i, 0 ≤ mnrA y i := by
  obtain ⟨h0, h1, h2, h3, h4, h5, hs⟩ := h.bounds
  intro i
  simp only [mnrA, R43x6.limbs6_zero, R43x6.limbs6_one, R43x6.limbs6_two, R43x6.limbs6_three,
    R43x6.limbs6_four, R43x6.limbs6_five, R43x6.shiftRight_eq]
  fin_cases i <;> simp_all <;> omega

end Firedancer.Avx512
