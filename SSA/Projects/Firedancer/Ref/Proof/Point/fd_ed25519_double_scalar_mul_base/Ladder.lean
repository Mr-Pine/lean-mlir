/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.Firedancer.Ref.Spec.Point.fd_ed25519_double_scalar_mul_base
import SSA.Projects.Firedancer.Ref.Spec.Point.Add
import SSA.Projects.Firedancer.Common.Proof.Scalar.fd_curve25519_scalar_wnaf
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Abel

/-!
# The values `fd_ed25519_double_scalar_mul_base` computes

The table `ai[k] = (2k+1)·a` (`aiValue`), the ladder's two half-iterations
(`addDigit_represents`, `addDigitB_value`), and the ladder's closed form `ladder`, whose value from
`0` is the digit sums' multiples of `a` and `G` (`ladder_digitSum`).
-/

namespace Firedancer.Ref.DoubleScalarMulBase
open LeanMLIR SLLVM
open Finset Ed25519

/-- `ai[k]` as `into_precomputed` leaves it: `a`, then `a2 + ai[k - 1]` multiplied out. -/
def aiVal (A : Point) : ℕ → PrecomputedPoint
  | 0 => A.toPrecomputed
  | k + 1 =>
    let Q := aiVal A k
    ((A.dbln 1#32).addPrecomputedPartial
      (if k = 0 then { Q with Z := 1 } else Q)).finalMul.toPrecomputed

/-- `{ Q.toPrecomputed with Z := 1 }` is `Q.toPrecomputed` for `Q.Z = 1`. -/
theorem toPrecomputed_withZ {Q : Point} (hZ : Q.Z = 1) :
    ({ Q.toPrecomputed with Z := 1 } : PrecomputedPoint) = Q.toPrecomputed := by
  simp [Point.toPrecomputed, hZ]

/-- Setting `Z := 1` on `ai[k]`, only ever at `k = 0`, changes nothing for `A.Z = 1`. -/
theorem aiVal_withZ {A : Point} (hZ : A.Z = 1) {k : ℕ} {c : Prop} [Decidable c]
    (hc : c → k = 0) : (if c then { aiVal A k with Z := 1 } else aiVal A k) = aiVal A k := by
  split_ifs with h
  · obtain rfl := hc h
    exact toPrecomputed_withZ hZ
  · rfl

/-- A digit's table index, `d >> 1` at 64 bits, as a natural. -/
theorem shift_toNat (d : BitVec 16) : (BitVec.setWidth 64 d >>> 1).toNat = d.toNat / 2 := by
  simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_eq_of_lt (by have := d.isLt; omega)]

theorem aiVal_succ (A : Point) (k : ℕ) :
    aiVal A (k + 1) = ((A.dbln 1#32).addPrecomputedPartial
      (if k = 0 then { aiVal A k with Z := 1 } else aiVal A k)).finalMul.toPrecomputed := rfl

/-- **`ai[i]` is `(2i+1)·a`**, the precomputed form of a well-formed point. -/
theorem aiValue {A : Point} (hA : A.WellFormed) (hZ : A.Z = 1) (i : ℕ) :
    ∃ (R : Point) (hR : R.WellFormed),
      aiVal A i = R.toPrecomputed ∧ R.toAffine hR = (2 * i + 1) • A.toAffine hA := by
  induction i with
  | zero => exact ⟨A, hA, rfl, by simp⟩
  | succ k ih =>
    obtain ⟨R, hR, hQ, hval⟩ := ih
    have h2 := Point.wellFormed_dbln 1#32 hA
    refine ⟨(A.dbln 1#32).addPrecomputed R.toPrecomputed,
      Point.wellFormed_addPrecomputed h2 hR, ?_, ?_⟩
    · rw [aiVal_succ, aiVal_withZ hZ id, hQ, Point.finalMul_addPrecomputedPartial]
    · rw [Point.toAffine_addPrecomputed h2 hR, hval, Point.toAffine_dbln hA]
      simp only [show dblnCount 1#32 = 1 by decide, pow_one, ← add_nsmul]
      congr 1
      ring

/-- `r` and `t` after `^bb8`–`^bb11` from `r = R` and digit `d`: `t` is `R` partially doubled; a
nonzero `d` finishes that into `r` and adds `ai[|d| >> 1]` to it, negated for `d < 0`, with
`Z := 1` at `|d| = 1`. -/
def addDigit (A R : Point) (d : BitVec 16) : Point × Point :=
  if 0#16 <ₛ d then
    (R.partialDbl.finalMul, R.partialDbl.finalMul.addPrecomputedPartial
      (if d = 1#16 then { aiVal A (BitVec.setWidth 64 d >>> 1).toNat with Z := 1 }
        else aiVal A (BitVec.setWidth 64 d >>> 1).toNat))
  else if d <ₛ 0#16 then
    (R.partialDbl.finalMul, R.partialDbl.finalMul.addPrecomputedPartial
      (if d = 65535#16 then { aiVal A (BitVec.setWidth 64 (-d) >>> 1).toNat with Z := 1 }
        else aiVal A (BitVec.setWidth 64 (-d) >>> 1).toNat).neg)
  else (R, R.partialDbl)

theorem addDigit_pos {A R : Point} {d : BitVec 16} (h : (0#16 <ₛ d) = true) :
    addDigit A R d = (R.partialDbl.finalMul, R.partialDbl.finalMul.addPrecomputedPartial
      (if d = 1#16 then { aiVal A (BitVec.setWidth 64 d >>> 1).toNat with Z := 1 }
        else aiVal A (BitVec.setWidth 64 d >>> 1).toNat)) := by
  rw [addDigit, if_pos h]

theorem addDigit_neg {A R : Point} {d : BitVec 16} (h0 : ¬(0#16 <ₛ d) = true)
    (h : (d <ₛ 0#16) = true) :
    addDigit A R d = (R.partialDbl.finalMul, R.partialDbl.finalMul.addPrecomputedPartial
      (if d = 65535#16 then { aiVal A (BitVec.setWidth 64 (-d) >>> 1).toNat with Z := 1 }
        else aiVal A (BitVec.setWidth 64 (-d) >>> 1).toNat).neg) := by
  rw [addDigit, if_neg h0, if_pos h]

theorem addDigit_zero {A R : Point} {d : BitVec 16} (h0 : ¬(0#16 <ₛ d) = true)
    (h : ¬(d <ₛ 0#16) = true) : addDigit A R d = (R, R.partialDbl) := by
  rw [addDigit, if_neg h0, if_neg h]

/-- `t` finished after `^bb8`–`^bb11`: `2R + d·A`, for `d` zero or odd in `[-15, 15]`. -/
theorem addDigit_value {A R : Point} (hA : A.WellFormed) (hZ : A.Z = 1) (hR : R.WellFormed)
    {d : BitVec 16} (hd : d = 0 ∨ d.toInt % 2 = 1) (hb : |d.toInt| ≤ 15) :
    ∃ h : (addDigit A R d).2.finalMul.WellFormed,
      (addDigit A R d).2.finalMul.toAffine h = 2 • R.toAffine hR + d.toInt • A.toAffine hA := by
  have hR₂ := Point.wellFormed_dbl hR
  rcases hd with h | h
  · subst h
    rw [addDigit_zero (by decide) (by decide), Point.finalMul_partialDbl]
    exact ⟨hR₂, by rw [Point.toAffine_dbl hR]; simp [two_nsmul]⟩
  have hc := BitVec.toInt_eq_toNat_cond d
  have := d.isLt
  rw [abs_le] at hb
  by_cases hp : (0#16 <ₛ d) = true
  · rw [addDigit_pos hp]
    have hgt : 0 < d.toInt := by simpa [BitVec.slt] using hp
    obtain ⟨Q, hQ, hQv, hval⟩ := aiValue hA hZ (d.toNat / 2)
    -- the entry added, `Z := 1` at `d = 1` or not, is `Q`'s precomputed form
    have hE : (if d = 1#16 then { aiVal A (BitVec.setWidth 64 d >>> 1).toNat with Z := 1 }
        else aiVal A (BitVec.setWidth 64 d >>> 1).toNat) = Q.toPrecomputed :=
      (aiVal_withZ hZ fun h1 => by subst h1; decide).trans (by rw [shift_toNat]; exact hQv)
    rw [hE, Point.finalMul_addPrecomputedPartial, Point.finalMul_partialDbl]
    refine ⟨Point.wellFormed_addPrecomputed hR₂ hQ, ?_⟩
    rw [Point.toAffine_addPrecomputed hR₂ hQ, Point.toAffine_dbl hR, hval, ← natCast_zsmul,
      ← two_nsmul, show ((2 * (d.toNat / 2) + 1 : ℕ) : ℤ) = d.toInt by
        split_ifs at hc <;> omega]
  by_cases hn : (d <ₛ 0#16) = true
  · rw [addDigit_neg hp hn]
    have hlt : d.toInt < 0 := by simpa [BitVec.slt] using hn
    have hneg : (-d).toNat = 65536 - d.toNat := by
      rw [BitVec.toNat_neg]; split_ifs at hc <;> omega
    obtain ⟨Q, hQ, hQv, hval⟩ := aiValue hA hZ ((-d).toNat / 2)
    -- the entry added, `Z := 1` at `d = -1` or not, is `Q`'s precomputed form
    have hE : (if d = 65535#16 then { aiVal A (BitVec.setWidth 64 (-d) >>> 1).toNat with Z := 1 }
        else aiVal A (BitVec.setWidth 64 (-d) >>> 1).toNat) = Q.toPrecomputed :=
      (aiVal_withZ hZ fun h1 => by subst h1; decide).trans (by rw [shift_toNat]; exact hQv)
    rw [hE, Point.finalMul_addPrecomputedPartial, Point.finalMul_partialDbl]
    refine ⟨Point.wellFormed_addPrecomputed_neg hR₂ hQ, ?_⟩
    rw [Point.toAffine_addPrecomputed_neg hR₂ hQ, Point.toAffine_dbl hR, hval, ← natCast_zsmul,
      ← two_nsmul, sub_eq_add_neg, ← neg_zsmul, show -((2 * ((-d).toNat / 2) + 1 : ℕ) : ℤ) = d.toInt by
        rw [hneg]; split_ifs at hc <;> omega]
  · have h0 : d = 0 := by simp only [Bool.not_eq_true] at hp hn; bv_decide
    simp [h0] at h

/-- `addDigit`'s `t` reads `R`'s `X, Y, Z` only. -/
theorem addDigit_fixT (A R : Point) (d : BitVec 16) :
    (addDigit A R.fixT d).2 = (addDigit A R d).2 := by
  unfold addDigit; split_ifs <;> rfl

/-- `addDigit_value` for `R` representing `X` up to `T`. -/
theorem addDigit_represents {A R : Point} {X : Edwards.Point curve}
    (hA : A.WellFormed) (hZ : A.Z = 1) (hR : R.Represents X) {d : BitVec 16}
    (hd : d = 0 ∨ d.toInt % 2 = 1) (hb : |d.toInt| ≤ 15) :
    ∃ h : (addDigit A R d).2.finalMul.WellFormed,
      (addDigit A R d).2.finalMul.toAffine h = 2 • X + d.toInt • A.toAffine hA := by
  obtain ⟨h, hv⟩ := addDigit_value hA hZ hR.wellFormed_fixT hd hb
  have e := addDigit_fixT A R d
  refine ⟨e ▸ h, ?_⟩
  rw [← hR.toAffine_fixT, ← hv]
  exact Point.toAffine_congr (congrArg _ e.symm) _ _

/-- `r` and `t` after `^bb12`–`^bb15` from `r = R`, `t = T` and digit `d`, `B` the base-point
table's entries: a nonzero `d` finishes `T` into `r` and adds `B (|d| >> 1)` to it at `Z := 1`,
negated for `d < 0`. -/
def addDigitB (B : ℕ → PrecomputedPoint) (R T : Point) (d : BitVec 16) :
    Point × Point :=
  if 0#16 <ₛ d then
    (T.finalMul, T.finalMul.addPrecomputedPartial
      { B (BitVec.setWidth 64 d >>> 1).toNat with Z := 1 })
  else if d <ₛ 0#16 then
    (T.finalMul, T.finalMul.addPrecomputedPartial
      ({ B (BitVec.setWidth 64 (-d) >>> 1).toNat with Z := 1 } : PrecomputedPoint).neg)
  else (R, T)

theorem addDigitB_pos {B : ℕ → PrecomputedPoint} {R T : Point} {d : BitVec 16}
    (h : (0#16 <ₛ d) = true) :
    addDigitB B R T d = (T.finalMul, T.finalMul.addPrecomputedPartial
      { B (BitVec.setWidth 64 d >>> 1).toNat with Z := 1 }) := by
  rw [addDigitB, if_pos h]

theorem addDigitB_neg {B : ℕ → PrecomputedPoint} {R T : Point} {d : BitVec 16}
    (h0 : ¬(0#16 <ₛ d) = true) (h : (d <ₛ 0#16) = true) :
    addDigitB B R T d = (T.finalMul, T.finalMul.addPrecomputedPartial
      ({ B (BitVec.setWidth 64 (-d) >>> 1).toNat with Z := 1 } : PrecomputedPoint).neg) :=
    by
  rw [addDigitB, if_neg h0, if_pos h]

theorem addDigitB_zero {B : ℕ → PrecomputedPoint} {R T : Point} {d : BitVec 16}
    (h0 : ¬(0#16 <ₛ d) = true) (h : ¬(d <ₛ 0#16) = true) : addDigitB B R T d = (R, T) := by
  rw [addDigitB, if_neg h0, if_neg h]

theorem addDigitB_value {B : ℕ → PrecomputedPoint} {G R T : Point}
    (hG : G.WellFormed) (hB : BaseVals B G hG)
    (hT : T.finalMul.WellFormed) {d : BitVec 16} (hd : d = 0 ∨ d.toInt % 2 = 1)
    (hb : |d.toInt| ≤ 255) :
    ∃ h : (addDigitB B R T d).2.finalMul.WellFormed,
      (addDigitB B R T d).2.finalMul.toAffine h
        = T.finalMul.toAffine hT + d.toInt • G.toAffine hG := by
  rcases hd with h | h
  · subst h
    rw [addDigitB_zero (by decide) (by decide)]
    exact ⟨hT, by simp⟩
  have hc := BitVec.toInt_eq_toNat_cond d
  have := d.isLt
  rw [abs_le] at hb
  by_cases hp : (0#16 <ₛ d) = true
  · rw [addDigitB_pos hp]
    have hk := shift_toNat d
    have hgt : 0 < d.toInt := by simpa [BitVec.slt] using hp
    obtain ⟨Q, hQ, hQZ, hBQ, hval⟩ := hB (d.toNat / 2) (by split_ifs at hc <;> omega)
    rw [hk, hBQ, toPrecomputed_withZ hQZ, Point.finalMul_addPrecomputedPartial]
    refine ⟨Point.wellFormed_addPrecomputed hT hQ, ?_⟩
    rw [Point.toAffine_addPrecomputed hT hQ, hval, ← natCast_zsmul]
    congr 2
    split_ifs at hc <;> omega
  by_cases hn : (d <ₛ 0#16) = true
  · rw [addDigitB_neg hp hn]
    have hk := shift_toNat (-d)
    have hlt : d.toInt < 0 := by simpa [BitVec.slt] using hn
    have hneg : (-d).toNat = 65536 - d.toNat := by
      rw [BitVec.toNat_neg]; split_ifs at hc <;> omega
    obtain ⟨Q, hQ, hQZ, hBQ, hval⟩ := hB ((-d).toNat / 2) (by rw [hneg]; split_ifs at hc <;> omega)
    rw [hk, hBQ, toPrecomputed_withZ hQZ, Point.finalMul_addPrecomputedPartial]
    refine ⟨Point.wellFormed_addPrecomputed_neg hT hQ, ?_⟩
    rw [Point.toAffine_addPrecomputed_neg hT hQ, hval, ← natCast_zsmul, sub_eq_add_neg,
      ← neg_zsmul]
    congr 2
    rw [hneg]
    split_ifs at hc <;> omega
  · have h0 : d = 0 := by simp only [Bool.not_eq_true] at hp hn; bv_decide
    simp [h0] at h

/-! ## The ladder -/

/-- One ladder iteration at position `j`: double `X`, add `d₁ⱼ·A` and `d₂ⱼ·G`. -/
def ladderStep (A G X : Edwards.Point curve) (w₁ w₂ : BitVec 4096) (j : ℕ) : Edwards.Point curve :=
  2 • X + (Common.Wnaf.slot w₁ j).toInt • A + (Common.Wnaf.slot w₂ j).toInt • G

/-- The ladder from `X` over positions `j` down to `0`:
`2^(j+1)·X + ∑ i ≤ j, 2^i·(d₁ᵢ·A + d₂ᵢ·G)`. -/
def ladder (A G X : Edwards.Point curve) (w₁ w₂ : BitVec 4096) (j : ℕ) : Edwards.Point curve :=
  2 ^ (j + 1) • X + ∑ i ∈ range (j + 1),
    (((Common.Wnaf.slot w₁ i).toInt * 2 ^ i) • A + ((Common.Wnaf.slot w₂ i).toInt * 2 ^ i) • G)

section Ladder
variable {A G X : Edwards.Point curve} {w₁ w₂ : BitVec 4096}

theorem ladder_zero : ladder A G X w₁ w₂ 0 = ladderStep A G X w₁ w₂ 0 := by
  simp [ladder, ladderStep, add_assoc]

theorem ladder_succ (j : ℕ) :
    ladder A G X w₁ w₂ (j + 1) = ladder A G (ladderStep A G X w₁ w₂ (j + 1)) w₁ w₂ j := by
  simp only [ladder, ladderStep]
  rw [Finset.sum_range_succ _ (j + 1)]
  generalize (∑ x ∈ range (j + 1), (((Common.Wnaf.slot w₁ x).toInt * 2 ^ x) • A
    + ((Common.Wnaf.slot w₂ x).toInt * 2 ^ x) • G) : Edwards.Point curve) = S
  rw [smul_add, smul_add, smul_smul, ← pow_succ, mul_smul, mul_smul,
    smul_comm (2 ^ (j + 1)) (Common.Wnaf.slot w₁ (j + 1)).toInt A,
    smul_comm (2 ^ (j + 1)) (Common.Wnaf.slot w₂ (j + 1)).toInt G]
  simp only [← natCast_zsmul, Nat.cast_pow, Nat.cast_ofNat]
  abel

/-- Zero digits above `i` add nothing. -/
theorem ladder_skip {i : ℕ} (hi : i < 256)
    (hz : ∀ k, i < k → k ≤ 255 → Common.Wnaf.slot w₁ k = 0 ∧ Common.Wnaf.slot w₂ k = 0) :
    ladder A G 0 w₁ w₂ i = ladder A G 0 w₁ w₂ 255 := by
  obtain ⟨j, hj⟩ : ∃ j, 256 = (i + 1) + j := ⟨256 - i - 1, by omega⟩
  simp only [ladder, smul_zero, zero_add, show 255 + 1 = 256 from rfl, hj,
    Finset.sum_range_add _ _ j, left_eq_add]
  refine Finset.sum_eq_zero fun x hx => ?_
  have := hz (i + 1 + x) (by omega) (by simp at hx; omega)
  simp [this.1, this.2]

theorem ladder_all_zero
    (hz : ∀ k ≤ 255, Common.Wnaf.slot w₁ k = 0 ∧ Common.Wnaf.slot w₂ k = 0) :
    ladder A G 0 w₁ w₂ 255 = 0 := by
  simp only [ladder, smul_zero, zero_add]
  refine Finset.sum_eq_zero fun x hx => ?_
  have := hz x (by simp at hx; omega)
  simp [this.1, this.2]

/-- `∑ i < K, dᵢ·2^i` over `w`'s digits is wnaf's `digitSum`. -/
theorem sum_slot_eq_digitSum (w : BitVec 4096) (K : ℕ) :
    ∑ i ∈ range K, (Common.Wnaf.slot w i).toInt * 2 ^ i = Common.digitSum w K := by
  induction K with
  | zero => rfl
  | succ K ih => rw [Finset.sum_range_succ, ih]; rfl

/-- The ladder's value from `0`: the digit sums' multiples of `A` and `G`. -/
theorem ladder_digitSum :
    ladder A G 0 w₁ w₂ 255 = Common.digitSum w₁ 256 • A + Common.digitSum w₂ 256 • G := by
  simp only [ladder, smul_zero, zero_add, Finset.sum_add_distrib, ← Finset.sum_smul,
    sum_slot_eq_digitSum]

end Ladder

theorem toAffine_zero : Point.zero.toAffine Point.wellFormed_zero = 0 :=
  Edwards.Point.ext (by simp [Point.toAffine, Point.x, Point.zero])
    (by simp [Point.toAffine, Point.y, Point.zero])

end Firedancer.Ref.DoubleScalarMulBase
