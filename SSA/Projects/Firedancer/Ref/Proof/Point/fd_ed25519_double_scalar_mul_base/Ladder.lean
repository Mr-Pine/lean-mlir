/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.Firedancer.Ref.Spec.Point.fd_ed25519_double_scalar_mul_base
import SSA.Projects.Firedancer.Ref.Spec.Point.Add
import SSA.Projects.Firedancer.Common.Proof.fd_ed25519_double_scalar_mul_base

/-!
# The values ref's `fd_ed25519_double_scalar_mul_base` computes

The table `ai[k]` (`aiVal`) and the ladder's two half-iterations (`addDigit_represents`,
`addDigitB_value`), each `Common.DoubleScalarMulBase.addSigned_value` once the partial
multiplications and `Z := 1` flags are multiplied out.
-/

namespace Firedancer.Ref.DoubleScalarMulBase
open LeanMLIR SLLVM
open Common.DoubleScalarMulBase Ed25519

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

theorem aiVal_succ (A : Point) (k : ℕ) :
    aiVal A (k + 1) = ((A.dbln 1#32).addPrecomputedPartial
      (if k = 0 then { aiVal A k with Z := 1 } else aiVal A k)).finalMul.toPrecomputed := rfl

theorem aiVal_succ' {A : Point} (hZ : A.Z = 1) (k : ℕ) :
    aiVal A (k + 1) = ((A.dbln 1#32).addPrecomputed (aiVal A k)).toPrecomputed := by
  rw [aiVal_succ, aiVal_withZ hZ id, Point.finalMul_addPrecomputedPartial]

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

/-- `t` finished is `2R` plus the digit's entry. -/
theorem addDigit_finalMul {A R : Point} (hZ : A.Z = 1) (d : BitVec 16) :
    (addDigit A R d).2.finalMul = addSigned R.dbl (aiVal A) d := by
  by_cases hp : (0#16 <ₛ d) = true
  · rw [addDigit_pos hp, addSigned, if_pos hp, aiVal_withZ hZ fun h1 => by subst h1; decide]
    rfl
  by_cases hn : (d <ₛ 0#16) = true
  · rw [addDigit_neg hp hn, addSigned, if_neg hp, if_pos hn,
      aiVal_withZ hZ fun h1 => by subst h1; decide]
    rfl
  · rw [addDigit_zero hp hn, addSigned, if_neg hp, if_neg hn]
    rfl

/-- `t` finished after `^bb8`–`^bb11`: `2R + d·A`, for `d` zero or odd in `[-15, 15]`. -/
theorem addDigit_value {A R : Point} (hA : A.WellFormed) (hZ : A.Z = 1) (hR : R.WellFormed)
    {d : BitVec 16} (hd : d = 0 ∨ d.toInt % 2 = 1) (hb : |d.toInt| ≤ 15) :
    ∃ h : (addDigit A R d).2.finalMul.WellFormed,
      (addDigit A R d).2.finalMul.toAffine h = 2 • R.toAffine hR + d.toInt • A.toAffine hA := by
  obtain ⟨h, hv⟩ := addSigned_value (Point.wellFormed_dbl hR)
    (oddMultiples_of_succ hA (E := aiVal A) rfl (aiVal_succ' hZ) 8) hd (by omega)
  rw [addDigit_finalMul hZ]
  exact ⟨h, by rw [hv, Point.toAffine_dbl hR, two_nsmul]⟩

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
  have e : (addDigitB B R T d).2.finalMul
      = addSigned T.finalMul (fun k => ({ B k with Z := 1 } : PrecomputedPoint)) d := by
    unfold addDigitB addSigned; split_ifs <;> rfl
  have hE : OddMultiples (fun k => ({ B k with Z := 1 } : PrecomputedPoint)) (G.toAffine hG) 128 :=
    fun k hk => (hB k hk).elim fun Q h => h.elim fun hQ h =>
      ⟨Q, hQ, by simp only [h.2.1, toPrecomputed_withZ h.1], h.2.2⟩
  obtain ⟨h, hv⟩ := addSigned_value hT hE hd (by omega)
  rw [e]
  exact ⟨h, hv⟩

end Firedancer.Ref.DoubleScalarMulBase
