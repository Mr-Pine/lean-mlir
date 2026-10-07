import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.CancellationRefinement
import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.UpperBounds

/-! Exact natural interpretation of the four high carry sums and all five
quotient limb words. The top truncation has an explicit independent bound. -/
namespace Agave.Ed25519.Verifier.Execution.ScalarMontgomeryMul

open Agave.Ed25519.ScalarReduce32.Arithmetic
set_option exponentiation.threshold 512
set_option maxRecDepth 100000

attribute [local irreducible] wordCancellationSums sourceCarryWord digitWord
  upperSums cancellationSums

theorem ushift52_repr (word : BitVec 128) (value : Nat) (h : word.toNat = value) :
    word >>> (52 : Nat) = BitVec.ofNat 128 (value / 2 ^ 52) := by
  have he : (word >>> (52 : Nat)).toNat = value / 2 ^ 52 := by
    rw [BitVec.toNat_ushiftRight, h, Nat.shiftRight_eq_div_pow]
  exact (BitVec.toNat_eq_nat.mp he).2

private theorem upper_reorder5 (c z p q r : Nat) :
    p + z + q + r + c = c + z + p + q + r := by omega

private theorem upper_reorder4 (c z p q : Nat) :
    p + z + q + c = c + z + p + q := by omega

private theorem upper_reorder3 (c z p : Nat) :
    p + z + c = c + z + p := by omega

/-- All four actual high sums equal the natural repacking schedule. -/
theorem wordUpperSums_toNat (z : Fin 9 → BitVec 128)
    (hz : ∀ i, (z i).toNat < 2 ^ 107) :
    ∀ i, (wordUpperSums z i).toNat = upperSums (fun j => (z j).toNat) i := by
  let w := wordCancellationSums z
  let t := cancellationSums (fun j => (z j).toNat)
  let wq := wordUpperSums z
  let q := upperSums (fun j => (z j).toNat)
  have hq := upperSums_bounds (fun j => (z j).toNat) hz
  have hd (i : Fin 5) := wordCancellationDigits_repr z hz i
  have hc := wordCancellationCarry_repr z hz 4
  have r0 : wq 0 = BitVec.ofNat 128 (q 0) := by
    change ((digitWord (w 1)).setWidth 128 <<< (44 : Nat)) + z 5 +
      (digitWord (w 3)).setWidth 128 * 1367801#128 +
      (digitWord (w 4)).setWidth 128 * 3916664325105025#128 + sourceCarryWord (w 4) = _
    conv_lhs =>
      rw [hd 1, hd 3, hd 4, hc, word_repr (z 5)]
      rw [ofNat_shift44 _ ((adjustmentDigit_bound (t 1)).trans (by decide))]
      simp only [← BitVec.ofNat_mul, ← BitVec.ofNat_add]
    apply congrArg (BitVec.ofNat 128)
    exact (upper_reorder5 _ _ _ _ _).trans (upperSums_zero _).symm
  have h0 : (wq 0).toNat = q 0 :=
    BitVec.toNat_eq_nat.mpr ⟨(hq 0).1.trans (by decide), r0⟩
  have c0 := ushift52_repr (wq 0) (q 0) h0
  have r1 : wq 1 = BitVec.ofNat 128 (q 1) := by
    change ((digitWord (w 2)).setWidth 128 <<< (44 : Nat)) + z 6 +
      (digitWord (w 4)).setWidth 128 * 1367801#128 + (wq 0 >>> (52 : Nat)) = _
    conv_lhs =>
      rw [hd 2, hd 4, c0, word_repr (z 6)]
      rw [ofNat_shift44 _ ((adjustmentDigit_bound (t 2)).trans (by decide))]
      simp only [← BitVec.ofNat_mul, ← BitVec.ofNat_add]
    apply congrArg (BitVec.ofNat 128)
    exact (upper_reorder4 _ _ _ _).trans (upperSums_one _).symm
  have h1 : (wq 1).toNat = q 1 :=
    BitVec.toNat_eq_nat.mpr ⟨(hq 1).1.trans (by decide), r1⟩
  have c1 := ushift52_repr (wq 1) (q 1) h1
  have r2 : wq 2 = BitVec.ofNat 128 (q 2) := by
    change ((digitWord (w 3)).setWidth 128 <<< (44 : Nat)) + z 7 + (wq 1 >>> (52 : Nat)) = _
    conv_lhs =>
      rw [hd 3, c1, word_repr (z 7)]
      rw [ofNat_shift44 _ ((adjustmentDigit_bound (t 3)).trans (by decide))]
      simp only [← BitVec.ofNat_mul, ← BitVec.ofNat_add]
    apply congrArg (BitVec.ofNat 128)
    exact (upper_reorder3 _ _ _).trans (upperSums_two _).symm
  have h2 : (wq 2).toNat = q 2 :=
    BitVec.toNat_eq_nat.mpr ⟨(hq 2).1.trans (by decide), r2⟩
  have c2 := ushift52_repr (wq 2) (q 2) h2
  have r3 : wq 3 = BitVec.ofNat 128 (q 3) := by
    change ((digitWord (w 4)).setWidth 128 <<< (44 : Nat)) + z 8 + (wq 2 >>> (52 : Nat)) = _
    conv_lhs =>
      rw [hd 4, c2, word_repr (z 8)]
      rw [ofNat_shift44 _ ((adjustmentDigit_bound (t 4)).trans (by decide))]
      simp only [← BitVec.ofNat_mul, ← BitVec.ofNat_add]
    apply congrArg (BitVec.ofNat 128)
    exact (upper_reorder3 _ _ _).trans (upperSums_three _).symm
  have h3 : (wq 3).toNat = q 3 :=
    BitVec.toNat_eq_nat.mpr ⟨(hq 3).1.trans (by decide), r3⟩
  intro i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3

private def repackWords (q : Fin 4 → BitVec 128) (i : Fin 5) : BitVec 64 :=
  match i.val with
  | 0 => (q 0).setWidth 64 &&& 4503599627370495#64
  | 1 => (q 1).setWidth 64 &&& 4503599627370495#64
  | 2 => (q 2).setWidth 64 &&& 4503599627370495#64
  | 3 => (q 3).setWidth 64 &&& 4503599627370495#64
  | _ => ((q 3) >>> (52 : Nat)).setWidth 64

private theorem repackWords_toNat (q : Fin 4 → BitVec 128) (n : Fin 4 → Nat)
    (hq : ∀ i, (q i).toNat = n i) (htop : repackUpper n 4 < 2 ^ 64) (i : Fin 5) :
    (repackWords q i).toNat = repackUpper n i := by
  fin_cases i
  · exact (trunc128_mask52 (q 0)).trans (congrArg (· % 2 ^ 52) (hq 0))
  · exact (trunc128_mask52 (q 1)).trans (congrArg (· % 2 ^ 52) (hq 1))
  · exact (trunc128_mask52 (q 2)).trans (congrArg (· % 2 ^ 52) (hq 2))
  · exact (trunc128_mask52 (q 3)).trans (congrArg (· % 2 ^ 52) (hq 3))
  · exact (final_carry_trunc (q 3) (by rw [hq 3]; exact htop)).trans
      (congrArg (· / 2 ^ 52) (hq 3))

private theorem wordQuotientLimbs_repack (z : Fin 9 → BitVec 128) (i : Fin 5) :
    wordQuotientLimbs z i = repackWords (wordUpperSums z) i := rfl

/-- The actual five quotient words agree with the natural quotient limbs. -/
theorem wordQuotientLimbs_toNat (z : Fin 9 → BitVec 128)
    (hz : ∀ i, (z i).toNat < 2 ^ 107)
    (htop : quotientLimbs (fun j => (z j).toNat) 4 < 2 ^ 64) (i : Fin 5) :
    (wordQuotientLimbs z i).toNat = quotientLimbs (fun j => (z j).toNat) i := by
  exact (congrArg BitVec.toNat (wordQuotientLimbs_repack z i)).trans
    (repackWords_toNat (wordUpperSums z) (upperSums (fun j => (z j).toNat))
      (wordUpperSums_toNat z hz) htop i)

end Agave.Ed25519.Verifier.Execution.ScalarMontgomeryMul
