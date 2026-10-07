import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.WordSchedule

/-! Refine each of the five actual cancellation inputs separately. The proof
uses bounded natural carries and algebraic `ofNat` addition/multiplication. -/
namespace Agave.Ed25519.Verifier.Execution.ScalarMontgomeryMul

open Agave.Ed25519.ScalarReduce32.Arithmetic
set_option exponentiation.threshold 512
set_option maxRecDepth 100000

private theorem cancellation_eq_one (z : Fin 9 → Nat) :
    cancellationSums z 1 = adjustmentCarry (cancellationSums z 0) + z 1 +
      adjustmentDigit (cancellationSums z 0) * 3916664325105025 := rfl

private theorem cancellation_eq_two (z : Fin 9 → Nat) :
    cancellationSums z 2 = adjustmentCarry (cancellationSums z 1) + z 2 +
      adjustmentDigit (cancellationSums z 0) * 1367801 +
      adjustmentDigit (cancellationSums z 1) * 3916664325105025 := rfl

private theorem cancellation_eq_three (z : Fin 9 → Nat) :
    cancellationSums z 3 = adjustmentCarry (cancellationSums z 2) + z 3 +
      adjustmentDigit (cancellationSums z 1) * 1367801 +
      adjustmentDigit (cancellationSums z 2) * 3916664325105025 := rfl

private theorem cancellation_eq_four (z : Fin 9 → Nat) :
    cancellationSums z 4 = adjustmentCarry (cancellationSums z 3) + z 4 +
      adjustmentDigit (cancellationSums z 0) * 17592186044416 +
      adjustmentDigit (cancellationSums z 2) * 1367801 +
      adjustmentDigit (cancellationSums z 3) * 3916664325105025 := rfl

private theorem cancellation_reorder3 (c z p : Nat) : p + z + c = c + z + p := by omega
private theorem cancellation_reorder4 (c z p q : Nat) : z + p + q + c = c + z + p + q := by omega
private theorem cancellation_reorder4' (c z p q : Nat) : p + z + q + c = c + z + p + q := by omega
private theorem cancellation_reorder5 (c z p q r : Nat) : z + p + q + r + c = c + z + p + q + r := by omega

/-- All five source-ordered word cancellation sums equal the natural schedule. -/
theorem wordCancellationSums_toNat (z : Fin 9 → BitVec 128)
    (hz : ∀ i, (z i).toNat < 2 ^ 107) :
    ∀ i, (wordCancellationSums z i).toNat =
      cancellationSums (fun j => (z j).toNat) i := by
  let w := wordCancellationSums z
  let t := cancellationSums (fun j => (z j).toNat)
  have ht := cancellationSums_bounds (fun j => (z j).toNat) hz
  have h0 : (w 0).toNat = t 0 := rfl
  have d0 := digitWord_repr (w 0) (t 0) h0
  have c0 := sourceCarryWord_repr (w 0) (t 0) h0 (ht 0).1
  have r1 : w 1 = BitVec.ofNat 128 (t 1) := by
    change (digitWord (w 0)).setWidth 128 * 3916664325105025#128 + z 1 + sourceCarryWord (w 0) = _
    conv_lhs =>
      rw [d0, c0, word_repr (z 1)]
      simp only [← BitVec.ofNat_mul, ← BitVec.ofNat_add]
    apply congrArg (BitVec.ofNat 128)
    exact (cancellation_reorder3 _ _ _).trans (cancellation_eq_one _).symm
  have h1 : (w 1).toNat = t 1 :=
    BitVec.toNat_eq_nat.mpr ⟨(ht 1).1.trans (by decide), r1⟩
  have d1 := digitWord_repr (w 1) (t 1) h1
  have c1 := sourceCarryWord_repr (w 1) (t 1) h1 (ht 1).1
  have r2 : w 2 = BitVec.ofNat 128 (t 2) := by
    change z 2 + (digitWord (w 0)).setWidth 128 * 1367801#128 +
      (digitWord (w 1)).setWidth 128 * 3916664325105025#128 + sourceCarryWord (w 1) = _
    conv_lhs =>
      rw [d0, d1, c1, word_repr (z 2)]
      simp only [← BitVec.ofNat_mul, ← BitVec.ofNat_add]
    apply congrArg (BitVec.ofNat 128)
    exact (cancellation_reorder4 _ _ _ _).trans (cancellation_eq_two _).symm
  have h2 : (w 2).toNat = t 2 :=
    BitVec.toNat_eq_nat.mpr ⟨(ht 2).1.trans (by decide), r2⟩
  have d2 := digitWord_repr (w 2) (t 2) h2
  have c2 := sourceCarryWord_repr (w 2) (t 2) h2 (ht 2).1
  have r3 : w 3 = BitVec.ofNat 128 (t 3) := by
    change (digitWord (w 1)).setWidth 128 * 1367801#128 + z 3 +
      (digitWord (w 2)).setWidth 128 * 3916664325105025#128 + sourceCarryWord (w 2) = _
    conv_lhs =>
      rw [d1, d2, c2, word_repr (z 3)]
      simp only [← BitVec.ofNat_mul, ← BitVec.ofNat_add]
    apply congrArg (BitVec.ofNat 128)
    exact (cancellation_reorder4' _ _ _ _).trans (cancellation_eq_three _).symm
  have h3 : (w 3).toNat = t 3 :=
    BitVec.toNat_eq_nat.mpr ⟨(ht 3).1.trans (by decide), r3⟩
  have d3 := digitWord_repr (w 3) (t 3) h3
  have c3 := sourceCarryWord_repr (w 3) (t 3) h3 (ht 3).1
  have r4 : w 4 = BitVec.ofNat 128 (t 4) := by
    change z 4 + ((digitWord (w 0)).setWidth 128 <<< (44 : Nat)) +
      (digitWord (w 2)).setWidth 128 * 1367801#128 +
      (digitWord (w 3)).setWidth 128 * 3916664325105025#128 + sourceCarryWord (w 3) = _
    conv_lhs =>
      rw [d0, d2, d3, c3, word_repr (z 4)]
      rw [ofNat_shift44 _ ((adjustmentDigit_bound (t 0)).trans (by decide))]
      simp only [← BitVec.ofNat_mul, ← BitVec.ofNat_add]
    apply congrArg (BitVec.ofNat 128)
    exact (cancellation_reorder5 _ _ _ _ _).trans (cancellation_eq_four _).symm
  have h4 : (w 4).toNat = t 4 :=
    BitVec.toNat_eq_nat.mpr ⟨(ht 4).1.trans (by decide), r4⟩
  intro i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

/-- Uniform bridge for all five actual digit words. -/
theorem wordCancellationDigits_repr (z : Fin 9 → BitVec 128)
    (hz : ∀ i, (z i).toNat < 2 ^ 107) (i : Fin 5) :
    (digitWord (wordCancellationSums z i)).setWidth 128 =
      BitVec.ofNat 128 (adjustmentDigit (cancellationSums (fun j => (z j).toNat) i)) :=
  digitWord_repr _ _ (wordCancellationSums_toNat z hz i)

/-- Uniform bridge for all five actual carry words. -/
theorem wordCancellationCarry_repr (z : Fin 9 → BitVec 128)
    (hz : ∀ i, (z i).toNat < 2 ^ 107) (i : Fin 5) :
    sourceCarryWord (wordCancellationSums z i) =
      BitVec.ofNat 128 (adjustmentCarry (cancellationSums (fun j => (z j).toNat) i)) :=
  sourceCarryWord_repr _ _ (wordCancellationSums_toNat z hz i)
    (cancellationSums_bounds _ hz i).1

end Agave.Ed25519.Verifier.Execution.ScalarMontgomeryMul
