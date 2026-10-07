import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.WrapperSumArithmetic

/-! Remove u64 wrapping from the wrapper addition under normalized input limbs. -/
namespace Agave.Ed25519.Verifier.Execution.ScalarWide
open ScalarMontgomeryMul (mask52_toNat)
set_option exponentiation.threshold 512

private theorem sumWord_repr (word : BitVec width) : word = BitVec.ofNat width word.toNat :=
  (BitVec.toNat_eq_nat.mp rfl).2

def sumWordSums (a b : Fin 5 → BitVec 64) : Fin 5 → BitVec 64 :=
  let t0 := a 0 + b 0
  let t1 := (t0 >>> 52) + b 1 + a 1
  let t2 := a 2 + b 2 + (t1 >>> 52)
  let t3 := a 3 + b 3 + (t2 >>> 52)
  let t4 := a 4 + b 4 + (t3 >>> 52)
  ![t0, t1, t2, t3, t4]

theorem sumWordSums_toNat (a b : Fin 5 → BitVec 64)
    (ha : ∀ i, (a i).toNat < 2 ^ 52) (hb : ∀ i, (b i).toNat < 2 ^ 52) :
    ∀ i, (sumWordSums a b i).toNat = sumSums (fun j => (a j).toNat) (fun j => (b j).toNat) i := by
  let w := sumWordSums a b
  let t := sumSums (fun j => (a j).toNat) (fun j => (b j).toNat)
  have ht := sumSums_bounds (fun j => (a j).toNat) (fun j => (b j).toNat) ha hb
  have r0 : w 0 = BitVec.ofNat 64 (t 0) := by
    change a 0 + b 0 = _
    rw [sumWord_repr (a 0), sumWord_repr (b 0)]
    simp only [← BitVec.ofNat_add]
    rfl
  have h0 : (w 0).toNat = t 0 :=
    BitVec.toNat_eq_nat.mpr ⟨(ht 0).1.trans (by decide), r0⟩
  have c0 : w 0 >>> 52 = BitVec.ofNat 64 (t 0 / 2 ^ 52) := by
    have he : (w 0 >>> 52).toNat = t 0 / 2 ^ 52 := by
      change (w 0).toNat >>> (52 : Nat) = t 0 / 2 ^ 52
      rw [h0, Nat.shiftRight_eq_div_pow]
    exact (BitVec.toNat_eq_nat.mp he).2
  have r1 : w 1 = BitVec.ofNat 64 (t 1) := by
    change (w 0 >>> 52) + b 1 + a 1 = _
    rw [sumWord_repr (a 1), sumWord_repr (b 1), c0]
    simp only [← BitVec.ofNat_add]
    rfl
  have h1 : (w 1).toNat = t 1 :=
    BitVec.toNat_eq_nat.mpr ⟨(ht 1).1.trans (by decide), r1⟩
  have c1 : w 1 >>> 52 = BitVec.ofNat 64 (t 1 / 2 ^ 52) := by
    have he : (w 1 >>> 52).toNat = t 1 / 2 ^ 52 := by
      change (w 1).toNat >>> (52 : Nat) = t 1 / 2 ^ 52
      rw [h1, Nat.shiftRight_eq_div_pow]
    exact (BitVec.toNat_eq_nat.mp he).2
  have r2 : w 2 = BitVec.ofNat 64 (t 2) := by
    change a 2 + b 2 + (w 1 >>> 52) = _
    rw [sumWord_repr (a 2), sumWord_repr (b 2), c1]
    simp only [← BitVec.ofNat_add]
    rfl
  have h2 : (w 2).toNat = t 2 :=
    BitVec.toNat_eq_nat.mpr ⟨(ht 2).1.trans (by decide), r2⟩
  have c2 : w 2 >>> 52 = BitVec.ofNat 64 (t 2 / 2 ^ 52) := by
    have he : (w 2 >>> 52).toNat = t 2 / 2 ^ 52 := by
      change (w 2).toNat >>> (52 : Nat) = t 2 / 2 ^ 52
      rw [h2, Nat.shiftRight_eq_div_pow]
    exact (BitVec.toNat_eq_nat.mp he).2
  have r3 : w 3 = BitVec.ofNat 64 (t 3) := by
    change a 3 + b 3 + (w 2 >>> 52) = _
    rw [sumWord_repr (a 3), sumWord_repr (b 3), c2]
    simp only [← BitVec.ofNat_add]
    rfl
  have h3 : (w 3).toNat = t 3 :=
    BitVec.toNat_eq_nat.mpr ⟨(ht 3).1.trans (by decide), r3⟩
  have c3 : w 3 >>> 52 = BitVec.ofNat 64 (t 3 / 2 ^ 52) := by
    have he : (w 3 >>> 52).toNat = t 3 / 2 ^ 52 := by
      change (w 3).toNat >>> (52 : Nat) = t 3 / 2 ^ 52
      rw [h3, Nat.shiftRight_eq_div_pow]
    exact (BitVec.toNat_eq_nat.mp he).2
  have r4 : w 4 = BitVec.ofNat 64 (t 4) := by
    change a 4 + b 4 + (w 3 >>> 52) = _
    rw [sumWord_repr (a 4), sumWord_repr (b 4), c3]
    simp only [← BitVec.ofNat_add]
    rfl
  have h4 : (w 4).toNat = t 4 :=
    BitVec.toNat_eq_nat.mpr ⟨(ht 4).1.trans (by decide), r4⟩
  intro i
  fin_cases i <;> assumption

theorem sumWords_toNat (a b : Fin 5 → BitVec 64)
    (ha : ∀ i, (a i).toNat < 2 ^ 52) (hb : ∀ i, (b i).toNat < 2 ^ 52)
    (i : Fin 5) :
    (sumWords a b i).toNat =
      sumSums (fun j => (a j).toNat) (fun j => (b j).toNat) i % 2 ^ 52 := by
  have he : sumWords a b i = sumWordSums a b i &&& 4503599627370495#64 := by
    fin_cases i <;> rfl
  rw [he, mask52_toNat, sumWordSums_toNat a b ha hb]

theorem sumWords_bound (a b : Fin 5 → BitVec 64) (i : Fin 5) :
    (sumWords a b i).toNat < 2 ^ 52 := by
  have he : sumWords a b i = sumWordSums a b i &&& 4503599627370495#64 := by
    fin_cases i <;> rfl
  rw [he, mask52_toNat]
  exact Nat.mod_lt _ (by decide)

theorem sumWords_value (a b : Fin 5 → BitVec 64)
    (ha : ∀ i, (a i).toNat < 2 ^ 52) (hb : ∀ i, (b i).toNat < 2 ^ 52)
    (hsmall : ScalarMontgomeryMul.limbValue (fun i => (a i).toNat) +
      ScalarMontgomeryMul.limbValue (fun i => (b i).toNat) < 2 ^ 260) :
    ScalarMontgomeryMul.limbValue (fun i => (sumWords a b i).toNat) =
      ScalarMontgomeryMul.limbValue (fun i => (a i).toNat) +
      ScalarMontgomeryMul.limbValue (fun i => (b i).toNat) := by
  simp only [ScalarMontgomeryMul.limbValue, sumWords_toNat a b ha hb]
  exact sumSums_value _ _ hsmall

end Agave.Ed25519.Verifier.Execution.ScalarWide
