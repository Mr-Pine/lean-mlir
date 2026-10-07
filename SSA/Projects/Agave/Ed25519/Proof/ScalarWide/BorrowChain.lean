import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.BorrowWord
import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.MontgomerySchedule

/-! The five actual borrow words, related one step at a time to normalized
radix-52 digits. No full-execution or packed-word correctness premise is used. -/
namespace Agave.Ed25519.Verifier.Execution.ScalarWide.Subtraction

open Agave.Ed25519.Bridge
open Agave.Ed25519.ScalarReduce32.Arithmetic (limbs radix)
set_option exponentiation.threshold 512
set_option maxRecDepth 100000

/-- Difference digit and outgoing borrow after each source subtraction. -/
def borrowSteps (x : Fin 5 → BitVec 52) (i : Fin 5) : Nat × Nat :=
  match i.val with
  | 0 => subtractDigit (x 0).toNat 671914833335277 0
  | 1 =>
      let s0 := subtractDigit (x 0).toNat 671914833335277 0
      subtractDigit (x 1).toNat 3916664325105025 s0.2
  | 2 =>
      let s0 := subtractDigit (x 0).toNat 671914833335277 0
      let s1 := subtractDigit (x 1).toNat 3916664325105025 s0.2
      subtractDigit (x 2).toNat 1367801 s1.2
  | 3 =>
      let s0 := subtractDigit (x 0).toNat 671914833335277 0
      let s1 := subtractDigit (x 1).toNat 3916664325105025 s0.2
      let s2 := subtractDigit (x 2).toNat 1367801 s1.2
      subtractDigit (x 3).toNat 0 s2.2
  | _ =>
      let s0 := subtractDigit (x 0).toNat 671914833335277 0
      let s1 := subtractDigit (x 1).toNat 3916664325105025 s0.2
      let s2 := subtractDigit (x 2).toNat 1367801 s1.2
      let s3 := subtractDigit (x 3).toNat 0 s2.2
      subtractDigit (x 4).toNat 17592186044416 s3.2

def rawValue (x : Fin 5 → BitVec 52) : Nat :=
  limbs (x 0).toNat (x 1).toNat (x 2).toNat (x 3).toNat (x 4).toNat

def differenceValue (x : Fin 5 → BitVec 52) : Nat :=
  limbs (borrowSteps x 0).1 (borrowSteps x 1).1 (borrowSteps x 2).1
    (borrowSteps x 3).1 (borrowSteps x 4).1

/-- Five subtraction equations telescope, including the outgoing top borrow. -/
theorem borrowSteps_certificate (x : Fin 5 → BitVec 52) :
    (∀ i, (borrowSteps x i).1 < 2 ^ 52 ∧ (borrowSteps x i).2 ≤ 1) ∧
      rawValue x + 2 ^ 260 * (borrowSteps x 4).2 = subgroupOrder + differenceValue x := by
  have h0 := subtractDigit_equation (x 0).toNat 671914833335277 0
    (x 0).isLt (by decide) (by decide)
  have h1 := subtractDigit_equation (x 1).toNat 3916664325105025 _
    (x 1).isLt (by decide) h0.2.2
  have h2 := subtractDigit_equation (x 2).toNat 1367801 _
    (x 2).isLt (by decide) h1.2.2
  have h3 := subtractDigit_equation (x 3).toNat 0 _
    (x 3).isLt (by decide) h2.2.2
  have h4 := subtractDigit_equation (x 4).toNat 17592186044416 _
    (x 4).isLt (by decide) h3.2.2
  constructor
  · intro i
    fin_cases i
    · exact h0.2
    · exact h1.2
    · exact h2.2
    · exact h3.2
    · exact h4.2
  · simp only [rawValue, differenceValue, borrowSteps, Matrix.cons_val_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ, Matrix.cons_val_succ',
      Matrix.cons_val_fin_one]
    norm_num [limbs, radix, subgroupOrder] at h0 h1 h2 h3 h4 ⊢
    omega

/-- A previous sign mask implements subtraction of exactly its borrow bit. -/
theorem add_borrow_mask (a : BitVec 64) (b incoming : Nat) (hin : incoming ≤ 1) :
    (if incoming = 1 then (-1 : BitVec 64) else 0) +
        (-BitVec.ofNat 64 b) + a = a - BitVec.ofNat 64 (b + incoming) := by
  have hh : incoming = 0 ∨ incoming = 1 := by omega
  rcases hh with rfl | rfl
  · simp [BitVec.sub_eq_add_neg, BitVec.add_comm]
  · simp only [if_pos rfl, BitVec.ofNat_add, BitVec.neg_add, BitVec.sub_eq_add_neg]
    ac_rfl

/-- Bridge a source arithmetic-shift/subtract/add sequence to one natural digit. -/
theorem next_borrow_word (a previous : BitVec 64) (b incoming : Nat)
    (ha : a.toNat < 2 ^ 52) (hb : b < 2 ^ 52) (hin : incoming ≤ 1)
    (hprev : previous.sshiftRight 63 = if incoming = 1 then -1 else 0) :
    let word := previous.sshiftRight 63 + (-BitVec.ofNat 64 b) + a
    (word &&& 4503599627370495#64).toNat = (subtractDigit a.toNat b incoming).1 ∧
      word.sshiftRight 63 = if (subtractDigit a.toNat b incoming).2 = 1 then -1 else 0 := by
  dsimp only
  rw [hprev, add_borrow_mask a b incoming hin]
  exact limb_sub_digit a b incoming ha hb hin

/-- Exact interpretation of every mask and sign shift in the five-word source
borrow chain. The separate RIR refinement retains the signed-overflow flags. -/
theorem differences_refine (x : Fin 5 → BitVec 52) :
    let d := differences (x 0) (x 1) (x 2) (x 3) (x 4)
    ∀ i, (d i &&& 4503599627370495#64).toNat = (borrowSteps x i).1 ∧
      (d i).sshiftRight 63 = if (borrowSteps x i).2 = 1 then -1 else 0 := by
  let d := differences (x 0) (x 1) (x 2) (x 3) (x 4)
  have hx (i : Fin 5) : ((x i).setWidth 64).toNat < 2 ^ 52 := by
    simpa only [BitVec.toNat_setWidth_of_le (by decide : 52 ≤ 64)] using (x i).isLt
  have hc := (borrowSteps_certificate x).1
  have h0 := limb_sub_digit ((x 0).setWidth 64) 671914833335277 0
    (hx 0) (by decide) (by decide)
  simp only [Nat.add_zero, BitVec.sub_eq_add_neg,
    BitVec.toNat_setWidth_of_le (by decide : 52 ≤ 64)] at h0
  have h1 := next_borrow_word ((x 1).setWidth 64)
    (d 0)
    3916664325105025 (borrowSteps x 0).2 (hx 1) (by decide) (hc 0).2 h0.2
  simp only [BitVec.toNat_setWidth_of_le (by decide : 52 ≤ 64)] at h1
  have h2 := next_borrow_word ((x 2).setWidth 64)
    (d 1)
    1367801 (borrowSteps x 1).2 (hx 2) (by decide) (hc 1).2 h1.2
  simp only [BitVec.toNat_setWidth_of_le (by decide : 52 ≤ 64)] at h2
  have h3 := next_borrow_word ((x 3).setWidth 64)
    (d 2)
    0 (borrowSteps x 2).2 (hx 3) (by decide) (hc 2).2 h2.2
  simp only [BitVec.toNat_setWidth_of_le (by decide : 52 ≤ 64)] at h3
  have hd3 : d 3 = (d 2).sshiftRight 63 + (-BitVec.ofNat 64 0) +
      (x 3).setWidth 64 := by
    have he : d 3 = (x 3).setWidth 64 + (d 2).sshiftRight 63 := rfl
    rw [he]
    simp only [BitVec.neg_zero, BitVec.add_zero]
    exact BitVec.add_comm _ _
  have hd4 : d 4 = (d 3).sshiftRight 63 +
      (-BitVec.ofNat 64 17592186044416) + (x 4).setWidth 64 := by
    have he : d 4 = (x 4).setWidth 64 +
        (-17592186044416 : BitVec 64) + (d 3).sshiftRight 63 := rfl
    rw [he]
    ac_rfl
  have hs3 : (d 3).sshiftRight 63 =
      if (borrowSteps x 3).2 = 1 then -1 else 0 := by
    rw [hd3]
    exact h3.2
  have h4 := next_borrow_word ((x 4).setWidth 64)
    (d 3) 17592186044416 (borrowSteps x 3).2 (hx 4) (by decide) (hc 3).2 hs3
  simp only [BitVec.toNat_setWidth_of_le (by decide : 52 ≤ 64)] at h4
  change ∀ i, (d i &&& 4503599627370495#64).toNat = (borrowSteps x i).1 ∧
    (d i).sshiftRight 63 = if (borrowSteps x i).2 = 1 then -1 else 0
  intro i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · change (d 3 &&& 4503599627370495#64).toNat = (borrowSteps x 3).1 ∧
      (d 3).sshiftRight 63 = if (borrowSteps x 3).2 = 1 then -1 else 0
    rw [hd3]
    exact h3
  · change (d 4 &&& 4503599627370495#64).toNat = (borrowSteps x 4).1 ∧
      (d 4).sshiftRight 63 = if (borrowSteps x 4).2 = 1 then -1 else 0
    rw [hd4]
    exact h4

/-- The mathematical packed output of the complete borrow/addback procedure. -/
theorem borrowSteps_addback (x : Fin 5 → BitVec 52) :
    (differenceValue x + if (borrowSteps x 4).2 = 1 then subgroupOrder else 0) % 2 ^ 260 =
      if rawValue x < subgroupOrder then rawValue x else rawValue x - subgroupOrder := by
  have hc := borrowSteps_certificate x
  have hraw : rawValue x < 2 ^ 260 := by
    exact Agave.Ed25519.ScalarReduce32.Arithmetic.adjustment_bound _ _ _ _ _
      (x 0).isLt (x 1).isLt (x 2).isLt (x 3).isLt (x 4).isLt
  have hdiff : differenceValue x < 2 ^ 260 := by
    exact Agave.Ed25519.ScalarReduce32.Arithmetic.adjustment_bound _ _ _ _ _
      (hc.1 0).1 (hc.1 1).1 (hc.1 2).1 (hc.1 3).1 (hc.1 4).1
  have hb : (borrowSteps x 4).2 = 0 ∨ (borrowSteps x 4).2 = 1 := by
    have := (hc.1 4).2
    omega
  rcases hb with hb | hb
  · simpa only [hb, Bool.false_eq_true, Nat.zero_ne_one, ↓reduceIte, Nat.mul_zero] using
      conditional_addback_identity (rawValue x) (differenceValue x) false hraw hdiff
        (by simpa only [hb, Nat.mul_zero, Bool.false_eq_true, Nat.zero_ne_one,
          ↓reduceIte] using hc.2)
  · simpa only [hb, ↓reduceIte, Nat.mul_one] using
      conditional_addback_identity (rawValue x) (differenceValue x) true hraw hdiff
        (by simpa only [hb, Nat.mul_one, ↓reduceIte] using hc.2)

end Agave.Ed25519.Verifier.Execution.ScalarWide.Subtraction
