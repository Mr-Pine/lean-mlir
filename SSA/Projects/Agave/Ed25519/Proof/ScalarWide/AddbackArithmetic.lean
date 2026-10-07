import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.BorrowChain

/-! The complete addback carry chain as natural arithmetic. Each local sum is
small enough for the source's flagged u64 additions; top-word wrapping is
handled separately by the low-52-bit word lemma. -/
namespace Agave.Ed25519.Verifier.Execution.ScalarWide.Subtraction

open Agave.Ed25519.Bridge
open Agave.Ed25519.ScalarReduce32.Arithmetic (limbs radix)
set_option exponentiation.threshold 512

/-- The five source addback sums, before each low-52-bit mask. -/
def addbackSums (digits : Fin 5 → Nat) (borrow : Nat) (i : Fin 5) : Nat :=
  match i.val with
  | 0 => digits 0 + borrow * 671914833335277
  | 1 =>
      let t0 := digits 0 + borrow * 671914833335277
      t0 / 2 ^ 52 + borrow * 3916664325105025 + digits 1
  | 2 =>
      let t0 := digits 0 + borrow * 671914833335277
      let t1 := t0 / 2 ^ 52 + borrow * 3916664325105025 + digits 1
      digits 2 + borrow * 1367801 + t1 / 2 ^ 52
  | 3 =>
      let t0 := digits 0 + borrow * 671914833335277
      let t1 := t0 / 2 ^ 52 + borrow * 3916664325105025 + digits 1
      let t2 := digits 2 + borrow * 1367801 + t1 / 2 ^ 52
      t2 / 2 ^ 52 + digits 3
  | _ =>
      let t0 := digits 0 + borrow * 671914833335277
      let t1 := t0 / 2 ^ 52 + borrow * 3916664325105025 + digits 1
      let t2 := digits 2 + borrow * 1367801 + t1 / 2 ^ 52
      let t3 := t2 / 2 ^ 52 + digits 3
      digits 4 + borrow * 17592186044416 + t3 / 2 ^ 52

private theorem addbackSums_zero (digits : Fin 5 → Nat) (borrow : Nat) :
    addbackSums digits borrow 0 = digits 0 + borrow * 671914833335277 := rfl

private theorem addbackSums_one (digits : Fin 5 → Nat) (borrow : Nat) :
    addbackSums digits borrow 1 = addbackSums digits borrow 0 / 2 ^ 52 +
      borrow * 3916664325105025 + digits 1 := rfl

private theorem addbackSums_two (digits : Fin 5 → Nat) (borrow : Nat) :
    addbackSums digits borrow 2 = digits 2 + borrow * 1367801 +
      addbackSums digits borrow 1 / 2 ^ 52 := rfl

private theorem addbackSums_three (digits : Fin 5 → Nat) (borrow : Nat) :
    addbackSums digits borrow 3 = addbackSums digits borrow 2 / 2 ^ 52 +
      digits 3 := rfl

private theorem addbackSums_four (digits : Fin 5 → Nat) (borrow : Nat) :
    addbackSums digits borrow 4 = digits 4 + borrow * 17592186044416 +
      addbackSums digits borrow 3 / 2 ^ 52 := rfl

/-- A local normalized digit and subgroup-order digit generate at most one
carry, and fit both the signed and unsigned u64 addition ranges. -/
theorem addback_sum_bound (digit constant carry borrow : Nat)
    (hd : digit < 2 ^ 52) (hk : constant < 2 ^ 52)
    (hc : carry ≤ 1) (hb : borrow ≤ 1) :
    digit + borrow * constant + carry < 2 ^ 53 ∧
      (digit + borrow * constant + carry) / 2 ^ 52 ≤ 1 := by
  have hm : borrow * constant ≤ constant := by
    simpa using Nat.mul_le_mul_right constant hb
  norm_num at hd hk ⊢
  omega

/- Explicit transport prevents the kernel from unfolding a large constant
multiplication while eliminating a zero carry or comparing source sum forms. -/
private theorem addbackSums_bound0 (digits : Fin 5 → Nat) (borrow : Nat)
    (hd : ∀ i, digits i < 2 ^ 52) (hb : borrow ≤ 1) :
    addbackSums digits borrow 0 < 2 ^ 53 ∧
      addbackSums digits borrow 0 / 2 ^ 52 ≤ 1 := by
  have h0 := addback_sum_bound (digits 0) 671914833335277 0 borrow
    (hd 0) (by decide) (by decide) hb
  have hs : digits 0 + borrow * 671914833335277 + 0 = addbackSums digits borrow 0 :=
    (Nat.add_zero _).trans (addbackSums_zero digits borrow).symm
  exact Eq.mp (congrArg (fun n => n < 2 ^ 53 ∧ n / 2 ^ 52 ≤ 1) hs) h0

private theorem addbackSums_bound1 (digits : Fin 5 → Nat) (borrow : Nat)
    (hd : ∀ i, digits i < 2 ^ 52) (hb : borrow ≤ 1) :
    addbackSums digits borrow 1 < 2 ^ 53 ∧
      addbackSums digits borrow 1 / 2 ^ 52 ≤ 1 := by
  have h1 := addback_sum_bound (digits 1) 3916664325105025
    (addbackSums digits borrow 0 / 2 ^ 52) borrow
    (hd 1) (by decide) (addbackSums_bound0 digits borrow hd hb).2 hb
  have hs : digits 1 + borrow * 3916664325105025 +
      addbackSums digits borrow 0 / 2 ^ 52 = addbackSums digits borrow 1 := by
    calc
      _ = addbackSums digits borrow 0 / 2 ^ 52 +
          borrow * 3916664325105025 + digits 1 := by omega
      _ = _ := (addbackSums_one digits borrow).symm
  exact Eq.mp (congrArg (fun n => n < 2 ^ 53 ∧ n / 2 ^ 52 ≤ 1) hs) h1

private theorem addbackSums_bound2 (digits : Fin 5 → Nat) (borrow : Nat)
    (hd : ∀ i, digits i < 2 ^ 52) (hb : borrow ≤ 1) :
    addbackSums digits borrow 2 < 2 ^ 53 ∧
      addbackSums digits borrow 2 / 2 ^ 52 ≤ 1 := by
  have h2 := addback_sum_bound (digits 2) 1367801
    (addbackSums digits borrow 1 / 2 ^ 52) borrow
    (hd 2) (by decide) (addbackSums_bound1 digits borrow hd hb).2 hb
  exact Eq.mpr (congrArg (fun n => n < 2 ^ 53 ∧ n / 2 ^ 52 ≤ 1)
    (addbackSums_two digits borrow)) h2

private theorem addbackSums_bound3 (digits : Fin 5 → Nat) (borrow : Nat)
    (hd : ∀ i, digits i < 2 ^ 52) (hb : borrow ≤ 1) :
    addbackSums digits borrow 3 < 2 ^ 53 ∧
      addbackSums digits borrow 3 / 2 ^ 52 ≤ 1 := by
  have h3 := addback_sum_bound (digits 3) 0 (addbackSums digits borrow 2 / 2 ^ 52) borrow
    (hd 3) (by decide) (addbackSums_bound2 digits borrow hd hb).2 hb
  have hs : digits 3 + borrow * 0 + addbackSums digits borrow 2 / 2 ^ 52 =
      addbackSums digits borrow 3 := by
    calc
      _ = addbackSums digits borrow 2 / 2 ^ 52 + digits 3 := by omega
      _ = _ := (addbackSums_three digits borrow).symm
  exact Eq.mp (congrArg (fun n => n < 2 ^ 53 ∧ n / 2 ^ 52 ≤ 1) hs) h3

private theorem addbackSums_bound4 (digits : Fin 5 → Nat) (borrow : Nat)
    (hd : ∀ i, digits i < 2 ^ 52) (hb : borrow ≤ 1) :
    addbackSums digits borrow 4 < 2 ^ 53 ∧
      addbackSums digits borrow 4 / 2 ^ 52 ≤ 1 := by
  have h4 := addback_sum_bound (digits 4) 17592186044416
    (addbackSums digits borrow 3 / 2 ^ 52) borrow
    (hd 4) (by decide) (addbackSums_bound3 digits borrow hd hb).2 hb
  exact Eq.mpr (congrArg (fun n => n < 2 ^ 53 ∧ n / 2 ^ 52 ≤ 1)
    (addbackSums_four digits borrow)) h4

/-- Bounds for every actual natural addback sum and outgoing carry. -/
theorem addbackSums_bounds (digits : Fin 5 → Nat) (borrow : Nat)
    (hd : ∀ i, digits i < 2 ^ 52) (hb : borrow ≤ 1) :
    ∀ i, addbackSums digits borrow i < 2 ^ 53 ∧
      addbackSums digits borrow i / 2 ^ 52 ≤ 1 := by
  intro i
  fin_cases i
  · exact addbackSums_bound0 digits borrow hd hb
  · exact addbackSums_bound1 digits borrow hd hb
  · exact addbackSums_bound2 digits borrow hd hb
  · exact addbackSums_bound3 digits borrow hd hb
  · exact addbackSums_bound4 digits borrow hd hb

/-- The carries telescope before discarding the final radix-260 carry. -/
theorem addbackSums_telescope (digits : Fin 5 → Nat) (borrow : Nat) :
    let t := addbackSums digits borrow
    limbs (t 0 % 2 ^ 52) (t 1 % 2 ^ 52) (t 2 % 2 ^ 52)
        (t 3 % 2 ^ 52) (t 4 % 2 ^ 52) + 2 ^ 260 * (t 4 / 2 ^ 52) =
      limbs (digits 0) (digits 1) (digits 2) (digits 3) (digits 4) +
        borrow * subgroupOrder := by
  have h0 := Nat.mod_add_div (addbackSums digits borrow 0) (2 ^ 52)
  have h1 := Nat.mod_add_div (addbackSums digits borrow 1) (2 ^ 52)
  have h2 := Nat.mod_add_div (addbackSums digits borrow 2) (2 ^ 52)
  have h3 := Nat.mod_add_div (addbackSums digits borrow 3) (2 ^ 52)
  have h4 := Nat.mod_add_div (addbackSums digits borrow 4) (2 ^ 52)
  dsimp only
  norm_num [addbackSums, limbs, radix, subgroupOrder] at h0 h1 h2 h3 h4 ⊢
  omega

/-- The normalized addback digits are exactly the full sum modulo 2^260. -/
theorem addbackSums_mod (digits : Fin 5 → Nat) (borrow : Nat) :
    let t := addbackSums digits borrow
    limbs (t 0 % 2 ^ 52) (t 1 % 2 ^ 52) (t 2 % 2 ^ 52)
        (t 3 % 2 ^ 52) (t 4 % 2 ^ 52) =
      (limbs (digits 0) (digits 1) (digits 2) (digits 3) (digits 4) +
        borrow * subgroupOrder) % 2 ^ 260 := by
  dsimp only
  rw [← addbackSums_telescope digits borrow, Nat.add_mul_mod_self_left]
  apply (Nat.mod_eq_of_lt _).symm
  exact Agave.Ed25519.ScalarReduce32.Arithmetic.adjustment_bound _ _ _ _ _
    (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide))
    (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide))

/-- Complete natural subtraction/addback equality, with no modular ambiguity. -/
theorem borrow_addback_exact (x : Fin 5 → BitVec 52) :
    let t := addbackSums (fun i => (borrowSteps x i).1) (borrowSteps x 4).2
    limbs (t 0 % 2 ^ 52) (t 1 % 2 ^ 52) (t 2 % 2 ^ 52)
        (t 3 % 2 ^ 52) (t 4 % 2 ^ 52) =
      if rawValue x < subgroupOrder then rawValue x else rawValue x - subgroupOrder := by
  dsimp only
  rw [addbackSums_mod]
  have hb := (borrowSteps_certificate x).1 4
  have he : (borrowSteps x 4).2 * subgroupOrder =
      if (borrowSteps x 4).2 = 1 then subgroupOrder else 0 := by
    have h : (borrowSteps x 4).2 = 0 ∨ (borrowSteps x 4).2 = 1 := by omega
    rcases h with h | h <;> simp [h]
  rw [he]
  exact borrowSteps_addback x

end Agave.Ed25519.Verifier.Execution.ScalarWide.Subtraction
