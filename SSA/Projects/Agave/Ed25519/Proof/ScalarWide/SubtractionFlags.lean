import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.AddbackWords

/-! Nonpoison proofs for the exact signed borrow and unsigned addback flags.
Bounds concern the local mathematical operands, not an assumed RIR result. -/
namespace Agave.Ed25519.Verifier.Execution.ScalarWide.Subtraction

open LeanMLIR.RIR

/-- A signed addition whose integer sum fits i64 retains its exact integer. -/
theorem signed_add64 (a b : BitVec 64)
    (hlo : -(2 ^ 63 : Int) ≤ a.toInt + b.toInt)
    (hhi : a.toInt + b.toInt < (2 ^ 63 : Int)) :
    Operation.add { nsw := true } (.value a) (.value b) = .value (a + b) ∧
      (a + b).toInt = a.toInt + b.toInt := by
  have hs : a.saddOverflow b = false := by
    simp only [BitVec.saddOverflow]
    norm_num at hlo hhi ⊢
    omega
  exact ⟨by simp [Operation.add, hs],
    BitVec.toInt_add_of_not_saddOverflow (by simp [hs])⟩

/-- Positive addback partial sums satisfy both source addition flags. -/
theorem addback_add64 (a b : BitVec 64) (h : a.toNat + b.toNat < 2 ^ 53) :
    Operation.add { nsw := true, nuw := true } (.value a) (.value b) = .value (a + b) ∧
      (a + b).toNat = a.toNat + b.toNat := by
  have hai : a.toInt = (a.toNat : Int) :=
    BitVec.toInt_eq_toNat_of_lt (by norm_num at h ⊢; omega)
  have hbi : b.toInt = (b.toNat : Int) :=
    BitVec.toInt_eq_toNat_of_lt (by norm_num at h ⊢; omega)
  have hs : a.saddOverflow b = false := by
    simp only [BitVec.saddOverflow, hai, hbi]
    norm_num at h ⊢
    omega
  have hu : a.uaddOverflow b = false := by
    simp only [BitVec.uaddOverflow]
    norm_num at h ⊢
    omega
  refine ⟨by simp [Operation.add, hs, hu], ?_⟩
  rw [BitVec.toNat_add]
  exact Nat.mod_eq_of_lt (h.trans (by decide))

/-- A negated normalized order limb has its ordinary negative integer value. -/
theorem negative_limb_toInt (b : Nat) (hb : b < 2 ^ 52) :
    (-BitVec.ofNat 64 b).toInt = -(b : Int) := by
  have hn : (BitVec.ofNat 64 b).toNat = b :=
    Nat.mod_eq_of_lt (hb.trans (by decide))
  have hm : (BitVec.ofNat 64 b).msb = false := by
    apply BitVec.msb_eq_false_iff_two_mul_lt.mpr
    rw [hn]
    norm_num at hb ⊢
    omega
  rw [BitVec.toInt_neg_eq_of_msb hm, BitVec.toInt_eq_toNat_of_msb hm, hn]

/-- A single normalized limb minus an order limb satisfies `add nsw`. -/
theorem limb_minus_constant (a : BitVec 64) (b : Nat)
    (ha : a.toNat < 2 ^ 52) (hb : b < 2 ^ 52) :
    Operation.add { nsw := true } (.value a) (.value (-BitVec.ofNat 64 b)) =
        .value (a + -BitVec.ofNat 64 b) ∧
      (a + -BitVec.ofNat 64 b).toInt = (a.toNat : Int) - b := by
  have hai : a.toInt = (a.toNat : Int) :=
    BitVec.toInt_eq_toNat_of_lt (by norm_num at ha ⊢; omega)
  have hbi := negative_limb_toInt b hb
  have hlo : -(2 ^ 63 : Int) ≤ a.toInt + (-BitVec.ofNat 64 b).toInt := by
    rw [hai, hbi]
    norm_num at ha hb ⊢
    omega
  have hhi : a.toInt + (-BitVec.ofNat 64 b).toInt < (2 ^ 63 : Int) := by
    rw [hai, hbi]
    norm_num at ha hb ⊢
    omega
  simpa only [hai, hbi, sub_eq_add_neg] using signed_add64 a (-BitVec.ofNat 64 b) hlo hhi

/-- Exact integer value of a broadcast borrow mask. -/
theorem borrow_mask_toInt (borrow : Nat) (hb : borrow ≤ 1) :
    (if borrow = 1 then (-1 : BitVec 64) else 0).toInt = -(borrow : Int) := by
  have hh : borrow = 0 ∨ borrow = 1 := by omega
  rcases hh with rfl | rfl <;> decide +kernel

/-- Both signed additions in a middle borrow step are safe. -/
theorem middle_borrow_flags (a : BitVec 64) (b borrow : Nat)
    (ha : a.toNat < 2 ^ 52) (hb : b < 2 ^ 52) (hc : borrow ≤ 1) :
    let mask : BitVec 64 := if borrow = 1 then -1 else 0
    let middle := mask + -BitVec.ofNat 64 b
    Operation.add { nsw := true } (.value mask) (.value (-BitVec.ofNat 64 b)) =
        .value middle ∧
      Operation.add { nsw := true } (.value middle) (.value a) = .value (middle + a) := by
  dsimp only
  have hmask := borrow_mask_toInt borrow hc
  have hconstant := negative_limb_toInt b hb
  have hai : a.toInt = (a.toNat : Int) :=
    BitVec.toInt_eq_toNat_of_lt (by norm_num at ha ⊢; omega)
  have hfirst := signed_add64 (if borrow = 1 then (-1 : BitVec 64) else 0)
    (-BitVec.ofNat 64 b)
    (by rw [hmask, hconstant]; norm_num at hb ⊢; omega)
    (by rw [hmask, hconstant]; norm_num at hb ⊢; omega)
  refine ⟨hfirst.1, ?_⟩
  exact (signed_add64 _ a
    (by rw [hfirst.2, hmask, hconstant, hai]; norm_num at ha hb ⊢; omega)
    (by rw [hfirst.2, hmask, hconstant, hai]; norm_num at ha hb ⊢; omega)).1

/-- Adding only the incoming borrow to a normalized limb is signed-safe. -/
theorem limb_plus_borrow (a : BitVec 64) (borrow : Nat)
    (ha : a.toNat < 2 ^ 52) (hb : borrow ≤ 1) :
    Operation.add { nsw := true } (.value a)
      (.value (if borrow = 1 then -1 else 0)) =
      .value (a + if borrow = 1 then -1 else 0) := by
  have hai : a.toInt = (a.toNat : Int) :=
    BitVec.toInt_eq_toNat_of_lt (by norm_num at ha ⊢; omega)
  have hmask := borrow_mask_toInt borrow hb
  exact (signed_add64 a _
    (by rw [hai, hmask]; norm_num at ha ⊢; omega)
    (by rw [hai, hmask]; norm_num at ha ⊢; omega)).1

/-- A shifted high bit is 0 or 1, so the retained truncation flags are safe. -/
theorem high_bit_trunc_flags (word : BitVec 64) :
    Operation.trunc { nsw := true, nuw := true } (.value (word >>> 63)) =
      .value ((word >>> 63).setWidth 8) := by
  have hw := word.isLt
  have hsmall : (word >>> 63).toNat ≤ 1 := by
    change word.toNat >>> 63 ≤ 1
    rw [Nat.shiftRight_eq_div_pow]
    norm_num at hw ⊢
    omega
  have hh : word >>> 63 = 0#64 ∨ word >>> 63 = 1#64 := by
    have he : (word >>> 63).toNat = 0 ∨ (word >>> 63).toNat = 1 := by omega
    rcases he with he | he
    · exact Or.inl (BitVec.eq_of_toNat_eq he)
    · exact Or.inr (BitVec.eq_of_toNat_eq he)
  rcases hh with hh | hh <;> rw [hh] <;> decide +kernel

end Agave.Ed25519.Verifier.Execution.ScalarWide.Subtraction
