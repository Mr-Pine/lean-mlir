import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.PackSafety

namespace Agave.Ed25519.ScalarReduce32.Execution
open LeanMLIR.RIR

/-- The five input limbs are nonnegative even under signed u64 interpretation. -/
theorem product_limb_nonneg (x : BitVec 64) (h : x.toNat < 2 ^ 52) :
    x.msb = false := by
  apply BitVec.msb_eq_false_iff_two_mul_lt.mpr
  norm_num at h ⊢
  omega

/-- Both flags of multiplication by a source R limb, with exact natural value. -/
theorem product_constant_flags (x : BitVec 64) (c : BitVec 128)
    (hx : x.toNat < 2 ^ 52) (hc : c.toNat < 2 ^ 52) :
    (x.setWidth 128).umulOverflow c = false ∧
    (x.setWidth 128).smulOverflow c = false ∧
    (x.setWidth 128 * c).toNat = x.toNat * c.toNat := by
  have hp : x.toNat * c.toNat < 2 ^ 104 := by
    have h := Nat.mul_lt_mul_of_le_of_lt (Nat.le_of_lt hx) hc
      (by decide : 0 < 2 ^ 52)
    norm_num at h ⊢
    exact h
  have hxi : (x.setWidth 128).toInt = (x.toNat : Int) := by
    rw [BitVec.toInt_eq_toNat_of_lt (by
      rw [BitVec.toNat_setWidth_of_le (by decide : 64 ≤ 128)]
      norm_num at hx ⊢
      omega), BitVec.toNat_setWidth_of_le (by decide : 64 ≤ 128)]
  have hci : c.toInt = (c.toNat : Int) :=
    BitVec.toInt_eq_toNat_of_lt (by norm_num at hc ⊢; omega)
  refine ⟨?_, ?_, ?_⟩
  · simp only [BitVec.umulOverflow,
      BitVec.toNat_setWidth_of_le (by decide : 64 ≤ 128)]
    norm_num at hp ⊢
    omega
  · simp only [BitVec.smulOverflow, hxi, hci, ← Int.natCast_mul]
    norm_num at hp ⊢
    omega
  · rw [BitVec.toNat_mul, BitVec.toNat_setWidth_of_le (by decide : 64 ≤ 128)]
    apply Nat.mod_eq_of_lt
    exact hp.trans (by decide)

/-- A positive column sum below the signed u128 limit satisfies both add flags. -/
theorem product_add_flags (a b : BitVec 128)
    (h : a.toNat + b.toNat < 2 ^ 127) :
    a.uaddOverflow b = false ∧ a.saddOverflow b = false ∧
    (a + b).toNat = a.toNat + b.toNat := by
  have hai : a.toInt = (a.toNat : Int) :=
    BitVec.toInt_eq_toNat_of_lt (by norm_num at h ⊢; omega)
  have hbi : b.toInt = (b.toNat : Int) :=
    BitVec.toInt_eq_toNat_of_lt (by norm_num at h ⊢; omega)
  refine ⟨?_, ?_, ?_⟩
  · simp only [BitVec.uaddOverflow]
    norm_num at h ⊢
    omega
  · simp only [BitVec.saddOverflow, hai, hbi]
    norm_num at h ⊢
    omega
  · rw [BitVec.toNat_add]
    apply Nat.mod_eq_of_lt
    exact h.trans (by decide)

end Agave.Ed25519.ScalarReduce32.Execution
