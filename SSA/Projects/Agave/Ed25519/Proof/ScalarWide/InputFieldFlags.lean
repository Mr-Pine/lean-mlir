import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.MontgomeryProduct

/-! Algebraic and bit-index proofs for the wrapper's mixed-width input loads.
Disjoint OR flags follow from nonoverlapping bit intervals; no bitblasting. -/
namespace Agave.Ed25519.Verifier.Execution.ScalarWide
open LeanMLIR.RIR

/-- A loaded fragment positioned in a u64 input word. -/
def placedField (word : BitVec width) (offset : Nat) : BitVec 64 := word.setWidth 64 <<< offset

theorem placedField_toNat (word : BitVec width) (offset : Nat) (h : width + offset ≤ 64) :
    (placedField word offset).toNat = word.toNat * 2 ^ offset := by
  have hw : width ≤ 64 := by omega
  have hp : word.toNat * 2 ^ offset < 2 ^ 64 := by
    have hmul := Nat.mul_lt_mul_of_pos_right word.isLt (Nat.two_pow_pos offset)
    rw [← Nat.pow_add] at hmul
    exact hmul.trans_le (Nat.pow_le_pow_right (by decide : 1 ≤ 2) h)
  rw [placedField, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
    BitVec.toNat_setWidth_of_le hw, Nat.mod_eq_of_lt hp]

theorem placedField_inverse (word : BitVec width) (offset : Nat) (h : width + offset ≤ 64) :
    placedField word offset >>> offset = word.setWidth 64 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, placedField_toNat word offset h,
    Nat.shiftRight_eq_div_pow, Nat.mul_div_cancel _ (Nat.two_pow_pos offset),
    BitVec.toNat_setWidth_of_le (by omega : width ≤ 64)]

theorem field_shl_nuw (word : BitVec width) (offset : Nat)
    (h : width + offset ≤ 64) (hoff : offset < 64) :
    Operation.shl { nuw := true } (.value (word.setWidth 64))
      (.value (BitVec.ofNat 64 offset)) = .value (placedField word offset) := by
  have ho : offset < 2 ^ 64 := hoff.trans (by decide)
  have hi := placedField_inverse word offset h
  have hm : offset % 18446744073709551616 = offset := Nat.mod_eq_of_lt ho
  dsimp only [placedField] at hi ⊢
  simp [Operation.shl, hm, hoff, hi]

theorem field_shl_nsw_nuw (word : BitVec width) (offset : Nat)
    (h : width + offset ≤ 63) (hoff : offset < 64) :
    Operation.shl { nsw := true, nuw := true } (.value (word.setWidth 64))
      (.value (BitVec.ofNat 64 offset)) = .value (placedField word offset) := by
  have hu := placedField_inverse word offset (by omega : width + offset ≤ 64)
  have hm : (placedField word offset).msb = false := by
    apply BitVec.msb_eq_false_iff_two_mul_lt.mpr
    rw [placedField_toNat word offset (by omega)]
    have hp := Nat.mul_lt_mul_of_pos_right word.isLt (Nat.two_pow_pos offset)
    rw [← Nat.pow_add] at hp
    have he := Nat.pow_le_pow_right (by decide : 1 ≤ 2) h
    have hsmall : word.toNat * 2 ^ offset < 2 ^ 63 := hp.trans_le he
    norm_num at hsmall ⊢
    omega
  have hs : (placedField word offset).sshiftRight offset = word.setWidth 64 := by
    rw [BitVec.sshiftRight_eq_of_msb_false hm, hu]
  have ho : offset < 2 ^ 64 := hoff.trans (by decide)
  have hmod : offset % 18446744073709551616 = offset := Nat.mod_eq_of_lt ho
  dsimp only [placedField] at hu hs ⊢
  simp [Operation.shl, hmod, hoff, hu, hs]

theorem placedField_bit_outside (word : BitVec width) (offset i : Nat)
    (h : i < offset ∨ offset + width ≤ i) :
    (placedField word offset).getLsbD i = false := by
  rcases h with h | h
  · simp [placedField, BitVec.getLsbD_shiftLeft, h]
  · have hw : width ≤ i - offset := by omega
    simp [placedField, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth,
      BitVec.getLsbD_of_ge word (i - offset) hw]

theorem placedField_disjoint (a : BitVec wa) (b : BitVec wb) (oa ob : Nat)
    (h : oa + wa ≤ ob ∨ ob + wb ≤ oa) :
    placedField a oa &&& placedField b ob = 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  by_cases ha : i < oa ∨ oa + wa ≤ i
  · simp [BitVec.getLsbD_and, placedField_bit_outside a oa i ha]
  · have hb : i < ob ∨ ob + wb ≤ i := by omega
    simp [BitVec.getLsbD_and, placedField_bit_outside b ob i hb]

end Agave.Ed25519.Verifier.Execution.ScalarWide
