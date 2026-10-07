import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.CancellationWords

namespace Agave.Ed25519.ScalarReduce32.Execution
open LeanMLIR.RIR

/-- Multiplication by the top nonzero L limb is emitted as a flagged shift. -/
theorem carry_shift44_flags (digit : BitVec 64) (h : digit.toNat < 2 ^ 52) :
    ((digit.setWidth 128 <<< 44) >>> 44 = digit.setWidth 128) ∧
    ((digit.setWidth 128 <<< 44).sshiftRight 44 = digit.setWidth 128) ∧
    (digit.setWidth 128 <<< 44).toNat = digit.toNat * 2 ^ 44 := by
  have hp : digit.toNat * 2 ^ 44 < 2 ^ 96 := by norm_num at h ⊢; omega
  have hn : (digit.setWidth 128 <<< 44).toNat = digit.toNat * 2 ^ 44 := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
      BitVec.toNat_setWidth_of_le (by decide : 64 ≤ 128)]
    exact Nat.mod_eq_of_lt (hp.trans (by decide))
  have hu : (digit.setWidth 128 <<< 44) >>> 44 = digit.setWidth 128 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, hn, Nat.shiftRight_eq_div_pow,
      BitVec.toNat_setWidth_of_le (by decide : 64 ≤ 128)]
    exact Nat.mul_div_cancel _ (by decide : 0 < 2 ^ 44)
  have hm : (digit.setWidth 128 <<< 44).msb = false := by
    apply BitVec.msb_eq_false_iff_two_mul_lt.mpr
    rw [hn]
    norm_num at hp ⊢
    omega
  exact ⟨hu, by rw [BitVec.sshiftRight_eq_of_msb_false hm, hu], hn⟩

/-- The final narrowing cast carries both flags in the actual scalar32 body. -/
theorem carry_trunc64_flags (word : BitVec 128) (h : word.toNat < 2 ^ 63) :
    (word.setWidth 64).setWidth 128 = word ∧
    (word.setWidth 64).signExtend 128 = word := by
  have hn : (word.setWidth 64).toNat = word.toNat := by
    rw [BitVec.toNat_setWidth]
    exact Nat.mod_eq_of_lt (h.trans (by decide))
  have hu : (word.setWidth 64).setWidth 128 = word := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth_of_le (by decide : 64 ≤ 128), hn]
  have hm : (word.setWidth 64).msb = false := by
    apply BitVec.msb_eq_false_iff_two_mul_lt.mpr
    rw [hn]
    norm_num at h ⊢
    omega
  exact ⟨hu, by rw [BitVec.signExtend_eq_setWidth_of_msb_false hm]; exact hu⟩

end Agave.Ed25519.ScalarReduce32.Execution
