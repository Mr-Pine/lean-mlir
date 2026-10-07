import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.MontgomeryPart1

/-! Flag safety depends only on a digit's mask, even before its natural
Montgomery interpretation is established. -/
namespace Agave.Ed25519.Verifier.Execution.ScalarMontgomeryMul

open LeanMLIR.RIR

theorem masked52_bound (word : BitVec 64) :
    (word &&& 4503599627370495#64).toNat < 2 ^ 52 := by
  rw [mask52_toNat]
  exact Nat.mod_lt _ (by decide)

theorem masked52_zext (word : BitVec 64) :
    Operation.zext true (.value (word &&& 4503599627370495#64)) =
      .value ((word &&& 4503599627370495#64).setWidth 128) := by
  have hb := masked52_bound word
  have hm : (word &&& 4503599627370495#64).msb = false := by
    apply BitVec.msb_eq_false_iff_two_mul_lt.mpr
    norm_num at hb ⊢
    omega
  simp [Operation.zext, hm]

theorem masked52_mul0 (word : BitVec 64) :
    Operation.mul { nsw := true, nuw := true }
      (.value ((word &&& 4503599627370495#64).setWidth 128)) (.value 671914833335277#128) =
      .value ((word &&& 4503599627370495#64).setWidth 128 * 671914833335277#128) :=
  adjustment_mul_flags _ _ (masked52_bound word) (by decide)

theorem masked52_mul1 (word : BitVec 64) :
    Operation.mul { nsw := true, nuw := true }
      (.value ((word &&& 4503599627370495#64).setWidth 128)) (.value 3916664325105025#128) =
      .value ((word &&& 4503599627370495#64).setWidth 128 * 3916664325105025#128) :=
  adjustment_mul_flags _ _ (masked52_bound word) (by decide)

theorem masked52_mul2 (word : BitVec 64) :
    Operation.mul { nsw := true, nuw := true }
      (.value ((word &&& 4503599627370495#64).setWidth 128)) (.value 1367801#128) =
      .value ((word &&& 4503599627370495#64).setWidth 128 * 1367801#128) :=
  adjustment_mul_flags _ _ (masked52_bound word) (by decide)

/-- The source multiplication by 2^44 retains all 96 product bits and its sign. -/
theorem masked52_shl44 (word : BitVec 64) :
    Operation.shl { nsw := true, nuw := true }
      (.value ((word &&& 4503599627370495#64).setWidth 128)) (.value 44#128) =
      .value (((word &&& 4503599627370495#64).setWidth 128) <<< 44) := by
  let digit := (word &&& 4503599627370495#64).setWidth 128
  have hd : digit.toNat < 2 ^ 52 := by
    rw [BitVec.toNat_setWidth_of_le (by decide : 64 ≤ 128)]
    exact masked52_bound word
  have hp : digit.toNat * 2 ^ 44 < 2 ^ 96 := by norm_num at hd ⊢; omega
  have hn : (digit <<< 44).toNat = digit.toNat * 2 ^ 44 := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
    exact Nat.mod_eq_of_lt (hp.trans (by decide))
  have hunsigned : (digit <<< 44) >>> 44 = digit := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, hn, Nat.shiftRight_eq_div_pow]
    exact Nat.mul_div_cancel _ (by decide : 0 < 2 ^ 44)
  have hm : (digit <<< 44).msb = false := by
    apply BitVec.msb_eq_false_iff_two_mul_lt.mpr
    rw [hn]
    norm_num at hp ⊢
    omega
  have hsigned : (digit <<< 44).sshiftRight 44 = digit := by
    rw [BitVec.sshiftRight_eq_of_msb_false hm]
    exact hunsigned
  change Operation.shl { nsw := true, nuw := true } (.value digit) (.value 44#128) =
    .value (digit <<< 44)
  simp [Operation.shl, hunsigned, hsigned]

end Agave.Ed25519.Verifier.Execution.ScalarMontgomeryMul
