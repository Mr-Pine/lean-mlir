import SSA.Projects.RIR.Semantics.Operations.Scalar
import SSA.Projects.Agave.Ed25519.Spec.Field
import Mathlib.Tactic

namespace Agave.Ed25519.Encoding
open LeanMLIR.RIR
section

theorem split_shift_value (x : BitVec 32) :
    Operation.shl {nsw := true, nuw := true}
      (.value (x.setWidth 64)) (.value 26#64) =
      .value (x.setWidth 64 <<< 26) := by
  have hx := x.isLt
  have hnat : (x.setWidth 64 <<< 26).toNat = x.toNat * 2^26 := by
    simp only [BitVec.toNat_shiftLeft,
      BitVec.toNat_setWidth_of_le (by decide : 32 ≤ 64), Nat.shiftLeft_eq]
    apply Nat.mod_eq_of_lt
    norm_num at hx ⊢
    omega
  have hu : (x.setWidth 64 <<< 26) >>> 26 = x.setWidth 64 := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, hnat, Nat.shiftRight_eq_div_pow,
      BitVec.toNat_setWidth_of_le (by decide : 32 ≤ 64)]
    omega
  have hm : (x.setWidth 64 <<< 26).msb = false := by
    rw [BitVec.msb_eq_false_iff_two_mul_lt, hnat]
    norm_num at hx ⊢
    omega
  have hs : (x.setWidth 64 <<< 26).sshiftRight 26 = x.setWidth 64 := by
    rw [BitVec.sshiftRight_eq_of_msb_false hm, hu]
  simp [Operation.shl, hu, hs]

theorem split_add_value (x y : BitVec 32) :
    Operation.add {nsw := true, nuw := true}
      (.value (y.setWidth 64 <<< 26)) (.value (x.setWidth 64)) =
      .value ((y.setWidth 64 <<< 26) + x.setWidth 64) := by
  have hx := x.isLt
  have hy := y.isLt
  have hnat : (y.setWidth 64 <<< 26).toNat = y.toNat * 2^26 := by
    simp only [BitVec.toNat_shiftLeft,
      BitVec.toNat_setWidth_of_le (by decide : 32 ≤ 64), Nat.shiftLeft_eq]
    apply Nat.mod_eq_of_lt
    norm_num at hy ⊢
    omega
  have hxi : (x.setWidth 64).toInt = x.toNat := by
    rw [BitVec.toInt_eq_toNat_of_lt,
      BitVec.toNat_setWidth_of_le (by decide : 32 ≤ 64)]
    simp only [BitVec.toNat_setWidth_of_le (by decide : 32 ≤ 64)]
    norm_num at hx ⊢
    omega
  have hyi : (y.setWidth 64 <<< 26).toInt = (y.toNat * 2^26 : Nat) := by
    rw [BitVec.toInt_eq_toNat_of_lt, hnat]
    rw [hnat]
    norm_num at hy ⊢
    omega
  have hu : (y.setWidth 64 <<< 26).uaddOverflow (x.setWidth 64) = false := by
    simp only [BitVec.uaddOverflow, hnat,
      BitVec.toNat_setWidth_of_le (by decide : 32 ≤ 64), decide_eq_false_iff_not]
    norm_num at hx hy ⊢
    omega
  have hs : (y.setWidth 64 <<< 26).saddOverflow (x.setWidth 64) = false := by
    simp only [BitVec.saddOverflow, hxi, hyi]
    norm_num at hx hy ⊢
    omega
  simp [Operation.add, hu, hs]

/-- LLVM's flagged widening, shift, and addition preserve the unbounded
pairing even for unrestricted physical u32 lanes. -/
theorem split_word_toNat (x y : BitVec 32) :
    ((y.setWidth 64 <<< 26) + x.setWidth 64).toNat = x.toNat + y.toNat * 2^26 := by
  have hb := Field.pair_u32_lt_u64 x y
  have hy : y.toNat * 2^26 < 2^64 := by omega
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft,
    BitVec.toNat_setWidth_of_le (by decide : 32 ≤ 64),
    Nat.shiftLeft_eq, Nat.mod_eq_of_lt hy]
  rw [Nat.add_comm, Nat.mod_eq_of_lt hb]

theorem split_word_eq (v : Field.Packed) (e : Field.Element) (i : Fin 5) :
    ((v i (Field.oddLane e)).setWidth 64 <<< 26) +
      (v i (Field.evenLane e)).setWidth 64 = Field.split v e i := by
  apply BitVec.eq_of_toNat_eq
  rw [split_word_toNat, Field.split_toNat]
  rfl

end
end Agave.Ed25519.Encoding
