module

public import MLIR.Run.Tactic
public import Examples.Mlir.decrypt_round
import Std.Tactic.BVDecide

namespace Examples.Mlir

open MLIR

/-! ## Specification -/

@[expose] public section

/-- Undoes one Feistel round: the high half is `right`, the low half `left ^ f right`, in the
program's operand order. -/
def decrypt_round.spec (encrypted : BitVec 128) (key : BitVec 64) : BitVec 128 :=
  let original_right := encrypted >>> 64
  let left := (original_right * key.setWidth 128 ^^^ encrypted).setWidth 64 ^^^
    0xefdeadbeefcaffee#64
  left.setWidth 128 <<< 64 ||| original_right

/-! ## Proof -/

@[simp]
theorem decrypt_round.no_overflow (a : BitVec 128) (b : BitVec 64) : ¬ (a >>> 64).umulOverflow (BitVec.setWidth 128 b) := by
  have ha : (a >>> 64).toNat < 2 ^ 64 := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; have := a.isLt; omega
  have hb : (b.setWidth 128).toNat < 2 ^ 64 := by
    rw [BitVec.toNat_setWidth]; have := b.isLt; omega
  have := Nat.mul_lt_mul'' ha hb
  simp only [BitVec.umulOverflow, decide_eq_true_eq, Nat.not_le]
  omega

/-- Shifting a zero-extended 64-bit value up by 64 loses no bits. -/
@[simp] theorem setWidth_shiftLeft_ushiftRight (x : BitVec 64) :
    x.setWidth 128 <<< 64 >>> 64 = x.setWidth 128 := by bv_decide

/-- The high half and a value shifted down by 64 share no bits. -/
@[simp] theorem setWidth_shiftLeft_and_ushiftRight (x : BitVec 64) (y : BitVec 128) :
    x.setWidth 128 <<< 64 &&& y >>> 64 = 0#128 := by bv_decide

/-- `decrypt_round` returns `spec encrypted key`. -/
public theorem decrypt_round.call_eq (encrypted : BitVec 128) (key : BitVec 64) (s : GlobalState)
    (hwf : s.WF) :
    decrypt_round.call (decrypt_round.args (.value encrypted) (.value key)) s =
      .value (.cons (.value (decrypt_round.spec encrypted key)) .nil, s) := by
  func_init
  block_init
  iterate 7
    step_pure
  step_pure with left
  iterate 3
    step_pure
  finish_block
  simp [hS, hleft, spec]

end

end Examples.Mlir
