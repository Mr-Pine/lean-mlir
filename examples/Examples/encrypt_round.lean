module

public import MLIR.Run.Tactic
public import Examples.Mlir.encrypt_round
import Std.Tactic.BVDecide

namespace Examples.Mlir

open MLIR

/-! ## Specification -/

@[expose] public section

/-- One Feistel round: `right` moves to the high half, `left ^ f right` to the low half, in the
program's operand order. -/
def encrypt_round.spec (left right key : BitVec 64) : BitVec 128 :=
  let new_right := left ^^^ key * right ^^^ 0xefdeadbeefcaffee#64
  right.setWidth 128 <<< 64 ||| new_right.setWidth 128

/-! ## Proof -/

/-- The `shl nuw`: shifting a zero-extended 64-bit value up by 64 loses no bits. -/
theorem encrypt_round.shl_nuw (x : BitVec 64) :
    (x.setWidth 128 <<< 64) >>> 64 = x.setWidth 128 := by bv_decide

/-- The `or disjoint`: the high and low halves share no bits. -/
theorem encrypt_round.or_disjoint (x y : BitVec 64) :
    (x.setWidth 128 <<< 64) &&& y.setWidth 128 = 0#128 := by bv_decide

attribute [local simp] encrypt_round.shl_nuw encrypt_round.or_disjoint

/-- `encrypt_round` returns `spec left right key`. -/
public theorem encrypt_round.call_eq (left right key : BitVec 64) (s : GlobalState)
    (hwf : s.WF) :
    encrypt_round.call (encrypt_round.args (.value left) (.value right) (.value key)) s =
      .value (.cons (.value (encrypt_round.spec left right key)) .nil, s) := by
  func_init
  block_init
  iterate 5
    step_pure
  step_pure with new_right
  iterate 3
    step_pure
  finish_block
  simp [hS, hnew_right, spec]

end

end Examples.Mlir
