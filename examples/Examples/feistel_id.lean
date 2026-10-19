module

public import MLIR.Run.Tactic
public import Examples.Mlir.feistel_id
public import Examples.encrypt_round
public import Examples.decrypt_round
import Std.Tactic.BVDecide.Bitblast.BVExpr.Basic

namespace Examples.Mlir

open MLIR

/-! ## Specification -/

@[expose] public section

/-- One round of `encrypt_round` on the halves of `lr`, undone by `decrypt_round`. -/
def feistel_id.spec (lr : BitVec 128) (key : BitVec 64) : BitVec 128 :=
  let left := (lr >>> 64).setWidth 64
  let right := lr.setWidth 64
  let enc := encrypt_round.spec left right key
  decrypt_round.spec enc key

/-- Decrypting undoes encrypting: `feistel_id` is the identity. -/
theorem feistel_id.spec_eq (lr : BitVec 128) (key : BitVec 64) : feistel_id.spec lr key = lr := by
  unfold spec encrypt_round.spec
  extract_lets left right new_right enc
  unfold decrypt_round.spec
  extract_lets original_right left'
  have hor : original_right = BitVec.setWidth 128 right := by
    simp only [original_right, enc]
    bv_decide
  have henc : enc.setWidth 64 = new_right := by
    simp only [enc]
    bv_decide
  have hleft : left' = left := by
    simp only [left', hor, BitVec.setWidth_xor, BitVec.setWidth_mul _ _ (by decide : 64 ≤ 128), BitVec.setWidth_setWidth_of_le _ (by decide : 64 ≤ 128), BitVec.setWidth_eq, henc, new_right, BitVec.mul_comm right key]
    bv_decide
  rw [hor, hleft]
  simp only [left, right]
  bv_decide

end

/-! ## Proof -/

/-- The `trunc nuw` of the high half: it fits in 64 bits. -/
theorem feistel_id.trunc_nuw (lr : BitVec 128) :
    ((lr >>> 64).setWidth 64).setWidth 128 = lr >>> 64 := by
  bv_decide

/-- `feistel_id` returns `spec lr key`. -/
public theorem feistel_id.call_eq (lr : BitVec 128) (key : BitVec 64) (s : GlobalState)
    (hwf : s.WF) :
    feistel_id.call (feistel_id.args (.value lr) (.value key)) s =
      .value (.cons (.value lr) .nil, s) := by
  func_init
  block_init
  -- `uint64_t left = lr >> 64;`
  step_pure
  step_pure
  step_pure [feistel_id.trunc_nuw] with left
  -- `uint64_t right = lr;`
  step_pure with right
  -- `__uint128_t enc = encrypt_round(left, right, key);`
  /- ## Calls
  To step a call, use `step_call using` with the call_eq theorem for the function.
  The tactic will try to discharge any preconditions for you, but might leave ones
  that it cannot solve as open goals.
  -/
  step_call using encrypt_round.call_eq
  -- `return decrypt_round(enc, key);`
  step_call using decrypt_round.call_eq
  finish_block
  simp [hS, hleft, hright]
  exact feistel_id.spec_eq lr key

end Examples.Mlir
