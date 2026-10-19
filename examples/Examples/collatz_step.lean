module

public import MLIR.Run.Tactic
public import Examples.Mlir.collatz_step
import Std.Tactic.BVDecide

namespace Examples.Mlir

open MLIR

/-! ## Specification -/

@[expose] public section

/-- `n / 2` for even `n`, else `3 * n + 1`, in the program's operand order. -/
def collatz_step.spec (n : BitVec 32) : BitVec 32 :=
  if n &&& 1#32 = 0#32 then n.sshiftRight 1 else n * 3#32 + 1#32

/-! ## Proof -/

/-- The `icmp` tests that `n` is even. -/
@[simp]
theorem collatz_step.icmp_eq (n : BitVec 32) :
    (BitVec.ofBool (n &&& 1#32 == 0#32) = 1#1) = (n &&& 1#32 = 0#32) := by
  apply propext; bv_decide

/-- The `ashr exact` tests that `n` is even. -/
@[simp]
theorem collatz_step.lsb_eq (n : BitVec 32) :
    (BitVec.extractLsb' 0 1 n = 0#1) = (n &&& 1#32 = 0#32) := by
  apply propext; bv_decide

/-- `collatz_step` returns `spec n`, for odd `n` only if `3 * n + 1` fits in an `int`. -/
public theorem collatz_step.call_eq (n : BitVec 32) (s : GlobalState) (hwf : s.WF) :
    collatz_step.call (collatz_step.args (.value n)) s =
      .value (.cons (.value (collatz_step.spec n)) .nil, s) := by
  func_init
  block_init
  iterate 5
    step_pure
  -- As you can see in the InfoView, we have a branch here
  -- finish_block splits the cases for us
  finish_block
  case isTrue =>
    -- New basic block
    block_init
    step_pure
    finish_block
    block_init
    finish_block
    simp [hS, hbr, spec]
  case isFalse =>
    block_init
    step_pure
    step_pure
    finish_block
    block_init
    finish_block
    simp [hS, spec, hbr]

end

end Examples.Mlir
