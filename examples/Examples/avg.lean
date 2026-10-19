module

public import MLIR.Run.Tactic
public import Examples.Mlir.avg
import Std.Tactic.BVDecide.Bitblast.BVExpr.Basic

namespace Examples.Mlir

open MLIR

/-! ## Specification -/

/-
The `call_eq` proof gets easier if the spec is close to the algorithm
the function implements
-/

@[expose] public section

/-- `(a & b) + ((a ^ b) >> 1)`, in the program's operand order. -/
def avg.spec (a b : BitVec 64) : BitVec 64 :=
  ((b ^^^ a) >>> 1) + (b &&& a)

/-
The semantics of the spec can then be proven separately
-/

def avg.semantics (a b : BitVec 64) : Nat :=
  (a.toNat + b.toNat) / 2

theorem avg.spec_semantics : (avg.spec a b).toNat = avg.semantics a b := by
  have h : (spec a b).setWidth 65 = (a.setWidth 65 + b.setWidth 65) >>> 1 := by
    simp only [spec]; bv_decide
  have h' := congrArg BitVec.toNat h
  simp only [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow] at h'
  have := a.isLt; have := b.isLt; have := (avg.spec a b).isLt
  simp only [semantics]
  omega

end

/-! ## Proof -/

/-- `avg` returns `spec a b`. -/
public theorem avg.call_eq (a b : BitVec 64) (s : GlobalState) (hwf : s.WF) :
    avg.call (avg.args (.value a) (.value b)) s =
      .value (.cons (.value (avg.spec a b)) .nil, s) := by
  -- A mlir proof always starts out with `func_init`
  func_init
  -- If the state contains a `<func>.runFrom E i S` with a concrete `i`,
  -- `block_init` is the tactic to "enter" the basic block `i`
  block_init
  -- You should now see the current and next instructions in your InfoView
  -- If the next instruction is pure (does not depend on or change the State),
  -- step_pure is the tactic of choice
  step_pure
  step_pure
  -- By default, the values are inserted into the env directly,
  -- but you can also name them
  step_pure with xored
  step_pure
  step_pure
  -- When the InfoView shows `exit`, use the `finish_block` tactic:
  finish_block
  simp [spec, hS, hxored]

end Examples.Mlir
