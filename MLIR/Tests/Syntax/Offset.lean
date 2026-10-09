module

public import MLIR.Syntax.Elab
public import MLIR.Run.Tactic
meta import MLIR.Semantics.Func

/-! # `mlir_def` on a region numbered from `%arg3` and `%7`, as MLIR 19+ prints a module's -/

namespace MLIR.Tests.Syntax

@[expose] public section

mlir_def offset_min := {
  ^bb0(%arg3: i32):
    %7 = "llvm.mlir.constant"() <{value = 14 : i32}> : () -> i32
    %8 = "llvm.intr.smin"(%arg3, %7) : (i32, i32) -> i32
    "llvm.return"(%8) : (i32) -> ()
}

/-- `smin`'s result, as a mathematical function. -/
def offset_min.spec (x : BitVec 32) : BitVec 32 :=
  if x.slt 14#32 then x else 14#32

end

-- registers from slot `0`, named from the region's first
example : offset_min.Γ = ⟨2, [.bv 32], [.bv 32, .bv 32], rfl, 3, 7⟩ := rfl
example : (%8 : Reg offset_min.Γ (.bv 32)) = .val 1 rfl := rfl
example : (%arg3 : Reg offset_min.Γ (.bv 32)) = .arg 0 rfl := rfl

/-- info: %8 : Reg offset_min.Γ (Ty.bv 32) -/
#guard_msgs in
#check (%8 : Reg offset_min.Γ (.bv 32))

/-- error: the registers of this context start at 7 -/
#guard_msgs in
#check (%6 : Reg offset_min.Γ (.bv 32))

public theorem offset_min.call_eq (x : BitVec 32) (s : GlobalState) (hwf : s.WF) :
    offset_min.call (offset_min.args (.value x)) s =
      .value (.cons (.value (offset_min.spec x)) .nil, s) := by
  func_init
  block_init
  step_pure
  step_pure
  finish_block
  rw [hS, offset_min.spec]

example (E : ⟪offset_min.Γ⟫) (S : GlobalState) (x : BitVec 32)
    (hArgs : E.args = (offset_min.args (.value x)).get) :
    offset_min.runFrom (E[%7 := .value 14#32, %8 := .value 0#32]) 0 S =
      .value (.cons (.value (offset_min.spec x)) .nil, S) := by
  block_init
  step_pure
  step_pure
  finish_block
  rw [offset_min.spec]

end MLIR.Tests.Syntax
