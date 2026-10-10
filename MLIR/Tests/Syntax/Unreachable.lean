module

public import MLIR.Syntax.Elab
public import MLIR.Run.Tactic
meta import MLIR.Semantics.Func

/-! # `llvm.unreachable` and `noreturn` calls: UB -/

namespace MLIR.Tests.Syntax.Unreachable

@[expose] public section

/-- A bounds check as rustc writes it: the panic, unbound, is `noreturn`, then `unreachable`. -/
mlir_def checked := {
  ^bb0(%arg0: i64, %arg1: !llvm.ptr):
    %0 = "llvm.mlir.constant"() <{value = 5 : i64}> : () -> i64
    %1 = "llvm.icmp"(%arg0, %0) <{predicate = 6 : i64}> : (i64, i64) -> i1
    "llvm.cond_br"(%1)[^bb1, ^bb2] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
  ^bb1:
    "llvm.return"(%arg0) : (i64) -> ()
  ^bb2:
    "llvm.call"(%arg0, %0, %arg1) <{CConv = #llvm.cconv<fastcc>, TailCallKind = #llvm.tailcallkind<none>, callee = @_RNvNtCsgxBkk5gSRhY_4core9panicking18panic_bounds_check, fastmathFlags = #llvm.fastmath<none>, no_inline, noreturn, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 3, 0>}> : (i64, i64, !llvm.ptr) -> ()
    "llvm.unreachable"() : () -> ()
}

example : checked.bb2.body.length = 1 := rfl

end

/-! ## Execution tests -/

section Tests

/-- `checked i`'s result, or `none` for UB. -/
private def checkedOut (i : BitVec 64) : Option ⟦Ty.bv 64⟧ :=
  match checked.eval 2 (checked.args (.value i) (.value Pointer.null)) ⟨⟨1⟩, ⟨∅⟩⟩ with
  | .value (some (.cons v .nil), _) => some v
  | _ => none

#guard checkedOut 4 == some (.value 4)
#guard checkedOut 5 == none

/-- `unreachable` alone: UB. -/
mlir_def never := {
    "llvm.unreachable"() : () -> ()
}

#guard (match never.eval 1 .nil ⟨⟨1⟩, ⟨∅⟩⟩ with
  | .value _ => false
  | _ => true)

end Tests

/-! ## Steps -/

section Steps

-- the check passes: the panic's block is never entered
example (i : BitVec 64) (p : Pointer) (s : GlobalState) (hwf : s.WF) (hi : i.ult 5#64 = true) :
    checked.call (checked.args (.value i) (.value p)) s = .value (.cons (.value i) .nil, s) := by
  func_init
  block_init
  step_pure
  step_pure [hi]
  finish_block
  block_init
  finish_block
  rw [hS]

end Steps

end MLIR.Tests.Syntax.Unreachable
