module

public import SSA.Projects.RIR.Syntax.Elab
meta import SSA.Projects.RIR.Semantics.Func

/-! # `llvm.mlir.zero` at `!llvm.ptr`, and `llvm.icmp` `eq`/`ne` on pointers -/

namespace LeanMLIR.RIR.Tests.Syntax.Null

@[expose] public section

mlir_def isNull := {
  ^bb0(%arg0: !llvm.ptr):
    %0 = "llvm.mlir.zero"() : () -> !llvm.ptr
    %1 = "llvm.icmp"(%arg0, %0) <{predicate = 0 : i64}> : (!llvm.ptr, !llvm.ptr) -> i1
    %2 = "llvm.icmp"(%arg0, %0) <{predicate = 1 : i64}> : (!llvm.ptr, !llvm.ptr) -> i1
    "llvm.return"(%1, %2) : (i1, i1) -> ()
}

end

/-- error: ^bb0: %1 = "llvm.icmp"(%arg0, %0) : (!llvm.ptr, !llvm.ptr) -> i1: pointers compare only by `eq` and `ne` -/
#guard_msgs in
mlir_def ordered := {
  ^bb0(%arg0: !llvm.ptr):
    %0 = "llvm.mlir.zero"() : () -> !llvm.ptr
    %1 = "llvm.icmp"(%arg0, %0) <{predicate = 6 : i64}> : (!llvm.ptr, !llvm.ptr) -> i1
    "llvm.return"(%1) : (i1) -> ()
}

/-! ## Execution tests -/

section Tests

/-- `isNull`'s `eq` and `ne` on `p`, or `none` for UB. -/
private def cmp (p : Pointer) : Option (BitVec 1 × BitVec 1) :=
  match isNull.eval 1 (isNull.args (.value p)) ⟨⟨1⟩, ⟨∅⟩⟩ with
  | .value (some (.cons (.value e) (.cons (.value n) .nil)), _) => some (e, n)
  | _ => none

#guard cmp Pointer.null == some (1#1, 0#1)
#guard cmp ⟨⟨1⟩, 0⟩ == some (0#1, 1#1)
-- block `0` at another offset is not null
#guard cmp ⟨⟨0⟩, 8⟩ == some (0#1, 1#1)

end Tests

end LeanMLIR.RIR.Tests.Syntax.Null
