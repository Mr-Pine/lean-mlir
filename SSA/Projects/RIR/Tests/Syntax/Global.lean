module

public import SSA.Projects.RIR.Syntax.Elab
meta import SSA.Projects.RIR.Semantics.Func
meta import SSA.Projects.RIR.Semantics.GlobalInitializer

/-! # `mlir_const_def`, and `llvm.mlir.addressof` of the global it defines -/

namespace LeanMLIR.RIR.Tests.Syntax.Global

@[expose] public section

mlir_const_def answer := {
    %0 = "llvm.mlir.constant"() <{value = 42 : i64}> : () -> i64
    "llvm.return"(%0) : (i64) -> ()
}

example : answer.t = .bv 64 := rfl

mlir_def readAnswer := {
    %0 = "llvm.mlir.addressof"() <{global_name = @answer}> : () -> !llvm.ptr
    %1 = "llvm.load"(%0) <{alignment = 8 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i64
    "llvm.return"(%1) : (i64) -> ()
} with @answer := answer

end

/-! ## Execution tests -/

section Tests

/-- What `readAnswer` returns from an empty state, or `none` for UB. -/
private def out : Option (BitVec 64) :=
  match readAnswer.eval 1 readAnswer.args ⟨⟨0⟩, ⟨∅⟩⟩ with
  | .value (some (.cons (.value v) .nil), _) => some v
  | _ => none

#guard out == some 42#64

end Tests

end LeanMLIR.RIR.Tests.Syntax.Global
