module

public import SSA.Projects.RIR.Syntax.Elab
meta import SSA.Projects.RIR.Semantics.Func

/-! # Struct padding: a stored struct's fields are where `getelementptr` finds them -/

namespace LeanMLIR.RIR.Tests.Syntax.Padding

@[expose] public section

/-- Store `(a, b)` as a `struct<(i8, i64)>`, then load `b` through its field address. -/
mlir_def storeStruct := {
  ^bb0(%arg0: !llvm.ptr, %arg1: i8, %arg2: i64):
    %0 = "llvm.mlir.undef"() : () -> !llvm.struct<(i8, i64)>
    %1 = "llvm.insertvalue"(%0, %arg1) <{position = array<i64: 0>}> : (!llvm.struct<(i8, i64)>, i8) -> !llvm.struct<(i8, i64)>
    %2 = "llvm.insertvalue"(%1, %arg2) <{position = array<i64: 1>}> : (!llvm.struct<(i8, i64)>, i64) -> !llvm.struct<(i8, i64)>
    "llvm.store"(%2, %arg0) <{alignment = 8 : i64, ordering = 0 : i64}> : (!llvm.struct<(i8, i64)>, !llvm.ptr) -> ()
    %3 = "llvm.getelementptr"(%arg0) <{elem_type = !llvm.struct<(i8, i64)>, rawConstantIndices = array<i32: 0, 1>}> : (!llvm.ptr) -> !llvm.ptr
    %4 = "llvm.load"(%3) <{alignment = 8 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i64
    "llvm.return"(%4) : (i64) -> ()
}

/-- Store `a` and `b` through their field addresses, then load the whole struct. -/
mlir_def storeFields := {
  ^bb0(%arg0: !llvm.ptr, %arg1: i8, %arg2: i64):
    %0 = "llvm.getelementptr"(%arg0) <{elem_type = !llvm.struct<(i8, i64)>, rawConstantIndices = array<i32: 0, 1>}> : (!llvm.ptr) -> !llvm.ptr
    "llvm.store"(%arg1, %arg0) <{alignment = 8 : i64, ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    "llvm.store"(%arg2, %0) <{alignment = 8 : i64, ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    %1 = "llvm.load"(%arg0) <{alignment = 8 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> !llvm.struct<(i8, i64)>
    "llvm.return"(%1) : (!llvm.struct<(i8, i64)>) -> ()
}

end

/-! ## Execution tests -/

section Tests

private def p : Pointer := ⟨⟨1⟩, 0⟩

/-- Block `1`: 16 zero bytes, one `struct<(i8, i64)>`. -/
private def blank : GlobalState :=
  ⟨⟨2⟩, ⟨Std.ExtHashMap.ofList [(⟨1⟩, ⟨16, 0#128⟩)]⟩⟩

#guard (match storeStruct.eval 1 (storeStruct.args (.value p) (.value 7) (.value 42)) blank with
  | .value (some (.cons (.value v) .nil), _) => some v
  | _ => none) == some 42

#guard (match storeFields.eval 1 (storeFields.args (.value p) (.value 7) (.value 42)) blank with
  | .value (some (.cons (.value a, .value b) .nil), _) => some (a, b)
  | _ => none) == some (7, 42)

end Tests

end LeanMLIR.RIR.Tests.Syntax.Padding
