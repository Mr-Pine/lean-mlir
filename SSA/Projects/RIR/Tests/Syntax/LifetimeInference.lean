module

public import SSA.Projects.RIR.Syntax.Elab

/-! LLVM 22 lifetime imports: exact whole-object sizes, with fail-closed handling
of every pointer whose allocating object is not directly visible. -/
namespace LeanMLIR.RIR.Tests.Syntax.LifetimeInference

@[expose] public section

mlir_def explicitSize := {
  ^bb0:
    %0 = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %1 = "llvm.alloca"(%0) <{elem_type = !llvm.array<256 x i8>, alignment = 1 : i64}> : (i64) -> !llvm.ptr
    "llvm.intr.lifetime.start"(%1) <{size = 256 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%1) <{size = 256 : i64}> : (!llvm.ptr) -> ()
    "llvm.return"() : () -> ()
}

mlir_def inferredSize := {
  ^bb0:
    %0 = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %1 = "llvm.alloca"(%0) <{elem_type = !llvm.array<256 x i8>, alignment = 1 : i64}> : (i64) -> !llvm.ptr
    "llvm.intr.lifetime.start"(%1) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%1) : (!llvm.ptr) -> ()
    "llvm.return"() : () -> ()
}

/-- Inference changes no instruction or semantics relative to explicit size. -/
example : inferredSize = explicitSize := rfl

/-- error: ^bb0: "llvm.intr.lifetime.start"(%arg0) : (!llvm.ptr) -> (): missing lifetime size: pointer is not a direct alloca -/
#guard_msgs in
mlir_def rejectArgument := {
  ^bb0(%arg0: !llvm.ptr):
    "llvm.intr.lifetime.start"(%arg0) : (!llvm.ptr) -> ()
    "llvm.return"() : () -> ()
}

/-- error: ^bb0: "llvm.intr.lifetime.start"(%2) : (!llvm.ptr) -> (): missing lifetime size: pointer is not a direct alloca -/
#guard_msgs in
mlir_def rejectInterior := {
  ^bb0:
    %0 = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %1 = "llvm.alloca"(%0) <{elem_type = !llvm.array<256 x i8>}> : (i64) -> !llvm.ptr
    %2 = "llvm.getelementptr"(%1) <{elem_type = i8, rawConstantIndices = array<i32: 1>}> : (!llvm.ptr) -> !llvm.ptr
    "llvm.intr.lifetime.start"(%2) : (!llvm.ptr) -> ()
    "llvm.return"() : () -> ()
}

end
end LeanMLIR.RIR.Tests.Syntax.LifetimeInference
