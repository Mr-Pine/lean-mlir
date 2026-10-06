module

public import SSA.Projects.Agave.Ed25519.Proof.Verifier.ExecutionElab

/-! Exact pinned MLIR region. Regenerate with MLIR/import_decompress.py.
All instructions and attributes are retained. Successful import is not an execution proof. -/

namespace Agave.Ed25519.Encoding.Decompress.Execution.BlackBox

open LeanMLIR.RIR
@[expose] public section

execution_def program  :=
{
  ^bb0(%arg0: i8):
    %0 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %1 = "llvm.alloca"(%0) <{alignment = 1 : i64, elem_type = i8}> : (i32) -> !llvm.ptr
    "llvm.store"(%arg0, %1) <{alignment = 1 : i64, ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %2 = "llvm.load"(%1) <{alignment = 1 : i64, ordering = 0 : i64, volatile_}> : (!llvm.ptr) -> i8
    "llvm.return"(%2) : (i8) -> ()
}

theorem block_count  : (program ).n = 1 := rfl

end
end Agave.Ed25519.Encoding.Decompress.Execution.BlackBox
