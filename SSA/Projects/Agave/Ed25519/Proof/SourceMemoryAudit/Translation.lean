module

public import SSA.Projects.Agave.Ed25519.Proof.Verifier.ExecutionElab

/-! Kernel-checked witnesses of current importer erasure. These deliberately
small audit regions are not production imports. The equalities must cease to
hold if RIR later retains alignment or volatile events. -/
namespace Agave.Ed25519.SourceMemoryAudit.Translation
open LeanMLIR.RIR
@[expose] public section

execution_def ordinary := {
  ^bb0(%arg0: !llvm.ptr, %arg1: i64):
    "llvm.store"(%arg1, %arg0) <{alignment = 1 : i64, ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    %0 = "llvm.load"(%arg0) <{alignment = 1 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i64
    "llvm.return"(%0) : (i64) -> ()
}

execution_def aligned := {
  ^bb0(%arg0: !llvm.ptr, %arg1: i64):
    "llvm.store"(%arg1, %arg0) <{alignment = 128 : i64, ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    %0 = "llvm.load"(%arg0) <{alignment = 128 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i64
    "llvm.return"(%0) : (i64) -> ()
}

execution_def volatileAligned := {
  ^bb0(%arg0: !llvm.ptr, %arg1: i64):
    "llvm.store"(%arg1, %arg0) <{alignment = 128 : i64, ordering = 0 : i64, volatile_}> : (i64, !llvm.ptr) -> ()
    %0 = "llvm.load"(%arg0) <{alignment = 128 : i64, ordering = 0 : i64, volatile_}> : (!llvm.ptr) -> i64
    "llvm.return"(%0) : (i64) -> ()
}

theorem alignment_erased : aligned.entry.body = ordinary.entry.body := rfl
theorem volatile_erased : volatileAligned.entry.body = aligned.entry.body := rfl

end
end Agave.Ed25519.SourceMemoryAudit.Translation
