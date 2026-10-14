module

public import MLIR.Syntax.Elab
meta import MLIR.Semantics.Func
meta import MLIR.Semantics.GlobalInitializer

/-! # Globals pointing at globals: an `addressof` member, resolved by the table -/

namespace MLIR.Tests.Syntax.GlobalPointers

@[expose] public section

mlir_const_def target := {
    %0 = "llvm.mlir.constant"() <{value = dense<[7, 8]> : tensor<2xi64>}> : () -> !llvm.array<2 x i64>
    "llvm.return"(%0) : (!llvm.array<2 x i64>) -> ()
}

/-- `{ &target, 5 }`, built as LLVM's importer writes a constant struct. -/
mlir_const_def holder := {
    %0 = "llvm.mlir.constant"() <{value = 5 : i64}> : () -> i64
    %1 = "llvm.mlir.addressof"() <{global_name = @target}> : () -> !llvm.ptr
    %2 = "llvm.mlir.undef"() : () -> !llvm.struct<(i64, ptr)>
    %3 = "llvm.insertvalue"(%2, %0) <{position = array<i64: 0>}> : (!llvm.struct<(i64, ptr)>, i64) -> !llvm.struct<(i64, ptr)>
    %4 = "llvm.insertvalue"(%3, %1) <{position = array<i64: 1>}> : (!llvm.struct<(i64, ptr)>, !llvm.ptr) -> !llvm.struct<(i64, ptr)>
    "llvm.return"(%4) : (!llvm.struct<(i64, ptr)>) -> ()
}

-- the member at bit 64, into `target` at byte 0
example : holder.ptrs = [(64, "target", 0)] := rfl

/-- `&target[1]` alone: a constant `getelementptr` off the address. -/
mlir_const_def second := {
    %0 = "llvm.mlir.addressof"() <{global_name = @target}> : () -> !llvm.ptr
    %1 = "llvm.getelementptr"(%0) <{elem_type = i64, noWrapFlags = 1 : i32, rawConstantIndices = array<i32: 1>}> : (!llvm.ptr) -> !llvm.ptr
    "llvm.return"(%1) : (!llvm.ptr) -> ()
}

example : second.ptrs = [(0, "target", 8)] := rfl

/-- `holder`'s pointer, loaded: whether it is `target`'s address, and the word through it. -/
mlir_def viaHolder := {
    %0 = "llvm.mlir.addressof"() <{global_name = @holder}> : () -> !llvm.ptr
    %1 = "llvm.getelementptr"(%0) <{elem_type = i8, rawConstantIndices = array<i32: 8>}> : (!llvm.ptr) -> !llvm.ptr
    %2 = "llvm.load"(%1) <{alignment = 8 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> !llvm.ptr
    %3 = "llvm.mlir.addressof"() <{global_name = @target}> : () -> !llvm.ptr
    %4 = "llvm.icmp"(%2, %3) <{predicate = 0 : i64}> : (!llvm.ptr, !llvm.ptr) -> i1
    %5 = "llvm.load"(%2) <{alignment = 8 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i64
    "llvm.return"(%4, %5) : (i1, i64) -> ()
} with @holder := holder, @target := target

/-- `second`'s pointer, loaded, and the word through it; its bits, as an integer. -/
mlir_def viaSecond := {
    %0 = "llvm.mlir.addressof"() <{global_name = @second}> : () -> !llvm.ptr
    %1 = "llvm.load"(%0) <{alignment = 8 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> !llvm.ptr
    %2 = "llvm.load"(%1) <{alignment = 8 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i64
    %3 = "llvm.load"(%0) <{alignment = 8 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i64
    %4 = "llvm.ptrtoaddr"(%1) : (!llvm.ptr) -> i64
    %5 = "llvm.icmp"(%3, %4) <{predicate = 0 : i64}> : (i64, i64) -> i1
    "llvm.return"(%2, %5) : (i64, i1) -> ()
} with @second := second, @target := target

/-- `viaSecond` with only `second` in the table. -/
mlir_def viaSecondAlone := {
    %0 = "llvm.mlir.addressof"() <{global_name = @second}> : () -> !llvm.ptr
    %1 = "llvm.load"(%0) <{alignment = 8 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> !llvm.ptr
    %2 = "llvm.ptrtoaddr"(%1) : (!llvm.ptr) -> i64
    "llvm.return"(%2) : (i64) -> ()
} with @second := second

end

/-! ## Execution tests -/

section Tests

/-- Addresses: block `b` at `0x1000 * b`. -/
private instance addrs : Unspecified :=
  ⟨fun b => BitVec.ofNat 64 (0x1000 * b.id), fun _ _ _ => 0, fun _ _ _ => 0⟩

/-- An empty state, its blocks at `addrs`. -/
private def s0 : GlobalState :=
  ⟨⟨1⟩, @MemoryState.mk ∅ addrs ⟨fun _ => none⟩⟩

-- `holder`'s member is `target`'s address, and loads through to its first word
#guard
  match viaHolder.eval 1 viaHolder.args (GlobalState.withGlobals viaHolder.globals s0) with
  | .value (some (.cons a (.cons b .nil)), _) => a == .value 1 && b == .value 7
  | _ => false

-- `second`'s, `target`'s second word, its bits `ptrtoaddr`'s
#guard
  match viaSecond.eval 1 viaSecond.args (GlobalState.withGlobals viaSecond.globals s0) with
  | .value (some (.cons a (.cons b .nil)), _) => a == .value 8 && b == .value 1
  | _ => false

-- without `target` in the table, the member is undefined: poison, whose `ptrtoaddr` is
#guard
  match viaSecondAlone.eval 1 viaSecondAlone.args
      (GlobalState.withGlobals viaSecondAlone.globals s0) with
  | .value (some (.cons a .nil), _) => a == .poison
  | _ => false

end Tests

end MLIR.Tests.Syntax.GlobalPointers
