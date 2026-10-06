module

public import SSA.Projects.Agave.Ed25519.Proof.Verifier.ExecutionElab

/-! Exact pinned MLIR region. Regenerate with MLIR/import_decompress.py.
All instructions and attributes are retained. Successful import is not an execution proof. -/

namespace Agave.Ed25519.Encoding.Decompress.Execution.Pow2k

open LeanMLIR.RIR
@[expose] public section

execution_def program  :=
{
  ^bb0(%arg0: !llvm.ptr, %arg1: !llvm.ptr, %arg2: i32):
    %0 = "llvm.mlir.constant"() <{value = 8 : i64}> : () -> i64
    %1 = "llvm.mlir.constant"() <{value = 16 : i64}> : () -> i64
    %2 = "llvm.mlir.constant"() <{value = 24 : i64}> : () -> i64
    %3 = "llvm.mlir.constant"() <{value = 32 : i64}> : () -> i64
    %4 = "llvm.mlir.constant"() <{value = 19 : i64}> : () -> i64
    %5 = "llvm.mlir.constant"() <{value = 1 : i128}> : () -> i128
    %6 = "llvm.mlir.constant"() <{value = 51 : i128}> : () -> i128
    %7 = "llvm.mlir.constant"() <{value = 18446744073709551615 : i128}> : () -> i128
    %8 = "llvm.mlir.constant"() <{value = 2251799813685247 : i64}> : () -> i64
    %9 = "llvm.mlir.constant"() <{value = 51 : i64}> : () -> i64
    %10 = "llvm.mlir.constant"() <{value = -1 : i32}> : () -> i32
    %11 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %12 = "llvm.load"(%arg1) <{alignment = 8 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i64
    %13 = "llvm.getelementptr"(%arg1, %0) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %14 = "llvm.load"(%13) <{alignment = 8 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i64
    %15 = "llvm.getelementptr"(%arg1, %1) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %16 = "llvm.load"(%15) <{alignment = 8 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i64
    %17 = "llvm.getelementptr"(%arg1, %2) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %18 = "llvm.load"(%17) <{alignment = 8 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i64
    %19 = "llvm.getelementptr"(%arg1, %3) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %20 = "llvm.load"(%19) <{alignment = 8 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i64
    "llvm.br"(%20, %18, %16, %14, %12, %arg2)[^bb1] : (i64, i64, i64, i64, i64, i32) -> ()
  ^bb1(%21: i64, %22: i64, %23: i64, %24: i64, %25: i64, %26: i32):  // 2 preds: ^bb0, ^bb1
    %27 = "llvm.mul"(%22, %4) <{overflowFlags = 0 : i32}> : (i64, i64) -> i64
    %28 = "llvm.mul"(%21, %4) <{overflowFlags = 0 : i32}> : (i64, i64) -> i64
    %29 = "llvm.zext"(%25) : (i64) -> i128
    %30 = "llvm.mul"(%29, %29) <{overflowFlags = 2 : i32}> : (i128, i128) -> i128
    %31 = "llvm.zext"(%24) : (i64) -> i128
    %32 = "llvm.zext"(%28) : (i64) -> i128
    %33 = "llvm.mul"(%31, %32) <{overflowFlags = 2 : i32}> : (i128, i128) -> i128
    %34 = "llvm.zext"(%23) : (i64) -> i128
    %35 = "llvm.zext"(%27) : (i64) -> i128
    %36 = "llvm.mul"(%34, %35) <{overflowFlags = 2 : i32}> : (i128, i128) -> i128
    %37 = "llvm.add"(%33, %36) <{overflowFlags = 0 : i32}> : (i128, i128) -> i128
    %38 = "llvm.shl"(%37, %5) <{overflowFlags = 0 : i32}> : (i128, i128) -> i128
    %39 = "llvm.add"(%38, %30) <{overflowFlags = 0 : i32}> : (i128, i128) -> i128
    %40 = "llvm.zext"(%22) : (i64) -> i128
    %41 = "llvm.mul"(%35, %40) <{overflowFlags = 2 : i32}> : (i128, i128) -> i128
    %42 = "llvm.mul"(%29, %31) <{overflowFlags = 2 : i32}> : (i128, i128) -> i128
    %43 = "llvm.mul"(%34, %32) <{overflowFlags = 2 : i32}> : (i128, i128) -> i128
    %44 = "llvm.add"(%42, %43) <{overflowFlags = 0 : i32}> : (i128, i128) -> i128
    %45 = "llvm.shl"(%44, %5) <{overflowFlags = 0 : i32}> : (i128, i128) -> i128
    %46 = "llvm.add"(%45, %41) <{overflowFlags = 0 : i32}> : (i128, i128) -> i128
    %47 = "llvm.mul"(%31, %31) <{overflowFlags = 2 : i32}> : (i128, i128) -> i128
    %48 = "llvm.mul"(%29, %34) <{overflowFlags = 2 : i32}> : (i128, i128) -> i128
    %49 = "llvm.zext"(%21) : (i64) -> i128
    %50 = "llvm.mul"(%35, %49) <{overflowFlags = 2 : i32}> : (i128, i128) -> i128
    %51 = "llvm.add"(%48, %50) <{overflowFlags = 0 : i32}> : (i128, i128) -> i128
    %52 = "llvm.shl"(%51, %5) <{overflowFlags = 0 : i32}> : (i128, i128) -> i128
    %53 = "llvm.add"(%52, %47) <{overflowFlags = 0 : i32}> : (i128, i128) -> i128
    %54 = "llvm.mul"(%32, %49) <{overflowFlags = 2 : i32}> : (i128, i128) -> i128
    %55 = "llvm.mul"(%29, %40) <{overflowFlags = 2 : i32}> : (i128, i128) -> i128
    %56 = "llvm.mul"(%31, %34) <{overflowFlags = 2 : i32}> : (i128, i128) -> i128
    %57 = "llvm.add"(%55, %56) <{overflowFlags = 0 : i32}> : (i128, i128) -> i128
    %58 = "llvm.shl"(%57, %5) <{overflowFlags = 0 : i32}> : (i128, i128) -> i128
    %59 = "llvm.add"(%58, %54) <{overflowFlags = 0 : i32}> : (i128, i128) -> i128
    %60 = "llvm.mul"(%34, %34) <{overflowFlags = 2 : i32}> : (i128, i128) -> i128
    %61 = "llvm.mul"(%29, %49) <{overflowFlags = 2 : i32}> : (i128, i128) -> i128
    %62 = "llvm.mul"(%31, %40) <{overflowFlags = 2 : i32}> : (i128, i128) -> i128
    %63 = "llvm.add"(%61, %62) <{overflowFlags = 0 : i32}> : (i128, i128) -> i128
    %64 = "llvm.shl"(%63, %5) <{overflowFlags = 0 : i32}> : (i128, i128) -> i128
    %65 = "llvm.add"(%64, %60) <{overflowFlags = 0 : i32}> : (i128, i128) -> i128
    %66 = "llvm.lshr"(%39, %6) : (i128, i128) -> i128
    %67 = "llvm.and"(%66, %7) : (i128, i128) -> i128
    %68 = "llvm.add"(%46, %67) <{overflowFlags = 0 : i32}> : (i128, i128) -> i128
    %69 = "llvm.trunc"(%39) <{overflowFlags = 0 : i32}> : (i128) -> i64
    %70 = "llvm.and"(%69, %8) : (i64, i64) -> i64
    %71 = "llvm.lshr"(%68, %6) : (i128, i128) -> i128
    %72 = "llvm.and"(%71, %7) : (i128, i128) -> i128
    %73 = "llvm.add"(%53, %72) <{overflowFlags = 0 : i32}> : (i128, i128) -> i128
    %74 = "llvm.trunc"(%68) <{overflowFlags = 0 : i32}> : (i128) -> i64
    %75 = "llvm.and"(%74, %8) : (i64, i64) -> i64
    %76 = "llvm.lshr"(%73, %6) : (i128, i128) -> i128
    %77 = "llvm.and"(%76, %7) : (i128, i128) -> i128
    %78 = "llvm.add"(%59, %77) <{overflowFlags = 0 : i32}> : (i128, i128) -> i128
    %79 = "llvm.trunc"(%73) <{overflowFlags = 0 : i32}> : (i128) -> i64
    %80 = "llvm.and"(%79, %8) : (i64, i64) -> i64
    %81 = "llvm.lshr"(%78, %6) : (i128, i128) -> i128
    %82 = "llvm.and"(%81, %7) : (i128, i128) -> i128
    %83 = "llvm.add"(%65, %82) <{overflowFlags = 0 : i32}> : (i128, i128) -> i128
    %84 = "llvm.trunc"(%78) <{overflowFlags = 0 : i32}> : (i128) -> i64
    %85 = "llvm.and"(%84, %8) : (i64, i64) -> i64
    %86 = "llvm.lshr"(%83, %6) : (i128, i128) -> i128
    %87 = "llvm.trunc"(%86) <{overflowFlags = 0 : i32}> : (i128) -> i64
    %88 = "llvm.trunc"(%83) <{overflowFlags = 0 : i32}> : (i128) -> i64
    %89 = "llvm.and"(%88, %8) : (i64, i64) -> i64
    %90 = "llvm.mul"(%87, %4) <{overflowFlags = 0 : i32}> : (i64, i64) -> i64
    %91 = "llvm.add"(%90, %70) <{overflowFlags = 0 : i32}> : (i64, i64) -> i64
    %92 = "llvm.lshr"(%91, %9) : (i64, i64) -> i64
    %93 = "llvm.add"(%92, %75) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %94 = "llvm.and"(%91, %8) : (i64, i64) -> i64
    %95 = "llvm.add"(%26, %10) <{overflowFlags = 0 : i32}> : (i32, i32) -> i32
    %96 = "llvm.icmp"(%95, %11) <{predicate = 0 : i64}> : (i32, i32) -> i1
    "llvm.cond_br"(%96, %89, %85, %80, %93, %94, %95)[^bb2, ^bb1] <{operandSegmentSizes = array<i32: 1, 0, 6>}> : (i1, i64, i64, i64, i64, i64, i32) -> ()
  ^bb2:  // pred: ^bb1
    "llvm.store"(%94, %arg0) <{alignment = 8 : i64, ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    %97 = "llvm.getelementptr"(%arg0, %0) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%93, %97) <{alignment = 8 : i64, ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    %98 = "llvm.getelementptr"(%arg0, %1) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%80, %98) <{alignment = 8 : i64, ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    %99 = "llvm.getelementptr"(%arg0, %2) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%85, %99) <{alignment = 8 : i64, ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    %100 = "llvm.getelementptr"(%arg0, %3) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%89, %100) <{alignment = 8 : i64, ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    "llvm.return"() : () -> ()
}

theorem block_count  : (program ).n = 3 := rfl

end
end Agave.Ed25519.Encoding.Decompress.Execution.Pow2k
