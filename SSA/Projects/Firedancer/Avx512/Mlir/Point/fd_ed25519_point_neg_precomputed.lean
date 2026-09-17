/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
-- build/native/gcc/mlir_canonicalized/avx512/region/fd_ed25519_point_neg_precomputed.mlir
module

public import SSA.Projects.SLLVM.Cfg

@[expose] public section

namespace Firedancer.Avx512
open LeanMLIR SLLVM

def fd_ed25519_point_neg_precomputed_region : MLIR.AST.Region 0 := [mlir_region|
{
  ^bb0(%arg0: !llvm.ptr, %arg1: !llvm.ptr):
    %0 = "llvm.mlir.constant"() <{value = 2199023255550 : i64}> : () -> i64
    %1 = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
    %2 = "llvm.mlir.constant"() <{value = 6 : i32}> : () -> i32
    %3 = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
    %4 = "llvm.mlir.constant"() <{value = 4 : i32}> : () -> i32
    %5 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %6 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %7 = "llvm.mlir.constant"() <{value = 17592186044378 : i64}> : () -> i64
    %8 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %9 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %10 = "llvm.mlir.constant"() <{value = 17592186044414 : i64}> : () -> i64
    %11 = "llvm.mlir.poison"() : () -> i64
    %12 = "llvm.mlir.undef"() : () -> vector<8xi64>
    %13 = "llvm.insertelement"(%12, %11, %6) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %14 = "llvm.insertelement"(%13, %11, %8) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %15 = "llvm.insertelement"(%14, %11, %9) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %16 = "llvm.insertelement"(%15, %7, %5) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %17 = "llvm.insertelement"(%16, %11, %4) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %18 = "llvm.insertelement"(%17, %11, %3) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %19 = "llvm.insertelement"(%18, %11, %2) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %20 = "llvm.insertelement"(%19, %10, %1) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %21 = "llvm.mlir.undef"() : () -> vector<8xi64>
    %22 = "llvm.insertelement"(%21, %11, %6) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %23 = "llvm.insertelement"(%22, %11, %8) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %24 = "llvm.insertelement"(%23, %11, %9) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %25 = "llvm.insertelement"(%24, %10, %5) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %26 = "llvm.insertelement"(%25, %11, %4) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %27 = "llvm.insertelement"(%26, %11, %3) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %28 = "llvm.insertelement"(%27, %11, %2) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %29 = "llvm.insertelement"(%28, %10, %1) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %30 = "llvm.mlir.undef"() : () -> vector<8xi64>
    %31 = "llvm.insertelement"(%30, %11, %6) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %32 = "llvm.insertelement"(%31, %11, %8) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %33 = "llvm.insertelement"(%32, %11, %9) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %34 = "llvm.insertelement"(%33, %10, %5) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %35 = "llvm.insertelement"(%34, %11, %4) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %36 = "llvm.insertelement"(%35, %11, %3) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %37 = "llvm.insertelement"(%36, %11, %2) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %38 = "llvm.insertelement"(%37, %0, %1) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %39 = "llvm.mlir.poison"() : () -> vector<8xi64>
    %40 = "llvm.load"(%arg1) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %41 = "llvm.getelementptr"(%arg1) <{elem_type = !llvm.struct<"struct.fd_curve25519_edwards", (vector<8xi64>, vector<8xi64>, vector<8xi64>)>, inbounds, rawConstantIndices = array<i32: 0, 1>}> : (!llvm.ptr) -> !llvm.ptr
    %42 = "llvm.load"(%41) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %43 = "llvm.getelementptr"(%arg1) <{elem_type = !llvm.struct<"struct.fd_curve25519_edwards", (vector<8xi64>, vector<8xi64>, vector<8xi64>)>, inbounds, rawConstantIndices = array<i32: 0, 2>}> : (!llvm.ptr) -> !llvm.ptr
    %44 = "llvm.load"(%43) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %45 = "llvm.sub"(%20, %40) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %46 = "llvm.shufflevector"(%40, %45) <{mask = array<i32: 0, 1, 2, 11, 4, 5, 6, 15>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    "llvm.store"(%46, %arg0) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (vector<8xi64>, !llvm.ptr) -> ()
    %47 = "llvm.load"(%41) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %48 = "llvm.sub"(%29, %42) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %49 = "llvm.shufflevector"(%47, %48) <{mask = array<i32: 0, 1, 2, 11, 4, 5, 6, 15>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %50 = "llvm.getelementptr"(%arg0) <{elem_type = !llvm.struct<"struct.fd_curve25519_edwards", (vector<8xi64>, vector<8xi64>, vector<8xi64>)>, inbounds, rawConstantIndices = array<i32: 0, 1>}> : (!llvm.ptr) -> !llvm.ptr
    "llvm.store"(%49, %50) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (vector<8xi64>, !llvm.ptr) -> ()
    %51 = "llvm.load"(%43) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %52 = "llvm.sub"(%38, %44) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %53 = "llvm.shufflevector"(%51, %52) <{mask = array<i32: 0, 1, 2, 11, 4, 5, 6, 15>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %54 = "llvm.getelementptr"(%arg0) <{elem_type = !llvm.struct<"struct.fd_curve25519_edwards", (vector<8xi64>, vector<8xi64>, vector<8xi64>)>, inbounds, rawConstantIndices = array<i32: 0, 2>}> : (!llvm.ptr) -> !llvm.ptr
    %55 = "llvm.shufflevector"(%46, %39) <{mask = array<i32: 1, 0, 2, 3, 5, 4, 6, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    "llvm.store"(%55, %arg0) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (vector<8xi64>, !llvm.ptr) -> ()
    %56 = "llvm.shufflevector"(%49, %39) <{mask = array<i32: 1, 0, 2, 3, 5, 4, 6, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    "llvm.store"(%56, %50) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (vector<8xi64>, !llvm.ptr) -> ()
    %57 = "llvm.shufflevector"(%53, %39) <{mask = array<i32: 1, 0, 2, 3, 5, 4, 6, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    "llvm.store"(%57, %54) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (vector<8xi64>, !llvm.ptr) -> ()
    "llvm.return"(%arg0) : (!llvm.ptr) -> ()
}
]

sllvm_cfg_def fd_ed25519_point_neg_precomputed :
    Cfg (Ctxt.ofList [SLLVM.Ty.ptr, SLLVM.Ty.ptr]) [SLLVM.Ty.ptr] :=
  [sllvm_cfg_of| fd_ed25519_point_neg_precomputed_region]

end Firedancer.Avx512
