/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.SLLVM.Cfg

/-!
# `fd_ed25519_point_neg` (AVX-512)

Byte-identical (modulo indentation) to
`build/native/gcc/mlir/avx512/region/fd_ed25519_point_neg.mlir`.
`FD_R43X6_QUAD_LANE_SUB_FAST` with `p + (p - a)` folded to `2p - a` on the `X`
and `T` lanes (`%85`-`%93`), then `FD_R43X6_QUAD_FOLD_UNSIGNED` (`%95`-`%105`).
-/

namespace Firedancer.Avx512
open LeanMLIR SLLVM

def fd_ed25519_point_neg_region : MLIR.AST.Region 0 := [mlir_region|
{
  ^bb0(%arg0: !llvm.ptr, %arg1: !llvm.ptr):
    %0 = "llvm.mlir.constant"() <{value = 0 : i64}> : () -> i64
    %1 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %2 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %3 = "llvm.mlir.constant"() <{value = 17592186044414 : i64}> : () -> i64
    %4 = "llvm.mlir.poison"() : () -> i64
    %5 = "llvm.mlir.constant"() <{value = 17592186044378 : i64}> : () -> i64
    %6 = "llvm.mlir.undef"() : () -> vector<8xi64>
    %7 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %8 = "llvm.insertelement"(%6, %5, %7) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %9 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %10 = "llvm.insertelement"(%8, %4, %9) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %11 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %12 = "llvm.insertelement"(%10, %4, %11) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %13 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %14 = "llvm.insertelement"(%12, %5, %13) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %15 = "llvm.mlir.constant"() <{value = 4 : i32}> : () -> i32
    %16 = "llvm.insertelement"(%14, %3, %15) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %17 = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
    %18 = "llvm.insertelement"(%16, %4, %17) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %19 = "llvm.mlir.constant"() <{value = 6 : i32}> : () -> i32
    %20 = "llvm.insertelement"(%18, %4, %19) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %21 = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
    %22 = "llvm.insertelement"(%20, %3, %21) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %23 = "llvm.mlir.undef"() : () -> vector<8xi64>
    %24 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %25 = "llvm.insertelement"(%23, %3, %24) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %26 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %27 = "llvm.insertelement"(%25, %4, %26) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %28 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %29 = "llvm.insertelement"(%27, %4, %28) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %30 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %31 = "llvm.insertelement"(%29, %3, %30) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %32 = "llvm.mlir.constant"() <{value = 4 : i32}> : () -> i32
    %33 = "llvm.insertelement"(%31, %3, %32) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %34 = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
    %35 = "llvm.insertelement"(%33, %4, %34) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %36 = "llvm.mlir.constant"() <{value = 6 : i32}> : () -> i32
    %37 = "llvm.insertelement"(%35, %4, %36) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %38 = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
    %39 = "llvm.insertelement"(%37, %3, %38) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %40 = "llvm.mlir.constant"() <{value = 2199023255550 : i64}> : () -> i64
    %41 = "llvm.mlir.undef"() : () -> vector<8xi64>
    %42 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %43 = "llvm.insertelement"(%41, %3, %42) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %44 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %45 = "llvm.insertelement"(%43, %4, %44) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %46 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %47 = "llvm.insertelement"(%45, %4, %46) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %48 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %49 = "llvm.insertelement"(%47, %3, %48) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %50 = "llvm.mlir.constant"() <{value = 4 : i32}> : () -> i32
    %51 = "llvm.insertelement"(%49, %40, %50) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %52 = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
    %53 = "llvm.insertelement"(%51, %4, %52) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %54 = "llvm.mlir.constant"() <{value = 6 : i32}> : () -> i32
    %55 = "llvm.insertelement"(%53, %4, %54) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %56 = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
    %57 = "llvm.insertelement"(%55, %40, %56) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %58 = "llvm.mlir.constant"() <{value = dense<43> : vector<8xi64>}> : () -> vector<8xi64>
    %59 = "llvm.mlir.constant"() <{value = dense<[43, 43, 43, 43, 40, 40, 40, 40]> : vector<8xi64>}> : () -> vector<8xi64>
    %60 = "llvm.mlir.constant"() <{value = 19 : i64}> : () -> i64
    %61 = "llvm.mlir.undef"() : () -> vector<8xi64>
    %62 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %63 = "llvm.insertelement"(%61, %4, %62) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %64 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %65 = "llvm.insertelement"(%63, %4, %64) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %66 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %67 = "llvm.insertelement"(%65, %4, %66) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %68 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %69 = "llvm.insertelement"(%67, %4, %68) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %70 = "llvm.mlir.constant"() <{value = 4 : i32}> : () -> i32
    %71 = "llvm.insertelement"(%69, %60, %70) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %72 = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
    %73 = "llvm.insertelement"(%71, %60, %72) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %74 = "llvm.mlir.constant"() <{value = 6 : i32}> : () -> i32
    %75 = "llvm.insertelement"(%73, %60, %74) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %76 = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
    %77 = "llvm.insertelement"(%75, %60, %76) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %78 = "llvm.mlir.constant"() <{value = dense<8796093022207> : vector<8xi64>}> : () -> vector<8xi64>
    %79 = "llvm.mlir.constant"() <{value = dense<[8796093022207, 8796093022207, 8796093022207, 8796093022207, 1099511627775, 1099511627775, 1099511627775, 1099511627775]> : vector<8xi64>}> : () -> vector<8xi64>
    %80 = "llvm.load"(%arg1) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %81 = "llvm.getelementptr"(%arg1, %0) <{elem_type = !llvm.struct<"struct.fd_curve25519_edwards", (vector<8xi64>, vector<8xi64>, vector<8xi64>)>, inbounds, rawConstantIndices = array<i32: -2147483648, 1>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %82 = "llvm.load"(%81) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %83 = "llvm.getelementptr"(%arg1, %0) <{elem_type = !llvm.struct<"struct.fd_curve25519_edwards", (vector<8xi64>, vector<8xi64>, vector<8xi64>)>, inbounds, rawConstantIndices = array<i32: -2147483648, 2>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %84 = "llvm.load"(%83) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %85 = "llvm.sub"(%22, %80) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %86 = "llvm.shufflevector"(%85, %80) <{mask = array<i32: 0, 9, 10, 3, 4, 13, 14, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    "llvm.store"(%86, %arg0) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (vector<8xi64>, !llvm.ptr) -> ()
    %87 = "llvm.load"(%81) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %88 = "llvm.sub"(%39, %82) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %89 = "llvm.shufflevector"(%88, %87) <{mask = array<i32: 0, 9, 10, 3, 4, 13, 14, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %90 = "llvm.getelementptr"(%arg0, %0) <{elem_type = !llvm.struct<"struct.fd_curve25519_edwards", (vector<8xi64>, vector<8xi64>, vector<8xi64>)>, inbounds, rawConstantIndices = array<i32: -2147483648, 1>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%89, %90) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (vector<8xi64>, !llvm.ptr) -> ()
    %91 = "llvm.load"(%83) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %92 = "llvm.sub"(%57, %84) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %93 = "llvm.shufflevector"(%92, %91) <{mask = array<i32: 0, 9, 10, 3, 4, 13, 14, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %94 = "llvm.getelementptr"(%arg0, %0) <{elem_type = !llvm.struct<"struct.fd_curve25519_edwards", (vector<8xi64>, vector<8xi64>, vector<8xi64>)>, inbounds, rawConstantIndices = array<i32: -2147483648, 2>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %95 = "llvm.lshr"(%86, %58) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %96 = "llvm.lshr"(%89, %58) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %97 = "llvm.lshr"(%93, %59) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %98 = "llvm.mul"(%97, %77) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %99 = "llvm.and"(%86, %78) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %100 = "llvm.shufflevector"(%98, %97) <{mask = array<i32: 4, 5, 6, 7, 8, 9, 10, 11>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %101 = "llvm.add"(%100, %99) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    "llvm.store"(%101, %arg0) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (vector<8xi64>, !llvm.ptr) -> ()
    %102 = "llvm.and"(%89, %78) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %103 = "llvm.add"(%102, %95) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    "llvm.store"(%103, %90) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (vector<8xi64>, !llvm.ptr) -> ()
    %104 = "llvm.and"(%93, %79) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %105 = "llvm.add"(%104, %96) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    "llvm.store"(%105, %94) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (vector<8xi64>, !llvm.ptr) -> ()
    "llvm.return"(%arg0) : (!llvm.ptr) -> ()
}
]

def fd_ed25519_point_neg : Cfg (Ctxt.ofList [SLLVM.Ty.ptr, SLLVM.Ty.ptr]) [SLLVM.Ty.ptr] :=
  [sllvm_cfg_of| fd_ed25519_point_neg_region]

end Firedancer.Avx512
