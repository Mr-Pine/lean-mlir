/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.SLLVM.Cfg

namespace Firedancer.Avx512
open LeanMLIR SLLVM

def fd_ed25519_point_neg_precomputed_region : MLIR.AST.Region 0 := [mlir_region|
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
    %8 = "llvm.insertelement"(%6, %4, %7) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %9 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %10 = "llvm.insertelement"(%8, %4, %9) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %11 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %12 = "llvm.insertelement"(%10, %4, %11) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %13 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %14 = "llvm.insertelement"(%12, %5, %13) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %15 = "llvm.mlir.constant"() <{value = 4 : i32}> : () -> i32
    %16 = "llvm.insertelement"(%14, %4, %15) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %17 = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
    %18 = "llvm.insertelement"(%16, %4, %17) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %19 = "llvm.mlir.constant"() <{value = 6 : i32}> : () -> i32
    %20 = "llvm.insertelement"(%18, %4, %19) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %21 = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
    %22 = "llvm.insertelement"(%20, %3, %21) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %23 = "llvm.mlir.undef"() : () -> vector<8xi64>
    %24 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %25 = "llvm.insertelement"(%23, %4, %24) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %26 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %27 = "llvm.insertelement"(%25, %4, %26) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %28 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %29 = "llvm.insertelement"(%27, %4, %28) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %30 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %31 = "llvm.insertelement"(%29, %3, %30) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %32 = "llvm.mlir.constant"() <{value = 4 : i32}> : () -> i32
    %33 = "llvm.insertelement"(%31, %4, %32) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %34 = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
    %35 = "llvm.insertelement"(%33, %4, %34) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %36 = "llvm.mlir.constant"() <{value = 6 : i32}> : () -> i32
    %37 = "llvm.insertelement"(%35, %4, %36) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %38 = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
    %39 = "llvm.insertelement"(%37, %3, %38) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %40 = "llvm.mlir.constant"() <{value = 2199023255550 : i64}> : () -> i64
    %41 = "llvm.mlir.undef"() : () -> vector<8xi64>
    %42 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %43 = "llvm.insertelement"(%41, %4, %42) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %44 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %45 = "llvm.insertelement"(%43, %4, %44) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %46 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %47 = "llvm.insertelement"(%45, %4, %46) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %48 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %49 = "llvm.insertelement"(%47, %3, %48) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %50 = "llvm.mlir.constant"() <{value = 4 : i32}> : () -> i32
    %51 = "llvm.insertelement"(%49, %4, %50) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %52 = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
    %53 = "llvm.insertelement"(%51, %4, %52) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %54 = "llvm.mlir.constant"() <{value = 6 : i32}> : () -> i32
    %55 = "llvm.insertelement"(%53, %4, %54) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %56 = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
    %57 = "llvm.insertelement"(%55, %40, %56) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %58 = "llvm.mlir.poison"() : () -> vector<8xi64>
    %59 = "llvm.load"(%arg1) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %60 = "llvm.getelementptr"(%arg1, %0) <{elem_type = !llvm.struct<"struct.fd_curve25519_edwards", (vector<8xi64>, vector<8xi64>, vector<8xi64>)>, inbounds, rawConstantIndices = array<i32: -2147483648, 1>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %61 = "llvm.load"(%60) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %62 = "llvm.getelementptr"(%arg1, %0) <{elem_type = !llvm.struct<"struct.fd_curve25519_edwards", (vector<8xi64>, vector<8xi64>, vector<8xi64>)>, inbounds, rawConstantIndices = array<i32: -2147483648, 2>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %63 = "llvm.load"(%62) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %64 = "llvm.sub"(%22, %59) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %65 = "llvm.shufflevector"(%59, %64) <{mask = array<i32: 0, 1, 2, 11, 4, 5, 6, 15>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    "llvm.store"(%65, %arg0) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (vector<8xi64>, !llvm.ptr) -> ()
    %66 = "llvm.load"(%60) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %67 = "llvm.sub"(%39, %61) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %68 = "llvm.shufflevector"(%66, %67) <{mask = array<i32: 0, 1, 2, 11, 4, 5, 6, 15>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %69 = "llvm.getelementptr"(%arg0, %0) <{elem_type = !llvm.struct<"struct.fd_curve25519_edwards", (vector<8xi64>, vector<8xi64>, vector<8xi64>)>, inbounds, rawConstantIndices = array<i32: -2147483648, 1>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%68, %69) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (vector<8xi64>, !llvm.ptr) -> ()
    %70 = "llvm.load"(%62) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %71 = "llvm.sub"(%57, %63) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %72 = "llvm.shufflevector"(%70, %71) <{mask = array<i32: 0, 1, 2, 11, 4, 5, 6, 15>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %73 = "llvm.getelementptr"(%arg0, %0) <{elem_type = !llvm.struct<"struct.fd_curve25519_edwards", (vector<8xi64>, vector<8xi64>, vector<8xi64>)>, inbounds, rawConstantIndices = array<i32: -2147483648, 2>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %74 = "llvm.shufflevector"(%65, %58) <{mask = array<i32: 1, 0, 2, 3, 5, 4, 6, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    "llvm.store"(%74, %arg0) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (vector<8xi64>, !llvm.ptr) -> ()
    %75 = "llvm.shufflevector"(%68, %58) <{mask = array<i32: 1, 0, 2, 3, 5, 4, 6, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    "llvm.store"(%75, %69) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (vector<8xi64>, !llvm.ptr) -> ()
    %76 = "llvm.shufflevector"(%72, %58) <{mask = array<i32: 1, 0, 2, 3, 5, 4, 6, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    "llvm.store"(%76, %73) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (vector<8xi64>, !llvm.ptr) -> ()
    "llvm.return"(%arg0) : (!llvm.ptr) -> ()
}
]

def fd_ed25519_point_neg_precomputed :
    Cfg (Ctxt.ofList [SLLVM.Ty.ptr, SLLVM.Ty.ptr]) [SLLVM.Ty.ptr] :=
  [sllvm_cfg_of| fd_ed25519_point_neg_precomputed_region]

end Firedancer.Avx512
