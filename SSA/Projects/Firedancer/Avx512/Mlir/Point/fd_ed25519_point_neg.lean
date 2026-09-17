/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
-- build/native/gcc/mlir_canonicalized/avx512/region/fd_ed25519_point_neg.mlir
import SSA.Projects.SLLVM.Cfg

namespace Firedancer.Avx512
open LeanMLIR SLLVM

def fd_ed25519_point_neg_region : MLIR.AST.Region 0 := [mlir_region|
{
  ^bb0(%arg0: !llvm.ptr, %arg1: !llvm.ptr):
    %0 = "llvm.mlir.constant"() <{value = dense<[8796093022207, 8796093022207, 8796093022207, 8796093022207, 1099511627775, 1099511627775, 1099511627775, 1099511627775]> : vector<8xi64>}> : () -> vector<8xi64>
    %1 = "llvm.mlir.constant"() <{value = dense<8796093022207> : vector<8xi64>}> : () -> vector<8xi64>
    %2 = "llvm.mlir.constant"() <{value = 19 : i64}> : () -> i64
    %3 = "llvm.mlir.constant"() <{value = dense<[43, 43, 43, 43, 40, 40, 40, 40]> : vector<8xi64>}> : () -> vector<8xi64>
    %4 = "llvm.mlir.constant"() <{value = dense<43> : vector<8xi64>}> : () -> vector<8xi64>
    %5 = "llvm.mlir.constant"() <{value = 2199023255550 : i64}> : () -> i64
    %6 = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
    %7 = "llvm.mlir.constant"() <{value = 6 : i32}> : () -> i32
    %8 = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
    %9 = "llvm.mlir.constant"() <{value = 4 : i32}> : () -> i32
    %10 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %11 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %12 = "llvm.mlir.constant"() <{value = 17592186044378 : i64}> : () -> i64
    %13 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %14 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %15 = "llvm.mlir.constant"() <{value = 17592186044414 : i64}> : () -> i64
    %16 = "llvm.mlir.poison"() : () -> i64
    %17 = "llvm.mlir.undef"() : () -> vector<8xi64>
    %18 = "llvm.insertelement"(%17, %12, %11) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %19 = "llvm.insertelement"(%18, %16, %13) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %20 = "llvm.insertelement"(%19, %16, %14) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %21 = "llvm.insertelement"(%20, %12, %10) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %22 = "llvm.insertelement"(%21, %15, %9) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %23 = "llvm.insertelement"(%22, %16, %8) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %24 = "llvm.insertelement"(%23, %16, %7) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %25 = "llvm.insertelement"(%24, %15, %6) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %26 = "llvm.mlir.undef"() : () -> vector<8xi64>
    %27 = "llvm.insertelement"(%26, %15, %11) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %28 = "llvm.insertelement"(%27, %16, %13) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %29 = "llvm.insertelement"(%28, %16, %14) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %30 = "llvm.insertelement"(%29, %15, %10) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %31 = "llvm.insertelement"(%30, %15, %9) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %32 = "llvm.insertelement"(%31, %16, %8) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %33 = "llvm.insertelement"(%32, %16, %7) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %34 = "llvm.insertelement"(%33, %15, %6) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %35 = "llvm.mlir.undef"() : () -> vector<8xi64>
    %36 = "llvm.insertelement"(%35, %15, %11) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %37 = "llvm.insertelement"(%36, %16, %13) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %38 = "llvm.insertelement"(%37, %16, %14) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %39 = "llvm.insertelement"(%38, %15, %10) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %40 = "llvm.insertelement"(%39, %5, %9) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %41 = "llvm.insertelement"(%40, %16, %8) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %42 = "llvm.insertelement"(%41, %16, %7) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %43 = "llvm.insertelement"(%42, %5, %6) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %44 = "llvm.mlir.undef"() : () -> vector<8xi64>
    %45 = "llvm.insertelement"(%44, %16, %11) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %46 = "llvm.insertelement"(%45, %16, %13) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %47 = "llvm.insertelement"(%46, %16, %14) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %48 = "llvm.insertelement"(%47, %16, %10) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %49 = "llvm.insertelement"(%48, %2, %9) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %50 = "llvm.insertelement"(%49, %2, %8) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %51 = "llvm.insertelement"(%50, %2, %7) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %52 = "llvm.insertelement"(%51, %2, %6) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %53 = "llvm.load"(%arg1) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %54 = "llvm.getelementptr"(%arg1) <{elem_type = !llvm.struct<"struct.fd_curve25519_edwards", (vector<8xi64>, vector<8xi64>, vector<8xi64>)>, inbounds, rawConstantIndices = array<i32: 0, 1>}> : (!llvm.ptr) -> !llvm.ptr
    %55 = "llvm.load"(%54) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %56 = "llvm.getelementptr"(%arg1) <{elem_type = !llvm.struct<"struct.fd_curve25519_edwards", (vector<8xi64>, vector<8xi64>, vector<8xi64>)>, inbounds, rawConstantIndices = array<i32: 0, 2>}> : (!llvm.ptr) -> !llvm.ptr
    %57 = "llvm.load"(%56) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %58 = "llvm.sub"(%25, %53) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %59 = "llvm.shufflevector"(%58, %53) <{mask = array<i32: 0, 9, 10, 3, 4, 13, 14, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    "llvm.store"(%59, %arg0) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (vector<8xi64>, !llvm.ptr) -> ()
    %60 = "llvm.load"(%54) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %61 = "llvm.sub"(%34, %55) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %62 = "llvm.shufflevector"(%61, %60) <{mask = array<i32: 0, 9, 10, 3, 4, 13, 14, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %63 = "llvm.getelementptr"(%arg0) <{elem_type = !llvm.struct<"struct.fd_curve25519_edwards", (vector<8xi64>, vector<8xi64>, vector<8xi64>)>, inbounds, rawConstantIndices = array<i32: 0, 1>}> : (!llvm.ptr) -> !llvm.ptr
    "llvm.store"(%62, %63) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (vector<8xi64>, !llvm.ptr) -> ()
    %64 = "llvm.load"(%56) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %65 = "llvm.sub"(%43, %57) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %66 = "llvm.shufflevector"(%65, %64) <{mask = array<i32: 0, 9, 10, 3, 4, 13, 14, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %67 = "llvm.getelementptr"(%arg0) <{elem_type = !llvm.struct<"struct.fd_curve25519_edwards", (vector<8xi64>, vector<8xi64>, vector<8xi64>)>, inbounds, rawConstantIndices = array<i32: 0, 2>}> : (!llvm.ptr) -> !llvm.ptr
    %68 = "llvm.lshr"(%59, %4) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %69 = "llvm.lshr"(%62, %4) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %70 = "llvm.lshr"(%66, %3) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %71 = "llvm.mul"(%70, %52) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %72 = "llvm.and"(%59, %1) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %73 = "llvm.shufflevector"(%71, %70) <{mask = array<i32: 4, 5, 6, 7, 8, 9, 10, 11>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %74 = "llvm.add"(%73, %72) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    "llvm.store"(%74, %arg0) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (vector<8xi64>, !llvm.ptr) -> ()
    %75 = "llvm.and"(%62, %1) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %76 = "llvm.add"(%75, %68) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    "llvm.store"(%76, %63) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (vector<8xi64>, !llvm.ptr) -> ()
    %77 = "llvm.and"(%66, %0) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %78 = "llvm.add"(%77, %69) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    "llvm.store"(%78, %67) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (vector<8xi64>, !llvm.ptr) -> ()
    "llvm.return"(%arg0) : (!llvm.ptr) -> ()
}
]

sllvm_cfg_def fd_ed25519_point_neg : Cfg (Ctxt.ofList [SLLVM.Ty.ptr, SLLVM.Ty.ptr]) [SLLVM.Ty.ptr] :=
  [sllvm_cfg_of| fd_ed25519_point_neg_region]

end Firedancer.Avx512
