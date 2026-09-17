/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
-- build/native/gcc/mlir_canonicalized/avx512/region/fd_r43x6_sqr_fast.mlir
module

public import SSA.Projects.SLLVM.Cfg

@[expose] public section

namespace Firedancer.Avx512
open LeanMLIR SLLVM

def fd_r43x6_sqr_fast_region : MLIR.AST.Region 0 := [mlir_region|
{
  ^bb0(%arg0: vector<8xi64>):
    %0 = "llvm.mlir.constant"() <{value = dense<24> : vector<8xi64>}> : () -> vector<8xi64>
    %1 = "llvm.mlir.constant"() <{value = dense<7> : vector<8xi64>}> : () -> vector<8xi64>
    %2 = "llvm.mlir.constant"() <{value = dense<[-1, -1, -1, -1, -1, -1, 0, 0]> : vector<8xi64>}> : () -> vector<8xi64>
    %3 = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
    %4 = "llvm.mlir.constant"() <{value = 6 : i32}> : () -> i32
    %5 = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
    %6 = "llvm.mlir.constant"() <{value = 4 : i32}> : () -> i32
    %7 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %8 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %9 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %10 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %11 = "llvm.mlir.constant"() <{value = -1 : i64}> : () -> i64
    %12 = "llvm.mlir.constant"() <{value = dense<[0, -1, 0, -1, -1, -1, -1, -1]> : vector<8xi64>}> : () -> vector<8xi64>
    %13 = "llvm.mlir.constant"() <{value = dense<[0, 0, -1, -1, -1, -1, -1, -1]> : vector<8xi64>}> : () -> vector<8xi64>
    %14 = "llvm.mlir.constant"() <{value = dense<9> : vector<8xi64>}> : () -> vector<8xi64>
    %15 = "llvm.mlir.constant"() <{value = dense<0> : vector<8xi64>}> : () -> vector<8xi64>
    %16 = "llvm.mlir.constant"() <{value = 0 : i64}> : () -> i64
    %17 = "llvm.mlir.constant"() <{value = dense<[1, 1, 0, 1, 0, 1, 1, 1]> : vector<8xi64>}> : () -> vector<8xi64>
    %18 = "llvm.mlir.constant"() <{value = dense<[0, 1, 0, 1, 1, 1, 1, 1]> : vector<8xi64>}> : () -> vector<8xi64>
    %19 = "llvm.mlir.constant"() <{value = dense<[0, 1, 1, 1, 1, 1, 0, 1]> : vector<8xi64>}> : () -> vector<8xi64>
    %20 = "llvm.mlir.poison"() : () -> vector<8xi64>
    %21 = "llvm.mlir.poison"() : () -> i64
    %22 = "llvm.mlir.undef"() : () -> vector<8xi64>
    %23 = "llvm.insertelement"(%22, %11, %10) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %24 = "llvm.insertelement"(%23, %11, %9) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %25 = "llvm.insertelement"(%24, %16, %8) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %26 = "llvm.insertelement"(%25, %16, %7) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %27 = "llvm.insertelement"(%26, %16, %6) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %28 = "llvm.insertelement"(%27, %16, %5) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %29 = "llvm.insertelement"(%28, %21, %4) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %30 = "llvm.insertelement"(%29, %21, %3) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %31 = "llvm.mlir.undef"() : () -> vector<8xi64>
    %32 = "llvm.insertelement"(%31, %11, %10) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %33 = "llvm.insertelement"(%32, %16, %9) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %34 = "llvm.insertelement"(%33, %11, %8) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %35 = "llvm.insertelement"(%34, %16, %7) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %36 = "llvm.insertelement"(%35, %16, %6) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %37 = "llvm.insertelement"(%36, %16, %5) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %38 = "llvm.insertelement"(%37, %21, %4) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %39 = "llvm.insertelement"(%38, %21, %3) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %40 = "llvm.mlir.undef"() : () -> vector<8xi64>
    %41 = "llvm.insertelement"(%40, %11, %10) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %42 = "llvm.insertelement"(%41, %11, %9) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %43 = "llvm.insertelement"(%42, %16, %8) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %44 = "llvm.insertelement"(%43, %16, %7) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %45 = "llvm.insertelement"(%44, %16, %6) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %46 = "llvm.insertelement"(%45, %21, %5) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %47 = "llvm.insertelement"(%46, %21, %4) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %48 = "llvm.insertelement"(%47, %21, %3) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %49 = "llvm.mlir.undef"() : () -> vector<8xi64>
    %50 = "llvm.insertelement"(%49, %11, %10) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %51 = "llvm.insertelement"(%50, %16, %9) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %52 = "llvm.insertelement"(%51, %11, %8) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %53 = "llvm.insertelement"(%52, %16, %7) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %54 = "llvm.insertelement"(%53, %16, %6) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %55 = "llvm.insertelement"(%54, %21, %5) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %56 = "llvm.insertelement"(%55, %21, %4) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %57 = "llvm.insertelement"(%56, %21, %3) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %58 = "llvm.mlir.undef"() : () -> vector<8xi64>
    %59 = "llvm.insertelement"(%58, %21, %10) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %60 = "llvm.insertelement"(%59, %21, %9) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %61 = "llvm.insertelement"(%60, %21, %8) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %62 = "llvm.insertelement"(%61, %21, %7) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %63 = "llvm.insertelement"(%62, %21, %6) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %64 = "llvm.insertelement"(%63, %21, %5) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %65 = "llvm.insertelement"(%64, %21, %4) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %66 = "llvm.insertelement"(%65, %16, %3) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %67 = "llvm.mlir.undef"() : () -> vector<8xi64>
    %68 = "llvm.insertelement"(%67, %16, %10) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %69 = "llvm.insertelement"(%68, %16, %9) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %70 = "llvm.insertelement"(%69, %16, %8) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %71 = "llvm.insertelement"(%70, %16, %7) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %72 = "llvm.insertelement"(%71, %16, %6) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %73 = "llvm.insertelement"(%72, %21, %5) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %74 = "llvm.insertelement"(%73, %21, %4) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %75 = "llvm.insertelement"(%74, %21, %3) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %76 = "llvm.shufflevector"(%arg0, %20) <{mask = array<i32: 0, 0, 0, 0, 0, 0, 3, 3>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %77 = "llvm.shufflevector"(%arg0, %20) <{mask = array<i32: 0, 1, 2, 3, 4, 5, 3, 4>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %78 = "llvm.shufflevector"(%arg0, %20) <{mask = array<i32: 4, 4, 1, 1, 1, 1, 1, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %79 = "llvm.shufflevector"(%arg0, %20) <{mask = array<i32: 4, 5, 1, 2, 3, 4, 5, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %80 = "llvm.shufflevector"(%arg0, %20) <{mask = array<i32: 3, 7, 5, 7, 2, 2, 2, 2>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %81 = "llvm.shufflevector"(%arg0, %20) <{mask = array<i32: 5, 7, 5, 7, 2, 3, 4, 5>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %82 = "llvm.shl"(%76, %19) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %83 = "llvm.shl"(%78, %18) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %84 = "llvm.shl"(%80, %17) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %85 = "x86vector.avx512.intr.vpmadd52l.uq.512"(%15, %82, %77) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %86 = "x86vector.avx512.intr.vpmadd52l.uq.512"(%15, %83, %79) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %87 = "x86vector.avx512.intr.vpmadd52l.uq.512"(%15, %84, %81) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %88 = "x86vector.avx512.intr.vpmadd52h.uq.512"(%15, %82, %77) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %89 = "llvm.shl"(%88, %14) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %90 = "x86vector.avx512.intr.vpmadd52h.uq.512"(%15, %83, %79) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %91 = "llvm.shl"(%90, %14) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %92 = "x86vector.avx512.intr.vpmadd52h.uq.512"(%15, %84, %81) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %93 = "llvm.shl"(%92, %14) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %94 = "llvm.and"(%86, %13) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %95 = "llvm.and"(%87, %12) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %96 = "llvm.and"(%91, %13) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %97 = "llvm.and"(%93, %12) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %98 = "llvm.add"(%96, %89) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %99 = "llvm.add"(%98, %97) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %100 = "llvm.and"(%86, %30) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %101 = "llvm.and"(%87, %39) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %102 = "llvm.and"(%91, %48) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %103 = "llvm.and"(%93, %57) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %104 = "llvm.add"(%103, %102) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %105 = "llvm.shufflevector"(%66, %99) <{mask = array<i32: 7, 8, 9, 10, 11, 12, 13, 14>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %106 = "llvm.add"(%94, %85) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %107 = "llvm.add"(%106, %95) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %108 = "llvm.add"(%107, %105) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %109 = "llvm.shufflevector"(%66, %104) <{mask = array<i32: 7, 8, 9, 10, 11, 12, -1, -1>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %110 = "llvm.shufflevector"(%99, %75) <{mask = array<i32: 7, 8, 9, 10, 11, 12, -1, -1>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %111 = "llvm.add"(%101, %100) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %112 = "llvm.add"(%111, %109) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %113 = "llvm.add"(%112, %110) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %114 = "llvm.and"(%108, %2) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %115 = "llvm.shufflevector"(%108, %113) <{mask = array<i32: 6, 7, 8, 9, 10, 11, 12, 13>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %116 = "llvm.shl"(%115, %1) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %117 = "llvm.add"(%116, %114) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %118 = "llvm.mul"(%115, %0) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %119 = "llvm.add"(%117, %118) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    "llvm.return"(%119) : (vector<8xi64>) -> ()
}
]

def fd_r43x6_sqr_fast := [sllvm_of| fd_r43x6_sqr_fast_region]

def fd_r43x6_sqr_fast_cfg := Cfg.ofCom (fd_r43x6_sqr_fast.castPureToEff .impure)

end Firedancer.Avx512
