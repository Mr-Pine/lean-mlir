/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
-- build/native/gcc/mlir_canonicalized/avx512/region/fd_r43x6_mul_fast.mlir
module

public import SSA.Projects.SLLVM.Cfg

@[expose] public section

namespace Firedancer.Avx512
open LeanMLIR SLLVM

def fd_r43x6_mul_fast_region : MLIR.AST.Region 0 := [mlir_region|
{
  ^bb0(%arg0: vector<8xi64>, %arg1: vector<8xi64>):
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
    %11 = "llvm.mlir.constant"() <{value = dense<9> : vector<8xi64>}> : () -> vector<8xi64>
    %12 = "llvm.mlir.constant"() <{value = dense<0> : vector<8xi64>}> : () -> vector<8xi64>
    %13 = "llvm.mlir.constant"() <{value = 0 : i64}> : () -> i64
    %14 = "llvm.mlir.poison"() : () -> vector<8xi64>
    %15 = "llvm.mlir.poison"() : () -> i64
    %16 = "llvm.mlir.undef"() : () -> vector<8xi64>
    %17 = "llvm.insertelement"(%16, %15, %10) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %18 = "llvm.insertelement"(%17, %15, %9) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %19 = "llvm.insertelement"(%18, %15, %8) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %20 = "llvm.insertelement"(%19, %15, %7) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %21 = "llvm.insertelement"(%20, %15, %6) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %22 = "llvm.insertelement"(%21, %15, %5) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %23 = "llvm.insertelement"(%22, %15, %4) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %24 = "llvm.insertelement"(%23, %13, %3) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %25 = "llvm.mlir.undef"() : () -> vector<8xi64>
    %26 = "llvm.insertelement"(%25, %15, %10) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %27 = "llvm.insertelement"(%26, %15, %9) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %28 = "llvm.insertelement"(%27, %15, %8) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %29 = "llvm.insertelement"(%28, %15, %7) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %30 = "llvm.insertelement"(%29, %15, %6) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %31 = "llvm.insertelement"(%30, %15, %5) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %32 = "llvm.insertelement"(%31, %13, %4) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %33 = "llvm.insertelement"(%32, %13, %3) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %34 = "llvm.mlir.undef"() : () -> vector<8xi64>
    %35 = "llvm.insertelement"(%34, %15, %10) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %36 = "llvm.insertelement"(%35, %15, %9) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %37 = "llvm.insertelement"(%36, %15, %8) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %38 = "llvm.insertelement"(%37, %15, %7) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %39 = "llvm.insertelement"(%38, %15, %6) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %40 = "llvm.insertelement"(%39, %13, %5) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %41 = "llvm.insertelement"(%40, %13, %4) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %42 = "llvm.insertelement"(%41, %13, %3) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %43 = "llvm.mlir.undef"() : () -> vector<8xi64>
    %44 = "llvm.insertelement"(%43, %13, %10) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %45 = "llvm.insertelement"(%44, %13, %9) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %46 = "llvm.insertelement"(%45, %13, %8) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %47 = "llvm.insertelement"(%46, %15, %7) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %48 = "llvm.insertelement"(%47, %15, %6) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %49 = "llvm.insertelement"(%48, %15, %5) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %50 = "llvm.insertelement"(%49, %15, %4) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %51 = "llvm.insertelement"(%50, %15, %3) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %52 = "llvm.mlir.undef"() : () -> vector<8xi64>
    %53 = "llvm.insertelement"(%52, %15, %10) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %54 = "llvm.insertelement"(%53, %15, %9) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %55 = "llvm.insertelement"(%54, %15, %8) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %56 = "llvm.insertelement"(%55, %15, %7) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %57 = "llvm.insertelement"(%56, %13, %6) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %58 = "llvm.insertelement"(%57, %13, %5) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %59 = "llvm.insertelement"(%58, %13, %4) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %60 = "llvm.insertelement"(%59, %13, %3) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %61 = "llvm.mlir.undef"() : () -> vector<8xi64>
    %62 = "llvm.insertelement"(%61, %13, %10) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %63 = "llvm.insertelement"(%62, %13, %9) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %64 = "llvm.insertelement"(%63, %15, %8) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %65 = "llvm.insertelement"(%64, %15, %7) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %66 = "llvm.insertelement"(%65, %15, %6) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %67 = "llvm.insertelement"(%66, %15, %5) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %68 = "llvm.insertelement"(%67, %15, %4) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %69 = "llvm.insertelement"(%68, %15, %3) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %70 = "llvm.mlir.undef"() : () -> vector<8xi64>
    %71 = "llvm.insertelement"(%70, %15, %10) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %72 = "llvm.insertelement"(%71, %15, %9) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %73 = "llvm.insertelement"(%72, %15, %8) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %74 = "llvm.insertelement"(%73, %13, %7) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %75 = "llvm.insertelement"(%74, %13, %6) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %76 = "llvm.insertelement"(%75, %13, %5) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %77 = "llvm.insertelement"(%76, %13, %4) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %78 = "llvm.insertelement"(%77, %13, %3) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %79 = "llvm.mlir.undef"() : () -> vector<8xi64>
    %80 = "llvm.insertelement"(%79, %13, %10) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %81 = "llvm.insertelement"(%80, %15, %9) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %82 = "llvm.insertelement"(%81, %15, %8) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %83 = "llvm.insertelement"(%82, %15, %7) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %84 = "llvm.insertelement"(%83, %15, %6) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %85 = "llvm.insertelement"(%84, %15, %5) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %86 = "llvm.insertelement"(%85, %15, %4) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %87 = "llvm.insertelement"(%86, %15, %3) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %88 = "llvm.mlir.undef"() : () -> vector<8xi64>
    %89 = "llvm.insertelement"(%88, %15, %10) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %90 = "llvm.insertelement"(%89, %15, %9) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %91 = "llvm.insertelement"(%90, %13, %8) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %92 = "llvm.insertelement"(%91, %13, %7) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %93 = "llvm.insertelement"(%92, %13, %6) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %94 = "llvm.insertelement"(%93, %13, %5) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %95 = "llvm.insertelement"(%94, %13, %4) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %96 = "llvm.insertelement"(%95, %13, %3) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %97 = "llvm.shufflevector"(%arg0, %14) <{mask = array<i32: 0, 0, 0, 0, 0, 0, 0, 0>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %98 = "llvm.shufflevector"(%arg0, %14) <{mask = array<i32: 1, 1, 1, 1, 1, 1, 1, 1>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %99 = "llvm.shufflevector"(%arg0, %14) <{mask = array<i32: 2, 2, 2, 2, 2, 2, 2, 2>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %100 = "llvm.shufflevector"(%arg0, %14) <{mask = array<i32: 3, 3, 3, 3, 3, 3, 3, 3>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %101 = "llvm.shufflevector"(%arg0, %14) <{mask = array<i32: 4, 4, 4, 4, 4, 4, 4, 4>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %102 = "llvm.shufflevector"(%arg0, %14) <{mask = array<i32: 5, 5, 5, 5, 5, 5, 5, 5>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %103 = "x86vector.avx512.intr.vpmadd52l.uq.512"(%12, %97, %arg1) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %104 = "x86vector.avx512.intr.vpmadd52h.uq.512"(%12, %97, %arg1) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %105 = "llvm.shl"(%104, %11) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %106 = "x86vector.avx512.intr.vpmadd52l.uq.512"(%105, %98, %arg1) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %107 = "x86vector.avx512.intr.vpmadd52h.uq.512"(%12, %98, %arg1) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %108 = "llvm.shl"(%107, %11) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %109 = "x86vector.avx512.intr.vpmadd52l.uq.512"(%108, %99, %arg1) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %110 = "x86vector.avx512.intr.vpmadd52h.uq.512"(%12, %99, %arg1) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %111 = "llvm.shl"(%110, %11) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %112 = "x86vector.avx512.intr.vpmadd52l.uq.512"(%111, %100, %arg1) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %113 = "x86vector.avx512.intr.vpmadd52h.uq.512"(%12, %100, %arg1) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %114 = "llvm.shl"(%113, %11) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %115 = "x86vector.avx512.intr.vpmadd52l.uq.512"(%114, %101, %arg1) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %116 = "x86vector.avx512.intr.vpmadd52h.uq.512"(%12, %101, %arg1) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %117 = "llvm.shl"(%116, %11) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %118 = "x86vector.avx512.intr.vpmadd52l.uq.512"(%117, %102, %arg1) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %119 = "x86vector.avx512.intr.vpmadd52h.uq.512"(%12, %102, %arg1) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %120 = "llvm.shl"(%119, %11) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %121 = "llvm.shufflevector"(%24, %106) <{mask = array<i32: 7, 8, 9, 10, 11, 12, 13, 14>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %122 = "llvm.shufflevector"(%33, %109) <{mask = array<i32: 6, 7, 8, 9, 10, 11, 12, 13>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %123 = "llvm.shufflevector"(%42, %112) <{mask = array<i32: 5, 6, 7, 8, 9, 10, 11, 12>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %124 = "llvm.shufflevector"(%112, %51) <{mask = array<i32: 5, 6, 7, 8, 9, 10, -1, -1>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %125 = "llvm.shufflevector"(%60, %115) <{mask = array<i32: 4, 5, 6, 7, 8, 9, 10, 11>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %126 = "llvm.shufflevector"(%115, %69) <{mask = array<i32: 4, 5, 6, 7, 8, 9, -1, -1>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %127 = "llvm.shufflevector"(%78, %118) <{mask = array<i32: 3, 4, 5, 6, 7, 8, 9, 10>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %128 = "llvm.shufflevector"(%118, %87) <{mask = array<i32: 3, 4, 5, 6, 7, 8, -1, -1>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %129 = "llvm.shufflevector"(%96, %120) <{mask = array<i32: 2, 3, 4, 5, 6, 7, 8, 9>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %130 = "llvm.shufflevector"(%120, %14) <{mask = array<i32: 2, 3, 4, 5, 6, 7, -1, -1>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %131 = "llvm.add"(%121, %103) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %132 = "llvm.add"(%131, %122) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %133 = "llvm.add"(%132, %123) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %134 = "llvm.add"(%133, %125) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %135 = "llvm.add"(%134, %127) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %136 = "llvm.add"(%135, %129) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %137 = "llvm.add"(%126, %124) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %138 = "llvm.add"(%137, %128) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %139 = "llvm.add"(%138, %130) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %140 = "llvm.and"(%136, %2) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %141 = "llvm.shufflevector"(%136, %139) <{mask = array<i32: 6, 7, 8, 9, 10, 11, 12, 13>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %142 = "llvm.shl"(%141, %1) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %143 = "llvm.add"(%142, %140) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %144 = "llvm.mul"(%141, %0) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %145 = "llvm.add"(%143, %144) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    "llvm.return"(%145) : (vector<8xi64>) -> ()
}
]

def fd_r43x6_mul_fast := [sllvm_of| fd_r43x6_mul_fast_region]

def fd_r43x6_mul_fast_cfg := Cfg.ofCom (fd_r43x6_mul_fast.castPureToEff .impure)

end Firedancer.Avx512
