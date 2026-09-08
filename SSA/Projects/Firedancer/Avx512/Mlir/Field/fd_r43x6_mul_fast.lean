/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.SLLVM.Cfg

/-!
# `fd_r43x6_mul_fast`, lifted from Firedancer's AVX-512 ed25519 implementation

The program below is the MLIR translation of `fd_r43x6_mul_fast` from
`firedancer/src/ballet/ed25519/avx512/fd_r43x6.h`, taken verbatim from the
build artifact `build/native/gcc/mlir/avx512/region/fd_r43x6_mul_fast.mlir`.
-/

namespace Firedancer.Avx512
open LeanMLIR SLLVM

/-- The region as an AST value, so that a multi-block caller -- which binds
its callees by region, not by `Com` -- can inline it. -/
def fd_r43x6_mul_fast_region : MLIR.AST.Region 0 := [mlir_region|
{
  ^bb0(%arg0: vector<8xi64>, %arg1: vector<8xi64>):
    %0 = "llvm.mlir.poison"() : () -> vector<8xi64>
    %1 = "llvm.mlir.constant"() <{value = 0 : i64}> : () -> i64
    %2 = "llvm.mlir.constant"() <{value = dense<0> : vector<8xi64>}> : () -> vector<8xi64>
    %3 = "llvm.mlir.constant"() <{value = dense<9> : vector<8xi64>}> : () -> vector<8xi64>
    %4 = "llvm.mlir.poison"() : () -> i64
    %5 = "llvm.mlir.undef"() : () -> vector<8xi64>
    %6 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %7 = "llvm.insertelement"(%5, %4, %6) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %8 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %9 = "llvm.insertelement"(%7, %4, %8) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %10 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %11 = "llvm.insertelement"(%9, %4, %10) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %12 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %13 = "llvm.insertelement"(%11, %4, %12) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %14 = "llvm.mlir.constant"() <{value = 4 : i32}> : () -> i32
    %15 = "llvm.insertelement"(%13, %4, %14) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %16 = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
    %17 = "llvm.insertelement"(%15, %4, %16) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %18 = "llvm.mlir.constant"() <{value = 6 : i32}> : () -> i32
    %19 = "llvm.insertelement"(%17, %4, %18) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %20 = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
    %21 = "llvm.insertelement"(%19, %1, %20) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %22 = "llvm.mlir.undef"() : () -> vector<8xi64>
    %23 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %24 = "llvm.insertelement"(%22, %4, %23) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %25 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %26 = "llvm.insertelement"(%24, %4, %25) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %27 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %28 = "llvm.insertelement"(%26, %4, %27) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %29 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %30 = "llvm.insertelement"(%28, %4, %29) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %31 = "llvm.mlir.constant"() <{value = 4 : i32}> : () -> i32
    %32 = "llvm.insertelement"(%30, %4, %31) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %33 = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
    %34 = "llvm.insertelement"(%32, %4, %33) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %35 = "llvm.mlir.constant"() <{value = 6 : i32}> : () -> i32
    %36 = "llvm.insertelement"(%34, %1, %35) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %37 = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
    %38 = "llvm.insertelement"(%36, %1, %37) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %39 = "llvm.mlir.undef"() : () -> vector<8xi64>
    %40 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %41 = "llvm.insertelement"(%39, %4, %40) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %42 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %43 = "llvm.insertelement"(%41, %4, %42) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %44 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %45 = "llvm.insertelement"(%43, %4, %44) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %46 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %47 = "llvm.insertelement"(%45, %4, %46) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %48 = "llvm.mlir.constant"() <{value = 4 : i32}> : () -> i32
    %49 = "llvm.insertelement"(%47, %4, %48) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %50 = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
    %51 = "llvm.insertelement"(%49, %1, %50) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %52 = "llvm.mlir.constant"() <{value = 6 : i32}> : () -> i32
    %53 = "llvm.insertelement"(%51, %1, %52) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %54 = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
    %55 = "llvm.insertelement"(%53, %1, %54) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %56 = "llvm.mlir.undef"() : () -> vector<8xi64>
    %57 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %58 = "llvm.insertelement"(%56, %1, %57) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %59 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %60 = "llvm.insertelement"(%58, %1, %59) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %61 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %62 = "llvm.insertelement"(%60, %1, %61) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %63 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %64 = "llvm.insertelement"(%62, %4, %63) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %65 = "llvm.mlir.constant"() <{value = 4 : i32}> : () -> i32
    %66 = "llvm.insertelement"(%64, %4, %65) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %67 = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
    %68 = "llvm.insertelement"(%66, %4, %67) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %69 = "llvm.mlir.constant"() <{value = 6 : i32}> : () -> i32
    %70 = "llvm.insertelement"(%68, %4, %69) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %71 = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
    %72 = "llvm.insertelement"(%70, %4, %71) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %73 = "llvm.mlir.undef"() : () -> vector<8xi64>
    %74 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %75 = "llvm.insertelement"(%73, %4, %74) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %76 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %77 = "llvm.insertelement"(%75, %4, %76) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %78 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %79 = "llvm.insertelement"(%77, %4, %78) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %80 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %81 = "llvm.insertelement"(%79, %4, %80) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %82 = "llvm.mlir.constant"() <{value = 4 : i32}> : () -> i32
    %83 = "llvm.insertelement"(%81, %1, %82) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %84 = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
    %85 = "llvm.insertelement"(%83, %1, %84) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %86 = "llvm.mlir.constant"() <{value = 6 : i32}> : () -> i32
    %87 = "llvm.insertelement"(%85, %1, %86) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %88 = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
    %89 = "llvm.insertelement"(%87, %1, %88) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %90 = "llvm.mlir.undef"() : () -> vector<8xi64>
    %91 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %92 = "llvm.insertelement"(%90, %1, %91) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %93 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %94 = "llvm.insertelement"(%92, %1, %93) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %95 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %96 = "llvm.insertelement"(%94, %4, %95) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %97 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %98 = "llvm.insertelement"(%96, %4, %97) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %99 = "llvm.mlir.constant"() <{value = 4 : i32}> : () -> i32
    %100 = "llvm.insertelement"(%98, %4, %99) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %101 = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
    %102 = "llvm.insertelement"(%100, %4, %101) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %103 = "llvm.mlir.constant"() <{value = 6 : i32}> : () -> i32
    %104 = "llvm.insertelement"(%102, %4, %103) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %105 = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
    %106 = "llvm.insertelement"(%104, %4, %105) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %107 = "llvm.mlir.undef"() : () -> vector<8xi64>
    %108 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %109 = "llvm.insertelement"(%107, %4, %108) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %110 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %111 = "llvm.insertelement"(%109, %4, %110) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %112 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %113 = "llvm.insertelement"(%111, %4, %112) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %114 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %115 = "llvm.insertelement"(%113, %1, %114) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %116 = "llvm.mlir.constant"() <{value = 4 : i32}> : () -> i32
    %117 = "llvm.insertelement"(%115, %1, %116) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %118 = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
    %119 = "llvm.insertelement"(%117, %1, %118) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %120 = "llvm.mlir.constant"() <{value = 6 : i32}> : () -> i32
    %121 = "llvm.insertelement"(%119, %1, %120) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %122 = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
    %123 = "llvm.insertelement"(%121, %1, %122) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %124 = "llvm.mlir.undef"() : () -> vector<8xi64>
    %125 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %126 = "llvm.insertelement"(%124, %1, %125) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %127 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %128 = "llvm.insertelement"(%126, %4, %127) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %129 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %130 = "llvm.insertelement"(%128, %4, %129) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %131 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %132 = "llvm.insertelement"(%130, %4, %131) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %133 = "llvm.mlir.constant"() <{value = 4 : i32}> : () -> i32
    %134 = "llvm.insertelement"(%132, %4, %133) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %135 = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
    %136 = "llvm.insertelement"(%134, %4, %135) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %137 = "llvm.mlir.constant"() <{value = 6 : i32}> : () -> i32
    %138 = "llvm.insertelement"(%136, %4, %137) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %139 = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
    %140 = "llvm.insertelement"(%138, %4, %139) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %141 = "llvm.mlir.undef"() : () -> vector<8xi64>
    %142 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %143 = "llvm.insertelement"(%141, %4, %142) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %144 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %145 = "llvm.insertelement"(%143, %4, %144) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %146 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %147 = "llvm.insertelement"(%145, %1, %146) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %148 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %149 = "llvm.insertelement"(%147, %1, %148) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %150 = "llvm.mlir.constant"() <{value = 4 : i32}> : () -> i32
    %151 = "llvm.insertelement"(%149, %1, %150) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %152 = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
    %153 = "llvm.insertelement"(%151, %1, %152) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %154 = "llvm.mlir.constant"() <{value = 6 : i32}> : () -> i32
    %155 = "llvm.insertelement"(%153, %1, %154) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %156 = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
    %157 = "llvm.insertelement"(%155, %1, %156) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %158 = "llvm.mlir.constant"() <{value = dense<[-1, -1, -1, -1, -1, -1, 0, 0]> : vector<8xi64>}> : () -> vector<8xi64>
    %159 = "llvm.mlir.constant"() <{value = dense<7> : vector<8xi64>}> : () -> vector<8xi64>
    %160 = "llvm.mlir.constant"() <{value = dense<24> : vector<8xi64>}> : () -> vector<8xi64>
    %161 = "llvm.shufflevector"(%arg0, %0) <{mask = array<i32: 0, 0, 0, 0, 0, 0, 0, 0>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %162 = "llvm.shufflevector"(%arg0, %0) <{mask = array<i32: 1, 1, 1, 1, 1, 1, 1, 1>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %163 = "llvm.shufflevector"(%arg0, %0) <{mask = array<i32: 2, 2, 2, 2, 2, 2, 2, 2>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %164 = "llvm.shufflevector"(%arg0, %0) <{mask = array<i32: 3, 3, 3, 3, 3, 3, 3, 3>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %165 = "llvm.shufflevector"(%arg0, %0) <{mask = array<i32: 4, 4, 4, 4, 4, 4, 4, 4>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %166 = "llvm.shufflevector"(%arg0, %0) <{mask = array<i32: 5, 5, 5, 5, 5, 5, 5, 5>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %167 = "x86vector.avx512.intr.vpmadd52l.uq.512"(%2, %161, %arg1) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %168 = "x86vector.avx512.intr.vpmadd52h.uq.512"(%2, %161, %arg1) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %169 = "llvm.shl"(%168, %3) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %170 = "x86vector.avx512.intr.vpmadd52l.uq.512"(%169, %162, %arg1) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %171 = "x86vector.avx512.intr.vpmadd52h.uq.512"(%2, %162, %arg1) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %172 = "llvm.shl"(%171, %3) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %173 = "x86vector.avx512.intr.vpmadd52l.uq.512"(%172, %163, %arg1) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %174 = "x86vector.avx512.intr.vpmadd52h.uq.512"(%2, %163, %arg1) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %175 = "llvm.shl"(%174, %3) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %176 = "x86vector.avx512.intr.vpmadd52l.uq.512"(%175, %164, %arg1) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %177 = "x86vector.avx512.intr.vpmadd52h.uq.512"(%2, %164, %arg1) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %178 = "llvm.shl"(%177, %3) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %179 = "x86vector.avx512.intr.vpmadd52l.uq.512"(%178, %165, %arg1) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %180 = "x86vector.avx512.intr.vpmadd52h.uq.512"(%2, %165, %arg1) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %181 = "llvm.shl"(%180, %3) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %182 = "x86vector.avx512.intr.vpmadd52l.uq.512"(%181, %166, %arg1) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %183 = "x86vector.avx512.intr.vpmadd52h.uq.512"(%2, %166, %arg1) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %184 = "llvm.shl"(%183, %3) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %185 = "llvm.shufflevector"(%21, %170) <{mask = array<i32: 7, 8, 9, 10, 11, 12, 13, 14>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %186 = "llvm.shufflevector"(%38, %173) <{mask = array<i32: 6, 7, 8, 9, 10, 11, 12, 13>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %187 = "llvm.shufflevector"(%55, %176) <{mask = array<i32: 5, 6, 7, 8, 9, 10, 11, 12>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %188 = "llvm.shufflevector"(%176, %72) <{mask = array<i32: 5, 6, 7, 8, 9, 10, -1, -1>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %189 = "llvm.shufflevector"(%89, %179) <{mask = array<i32: 4, 5, 6, 7, 8, 9, 10, 11>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %190 = "llvm.shufflevector"(%179, %106) <{mask = array<i32: 4, 5, 6, 7, 8, 9, -1, -1>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %191 = "llvm.shufflevector"(%123, %182) <{mask = array<i32: 3, 4, 5, 6, 7, 8, 9, 10>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %192 = "llvm.shufflevector"(%182, %140) <{mask = array<i32: 3, 4, 5, 6, 7, 8, -1, -1>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %193 = "llvm.shufflevector"(%157, %184) <{mask = array<i32: 2, 3, 4, 5, 6, 7, 8, 9>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %194 = "llvm.shufflevector"(%184, %0) <{mask = array<i32: 2, 3, 4, 5, 6, 7, -1, -1>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %195 = "llvm.add"(%185, %167) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %196 = "llvm.add"(%195, %186) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %197 = "llvm.add"(%196, %187) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %198 = "llvm.add"(%197, %189) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %199 = "llvm.add"(%198, %191) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %200 = "llvm.add"(%199, %193) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %201 = "llvm.add"(%190, %188) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %202 = "llvm.add"(%201, %192) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %203 = "llvm.add"(%202, %194) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %204 = "llvm.and"(%200, %158) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %205 = "llvm.shufflevector"(%200, %203) <{mask = array<i32: 6, 7, 8, 9, 10, 11, 12, 13>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %206 = "llvm.shl"(%205, %159) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %207 = "llvm.add"(%206, %204) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %208 = "llvm.mul"(%205, %160) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %209 = "llvm.add"(%207, %208) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    "llvm.return"(%209) : (vector<8xi64>) -> ()
}
]

def fd_r43x6_mul_fast := [sllvm_of| fd_r43x6_mul_fast_region]

/-- The kernel as a `Cfg`, for callers that embed it *by reference*: the call
node then holds `fd_r43x6_mul_fast_cfg.entry`/`.blocks` rather than the
whole body inlined, and `Cfg.denote_mk_self` lets its denotation theorem apply
syntactically. -/
def fd_r43x6_mul_fast_cfg := Cfg.ofCom (fd_r43x6_mul_fast.castPureToEff .impure)

end Firedancer.Avx512
