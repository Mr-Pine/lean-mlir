/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.SLLVM.Dialect

/-!
# `fd_r43x6_sqr_fast`, lifted from Firedancer's AVX-512 ed25519 implementation

The program below is the MLIR translation of `fd_r43x6_sqr_fast` from
`firedancer/src/ballet/ed25519/avx512/fd_r43x6.h`, taken verbatim from the
build artifact `build/native/gcc/mlir/avx512/region/fd_r43x6_sqr_fast.mlir`.
-/

namespace Firedancer.Avx512
open LeanMLIR SLLVM

def fd_r43x6_sqr_fast := [sllvm|
{
  ^bb0(%arg0: vector<8xi64>):
    %0 = "llvm.mlir.poison"() : () -> vector<8xi64>
    %1 = "llvm.mlir.constant"() <{value = dense<[0, 1, 1, 1, 1, 1, 0, 1]> : vector<8xi64>}> : () -> vector<8xi64>
    %2 = "llvm.mlir.constant"() <{value = dense<[0, 1, 0, 1, 1, 1, 1, 1]> : vector<8xi64>}> : () -> vector<8xi64>
    %3 = "llvm.mlir.constant"() <{value = dense<[1, 1, 0, 1, 0, 1, 1, 1]> : vector<8xi64>}> : () -> vector<8xi64>
    %4 = "llvm.mlir.constant"() <{value = 0 : i64}> : () -> i64
    %5 = "llvm.mlir.constant"() <{value = dense<0> : vector<8xi64>}> : () -> vector<8xi64>
    %6 = "llvm.mlir.constant"() <{value = dense<9> : vector<8xi64>}> : () -> vector<8xi64>
    %7 = "llvm.mlir.constant"() <{value = dense<[0, 0, -1, -1, -1, -1, -1, -1]> : vector<8xi64>}> : () -> vector<8xi64>
    %8 = "llvm.mlir.constant"() <{value = dense<[0, -1, 0, -1, -1, -1, -1, -1]> : vector<8xi64>}> : () -> vector<8xi64>
    %9 = "llvm.mlir.poison"() : () -> i64
    %10 = "llvm.mlir.constant"() <{value = -1 : i64}> : () -> i64
    %11 = "llvm.mlir.undef"() : () -> vector<8xi64>
    %12 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %13 = "llvm.insertelement"(%11, %10, %12) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %14 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %15 = "llvm.insertelement"(%13, %10, %14) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %16 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %17 = "llvm.insertelement"(%15, %4, %16) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %18 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %19 = "llvm.insertelement"(%17, %4, %18) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %20 = "llvm.mlir.constant"() <{value = 4 : i32}> : () -> i32
    %21 = "llvm.insertelement"(%19, %4, %20) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %22 = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
    %23 = "llvm.insertelement"(%21, %4, %22) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %24 = "llvm.mlir.constant"() <{value = 6 : i32}> : () -> i32
    %25 = "llvm.insertelement"(%23, %9, %24) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %26 = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
    %27 = "llvm.insertelement"(%25, %9, %26) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %28 = "llvm.mlir.undef"() : () -> vector<8xi64>
    %29 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %30 = "llvm.insertelement"(%28, %10, %29) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %31 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %32 = "llvm.insertelement"(%30, %4, %31) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %33 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %34 = "llvm.insertelement"(%32, %10, %33) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %35 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %36 = "llvm.insertelement"(%34, %4, %35) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %37 = "llvm.mlir.constant"() <{value = 4 : i32}> : () -> i32
    %38 = "llvm.insertelement"(%36, %4, %37) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %39 = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
    %40 = "llvm.insertelement"(%38, %4, %39) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %41 = "llvm.mlir.constant"() <{value = 6 : i32}> : () -> i32
    %42 = "llvm.insertelement"(%40, %9, %41) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %43 = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
    %44 = "llvm.insertelement"(%42, %9, %43) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %45 = "llvm.mlir.undef"() : () -> vector<8xi64>
    %46 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %47 = "llvm.insertelement"(%45, %10, %46) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %48 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %49 = "llvm.insertelement"(%47, %10, %48) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %50 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %51 = "llvm.insertelement"(%49, %4, %50) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %52 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %53 = "llvm.insertelement"(%51, %4, %52) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %54 = "llvm.mlir.constant"() <{value = 4 : i32}> : () -> i32
    %55 = "llvm.insertelement"(%53, %4, %54) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %56 = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
    %57 = "llvm.insertelement"(%55, %9, %56) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %58 = "llvm.mlir.constant"() <{value = 6 : i32}> : () -> i32
    %59 = "llvm.insertelement"(%57, %9, %58) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %60 = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
    %61 = "llvm.insertelement"(%59, %9, %60) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %62 = "llvm.mlir.undef"() : () -> vector<8xi64>
    %63 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %64 = "llvm.insertelement"(%62, %10, %63) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %65 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %66 = "llvm.insertelement"(%64, %4, %65) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %67 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %68 = "llvm.insertelement"(%66, %10, %67) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %69 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %70 = "llvm.insertelement"(%68, %4, %69) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %71 = "llvm.mlir.constant"() <{value = 4 : i32}> : () -> i32
    %72 = "llvm.insertelement"(%70, %4, %71) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %73 = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
    %74 = "llvm.insertelement"(%72, %9, %73) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %75 = "llvm.mlir.constant"() <{value = 6 : i32}> : () -> i32
    %76 = "llvm.insertelement"(%74, %9, %75) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %77 = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
    %78 = "llvm.insertelement"(%76, %9, %77) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %79 = "llvm.mlir.undef"() : () -> vector<8xi64>
    %80 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %81 = "llvm.insertelement"(%79, %9, %80) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %82 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %83 = "llvm.insertelement"(%81, %9, %82) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %84 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %85 = "llvm.insertelement"(%83, %9, %84) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %86 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %87 = "llvm.insertelement"(%85, %9, %86) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %88 = "llvm.mlir.constant"() <{value = 4 : i32}> : () -> i32
    %89 = "llvm.insertelement"(%87, %9, %88) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %90 = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
    %91 = "llvm.insertelement"(%89, %9, %90) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %92 = "llvm.mlir.constant"() <{value = 6 : i32}> : () -> i32
    %93 = "llvm.insertelement"(%91, %9, %92) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %94 = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
    %95 = "llvm.insertelement"(%93, %4, %94) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %96 = "llvm.mlir.undef"() : () -> vector<8xi64>
    %97 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %98 = "llvm.insertelement"(%96, %4, %97) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %99 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %100 = "llvm.insertelement"(%98, %4, %99) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %101 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %102 = "llvm.insertelement"(%100, %4, %101) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %103 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %104 = "llvm.insertelement"(%102, %4, %103) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %105 = "llvm.mlir.constant"() <{value = 4 : i32}> : () -> i32
    %106 = "llvm.insertelement"(%104, %4, %105) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %107 = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
    %108 = "llvm.insertelement"(%106, %9, %107) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %109 = "llvm.mlir.constant"() <{value = 6 : i32}> : () -> i32
    %110 = "llvm.insertelement"(%108, %9, %109) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %111 = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
    %112 = "llvm.insertelement"(%110, %9, %111) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %113 = "llvm.mlir.constant"() <{value = dense<[-1, -1, -1, -1, -1, -1, 0, 0]> : vector<8xi64>}> : () -> vector<8xi64>
    %114 = "llvm.mlir.constant"() <{value = dense<7> : vector<8xi64>}> : () -> vector<8xi64>
    %115 = "llvm.mlir.constant"() <{value = dense<24> : vector<8xi64>}> : () -> vector<8xi64>
    %116 = "llvm.shufflevector"(%arg0, %0) <{mask = array<i32: 0, 0, 0, 0, 0, 0, 3, 3>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %117 = "llvm.shufflevector"(%arg0, %0) <{mask = array<i32: 0, 1, 2, 3, 4, 5, 3, 4>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %118 = "llvm.shufflevector"(%arg0, %0) <{mask = array<i32: 4, 4, 1, 1, 1, 1, 1, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %119 = "llvm.shufflevector"(%arg0, %0) <{mask = array<i32: 4, 5, 1, 2, 3, 4, 5, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %120 = "llvm.shufflevector"(%arg0, %0) <{mask = array<i32: 3, 7, 5, 7, 2, 2, 2, 2>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %121 = "llvm.shufflevector"(%arg0, %0) <{mask = array<i32: 5, 7, 5, 7, 2, 3, 4, 5>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %122 = "llvm.shl"(%116, %1) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %123 = "llvm.shl"(%118, %2) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %124 = "llvm.shl"(%120, %3) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %125 = "x86vector.avx512.intr.vpmadd52l.uq.512"(%5, %122, %117) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %126 = "x86vector.avx512.intr.vpmadd52l.uq.512"(%5, %123, %119) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %127 = "x86vector.avx512.intr.vpmadd52l.uq.512"(%5, %124, %121) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %128 = "x86vector.avx512.intr.vpmadd52h.uq.512"(%5, %122, %117) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %129 = "llvm.shl"(%128, %6) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %130 = "x86vector.avx512.intr.vpmadd52h.uq.512"(%5, %123, %119) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %131 = "llvm.shl"(%130, %6) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %132 = "x86vector.avx512.intr.vpmadd52h.uq.512"(%5, %124, %121) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %133 = "llvm.shl"(%132, %6) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %134 = "llvm.and"(%126, %7) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %135 = "llvm.and"(%127, %8) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %136 = "llvm.and"(%131, %7) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %137 = "llvm.and"(%133, %8) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %138 = "llvm.add"(%136, %129) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %139 = "llvm.add"(%138, %137) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %140 = "llvm.and"(%126, %27) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %141 = "llvm.and"(%127, %44) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %142 = "llvm.and"(%131, %61) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %143 = "llvm.and"(%133, %78) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %144 = "llvm.add"(%143, %142) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %145 = "llvm.shufflevector"(%95, %139) <{mask = array<i32: 7, 8, 9, 10, 11, 12, 13, 14>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %146 = "llvm.add"(%134, %125) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %147 = "llvm.add"(%146, %135) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %148 = "llvm.add"(%147, %145) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %149 = "llvm.shufflevector"(%95, %144) <{mask = array<i32: 7, 8, 9, 10, 11, 12, -1, -1>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %150 = "llvm.shufflevector"(%139, %112) <{mask = array<i32: 7, 8, 9, 10, 11, 12, -1, -1>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %151 = "llvm.add"(%141, %140) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %152 = "llvm.add"(%151, %149) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %153 = "llvm.add"(%152, %150) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %154 = "llvm.and"(%148, %113) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %155 = "llvm.shufflevector"(%148, %153) <{mask = array<i32: 6, 7, 8, 9, 10, 11, 12, 13>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %156 = "llvm.shl"(%155, %114) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %157 = "llvm.add"(%156, %154) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %158 = "llvm.mul"(%155, %115) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %159 = "llvm.add"(%157, %158) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    "llvm.return"(%159) : (vector<8xi64>) -> ()
}
]

end Firedancer.Avx512
