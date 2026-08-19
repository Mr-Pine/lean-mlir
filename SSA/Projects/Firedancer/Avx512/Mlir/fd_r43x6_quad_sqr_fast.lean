/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.SLLVM.Dialect

/-!
# `fd_r43x6_quad_sqr_fast`, lifted from Firedancer's AVX-512 ed25519 implementation

The program below is the MLIR translation of `fd_r43x6_quad_sqr_fast` from
`firedancer/src/ballet/ed25519/avx512/fd_r43x6_inl.h`, taken verbatim from the
build artifact
`build/linux/gcc/x86_64/mlir/avx512-quad/region/fd_mlir_r43x6_quad_sqr_fast.mlir`
produced by `make mlir-avx512-quad` on the firedancer `conformance-lean-mlir`
branch.

Block arguments are `x03, x14, x25`. The single result is **24 lanes**: the kernel
returns three `fd_r43x6_t` through pointers, and the extraction probe
concatenates them, lanes 0-7 holding `z03`, 8-15 `z14` and 16-23 `z25`.

That concatenation is the only thing the probe adds, and it is why the kernel
is extracted *without* `-fno-inline`, unlike the scalar probes of
`mlir_avx512.c`: left uninlined the kernel carries pointer parameters and
stores, and returning a three-vector struct instead goes by `sret`, which is
again a pointer and stores -- none of which this dialect can express. Inlined,
`-O2` promotes the stores away and what remains is straight-line vector
arithmetic plus three shuffles of result packaging at the end. See
`conformance_verification/mlir_avx512_quad.c`.
-/

namespace Firedancer.Avx512
open LeanMLIR SLLVM

def fd_r43x6_quad_sqr_fast := [sllvm|
{
  ^bb0(%arg0: vector<8xi64>, %arg1: vector<8xi64>, %arg2: vector<8xi64>):
    %0 = "llvm.mlir.poison"() : () -> vector<8xi64>
    %1 = "llvm.mlir.poison"() : () -> i64
    %2 = "llvm.mlir.constant"() <{value = 0 : i64}> : () -> i64
    %3 = "llvm.mlir.undef"() : () -> vector<8xi64>
    %4 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %5 = "llvm.insertelement"(%3, %2, %4) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %6 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %7 = "llvm.insertelement"(%5, %2, %6) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %8 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %9 = "llvm.insertelement"(%7, %2, %8) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %10 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %11 = "llvm.insertelement"(%9, %2, %10) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %12 = "llvm.mlir.constant"() <{value = 4 : i32}> : () -> i32
    %13 = "llvm.insertelement"(%11, %1, %12) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %14 = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
    %15 = "llvm.insertelement"(%13, %1, %14) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %16 = "llvm.mlir.constant"() <{value = 6 : i32}> : () -> i32
    %17 = "llvm.insertelement"(%15, %1, %16) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %18 = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
    %19 = "llvm.insertelement"(%17, %1, %18) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %20 = "llvm.mlir.constant"() <{value = dense<1> : vector<8xi64>}> : () -> vector<8xi64>
    %21 = "llvm.mlir.constant"() <{value = dense<0> : vector<8xi64>}> : () -> vector<8xi64>
    %22 = "llvm.mlir.constant"() <{value = dense<9> : vector<8xi64>}> : () -> vector<8xi64>
    %23 = "llvm.mlir.undef"() : () -> vector<8xi64>
    %24 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %25 = "llvm.insertelement"(%23, %1, %24) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %26 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %27 = "llvm.insertelement"(%25, %1, %26) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %28 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %29 = "llvm.insertelement"(%27, %1, %28) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %30 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %31 = "llvm.insertelement"(%29, %1, %30) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %32 = "llvm.mlir.constant"() <{value = 4 : i32}> : () -> i32
    %33 = "llvm.insertelement"(%31, %2, %32) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %34 = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
    %35 = "llvm.insertelement"(%33, %2, %34) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %36 = "llvm.mlir.constant"() <{value = 6 : i32}> : () -> i32
    %37 = "llvm.insertelement"(%35, %2, %36) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %38 = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
    %39 = "llvm.insertelement"(%37, %2, %38) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %40 = "llvm.mlir.constant"() <{value = dense<7> : vector<8xi64>}> : () -> vector<8xi64>
    %41 = "llvm.mlir.constant"() <{value = dense<24> : vector<8xi64>}> : () -> vector<8xi64>
    %42 = "llvm.shufflevector"(%arg0, %arg2) <{mask = array<i32: 0, 1, 2, 3, 12, 13, 14, 15>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %43 = "llvm.shufflevector"(%arg1, %arg2) <{mask = array<i32: 0, 1, 2, 3, 8, 9, 10, 11>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %44 = "llvm.shufflevector"(%arg0, %arg1) <{mask = array<i32: 4, 5, 6, 7, 12, 13, 14, 15>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %45 = "llvm.shufflevector"(%arg1, %0) <{mask = array<i32: 4, 5, 6, 7, 0, 1, 2, 3>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %46 = "llvm.shufflevector"(%arg2, %arg0) <{mask = array<i32: 0, 1, 2, 3, 12, 13, 14, 15>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %47 = "llvm.shufflevector"(%arg2, %0) <{mask = array<i32: 4, 5, 6, 7, 0, 1, 2, 3>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %48 = "llvm.shufflevector"(%arg1, %19) <{mask = array<i32: 4, 5, 6, 7, 8, 9, 10, 11>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %49 = "llvm.shl"(%arg0, %20) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %50 = "llvm.shl"(%arg1, %20) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %51 = "llvm.shl"(%42, %20) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %52 = "llvm.shl"(%43, %20) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %53 = "x86vector.avx512.intr.vpmadd52l.uq.512"(%21, %42, %42) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %54 = "x86vector.avx512.intr.vpmadd52l.uq.512"(%21, %51, %arg1) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %55 = "x86vector.avx512.intr.vpmadd52l.uq.512"(%21, %arg1, %arg1) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %56 = "x86vector.avx512.intr.vpmadd52l.uq.512"(%55, %49, %arg2) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %57 = "x86vector.avx512.intr.vpmadd52l.uq.512"(%21, %49, %44) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %58 = "x86vector.avx512.intr.vpmadd52l.uq.512"(%57, %52, %arg2) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %59 = "x86vector.avx512.intr.vpmadd52l.uq.512"(%21, %46, %46) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %60 = "x86vector.avx512.intr.vpmadd52l.uq.512"(%59, %51, %45) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %61 = "x86vector.avx512.intr.vpmadd52l.uq.512"(%60, %52, %44) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %62 = "x86vector.avx512.intr.vpmadd52l.uq.512"(%21, %49, %47) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %63 = "x86vector.avx512.intr.vpmadd52l.uq.512"(%62, %50, %48) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %64 = "x86vector.avx512.intr.vpmadd52h.uq.512"(%21, %42, %42) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %65 = "llvm.shl"(%64, %22) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %66 = "x86vector.avx512.intr.vpmadd52h.uq.512"(%21, %51, %arg1) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %67 = "llvm.shl"(%66, %22) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %68 = "x86vector.avx512.intr.vpmadd52h.uq.512"(%21, %arg1, %arg1) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %69 = "x86vector.avx512.intr.vpmadd52h.uq.512"(%68, %49, %arg2) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %70 = "llvm.shl"(%69, %22) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %71 = "x86vector.avx512.intr.vpmadd52h.uq.512"(%21, %49, %44) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %72 = "x86vector.avx512.intr.vpmadd52h.uq.512"(%71, %52, %arg2) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %73 = "llvm.shl"(%72, %22) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %74 = "x86vector.avx512.intr.vpmadd52h.uq.512"(%21, %46, %46) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %75 = "x86vector.avx512.intr.vpmadd52h.uq.512"(%74, %51, %45) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %76 = "x86vector.avx512.intr.vpmadd52h.uq.512"(%75, %52, %44) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %77 = "llvm.shl"(%76, %22) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %78 = "x86vector.avx512.intr.vpmadd52h.uq.512"(%21, %49, %47) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %79 = "x86vector.avx512.intr.vpmadd52h.uq.512"(%78, %50, %48) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %80 = "llvm.shl"(%79, %22) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %81 = "llvm.shufflevector"(%53, %58) <{mask = array<i32: 0, 1, 2, 3, 8, 9, 10, 11>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %82 = "llvm.shufflevector"(%19, %70) <{mask = array<i32: 0, 1, 2, 3, 8, 9, 10, 11>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %83 = "llvm.add"(%82, %81) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %84 = "llvm.shufflevector"(%54, %61) <{mask = array<i32: 0, 1, 2, 3, 8, 9, 10, 11>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %85 = "llvm.shufflevector"(%65, %73) <{mask = array<i32: 0, 1, 2, 3, 8, 9, 10, 11>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %86 = "llvm.add"(%85, %84) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %87 = "llvm.shufflevector"(%56, %63) <{mask = array<i32: 0, 1, 2, 3, 8, 9, 10, 11>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %88 = "llvm.shufflevector"(%67, %77) <{mask = array<i32: 0, 1, 2, 3, 8, 9, 10, 11>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %89 = "llvm.shufflevector"(%19, %63) <{mask = array<i32: 0, 1, 2, 3, 12, 13, 14, 15>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %90 = "llvm.shufflevector"(%61, %54) <{mask = array<i32: 4, 5, 6, 7, 12, 13, 14, 15>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %91 = "llvm.shufflevector"(%80, %70) <{mask = array<i32: 4, 5, 6, 7, 12, 13, 14, 15>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %92 = "llvm.add"(%91, %90) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %93 = "llvm.shufflevector"(%80, %39) <{mask = array<i32: 0, 1, 2, 3, 12, 13, 14, 15>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %94 = "llvm.add"(%92, %93) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %95 = "llvm.shufflevector"(%58, %53) <{mask = array<i32: 4, 5, 6, 7, 12, 13, 14, 15>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %96 = "llvm.shufflevector"(%77, %67) <{mask = array<i32: 4, 5, 6, 7, 12, 13, 14, 15>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %97 = "llvm.add"(%96, %95) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %98 = "llvm.shufflevector"(%56, %39) <{mask = array<i32: 4, 5, 6, 7, 12, 13, 14, 15>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %99 = "llvm.shufflevector"(%73, %65) <{mask = array<i32: 4, 5, 6, 7, 12, 13, 14, 15>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %100 = "llvm.add"(%99, %98) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %101 = "llvm.shl"(%94, %40) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %102 = "llvm.add"(%83, %101) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %103 = "llvm.mul"(%94, %41) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %104 = "llvm.add"(%102, %103) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %105 = "llvm.shl"(%97, %40) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %106 = "llvm.add"(%86, %105) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %107 = "llvm.mul"(%97, %41) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %108 = "llvm.add"(%106, %107) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %109 = "llvm.shl"(%100, %40) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %110 = "llvm.mul"(%100, %41) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %111 = "llvm.add"(%89, %87) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %112 = "llvm.add"(%111, %109) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %113 = "llvm.add"(%112, %110) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %114 = "llvm.add"(%113, %88) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %115 = "llvm.shufflevector"(%104, %108) <{mask = array<i32: 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15>}> : (vector<8xi64>, vector<8xi64>) -> vector<16xi64>
    %116 = "llvm.shufflevector"(%114, %0) <{mask = array<i32: 0, 1, 2, 3, 4, 5, 6, 7, -1, -1, -1, -1, -1, -1, -1, -1>}> : (vector<8xi64>, vector<8xi64>) -> vector<16xi64>
    %117 = "llvm.shufflevector"(%115, %116) <{mask = array<i32: 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23>}> : (vector<16xi64>, vector<16xi64>) -> vector<24xi64>
    "llvm.return"(%117) : (vector<24xi64>) -> ()
}
]

end Firedancer.Avx512
