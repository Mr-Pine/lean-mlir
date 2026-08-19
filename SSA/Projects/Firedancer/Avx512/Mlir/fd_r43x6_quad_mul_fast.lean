/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.SLLVM.Dialect

/-!
# `fd_r43x6_quad_mul_fast`, lifted from Firedancer's AVX-512 ed25519 implementation

The program below is the MLIR translation of `fd_r43x6_quad_mul_fast` from
`firedancer/src/ballet/ed25519/avx512/fd_r43x6_inl.h`, taken verbatim from the
build artifact
`build/linux/gcc/x86_64/mlir/avx512-quad/region/fd_mlir_r43x6_quad_mul_fast.mlir`
produced by `make mlir-avx512-quad` on the firedancer `conformance-lean-mlir`
branch.

Block arguments are `x03, x14, x25, y03, y14, y25`. The single result is **24 lanes**: the kernel
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

def fd_r43x6_quad_mul_fast := [sllvm|
{
  ^bb0(%arg0: vector<8xi64>, %arg1: vector<8xi64>, %arg2: vector<8xi64>, %arg3: vector<8xi64>, %arg4: vector<8xi64>, %arg5: vector<8xi64>):
    %0 = "llvm.mlir.poison"() : () -> vector<8xi64>
    %1 = "llvm.mlir.constant"() <{value = 0 : i64}> : () -> i64
    %2 = "llvm.mlir.constant"() <{value = dense<0> : vector<8xi64>}> : () -> vector<8xi64>
    %3 = "llvm.mlir.constant"() <{value = dense<9> : vector<8xi64>}> : () -> vector<8xi64>
    %4 = "llvm.mlir.constant"() <{value = dense<7> : vector<8xi64>}> : () -> vector<8xi64>
    %5 = "llvm.mlir.constant"() <{value = dense<24> : vector<8xi64>}> : () -> vector<8xi64>
    %6 = "llvm.shufflevector"(%arg0, %0) <{mask = array<i32: 0, 1, 2, 3, 0, 1, 2, 3>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %7 = "llvm.shufflevector"(%arg1, %0) <{mask = array<i32: 0, 1, 2, 3, 0, 1, 2, 3>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %8 = "llvm.shufflevector"(%arg2, %0) <{mask = array<i32: 0, 1, 2, 3, 0, 1, 2, 3>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %9 = "llvm.shufflevector"(%arg0, %0) <{mask = array<i32: 4, 5, 6, 7, 4, 5, 6, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %10 = "llvm.shufflevector"(%arg1, %0) <{mask = array<i32: 4, 5, 6, 7, 4, 5, 6, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %11 = "llvm.shufflevector"(%arg2, %0) <{mask = array<i32: 4, 5, 6, 7, 4, 5, 6, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %12 = "x86vector.avx512.intr.vpmadd52l.uq.512"(%2, %6, %arg3) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %13 = "x86vector.avx512.intr.vpmadd52l.uq.512"(%2, %7, %arg3) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %14 = "x86vector.avx512.intr.vpmadd52l.uq.512"(%13, %6, %arg4) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %15 = "x86vector.avx512.intr.vpmadd52l.uq.512"(%2, %8, %arg3) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %16 = "x86vector.avx512.intr.vpmadd52l.uq.512"(%15, %7, %arg4) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %17 = "x86vector.avx512.intr.vpmadd52l.uq.512"(%16, %6, %arg5) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %18 = "x86vector.avx512.intr.vpmadd52l.uq.512"(%2, %9, %arg3) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %19 = "x86vector.avx512.intr.vpmadd52l.uq.512"(%18, %8, %arg4) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %20 = "x86vector.avx512.intr.vpmadd52l.uq.512"(%19, %7, %arg5) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %21 = "x86vector.avx512.intr.vpmadd52l.uq.512"(%2, %10, %arg3) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %22 = "x86vector.avx512.intr.vpmadd52l.uq.512"(%21, %9, %arg4) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %23 = "x86vector.avx512.intr.vpmadd52l.uq.512"(%22, %8, %arg5) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %24 = "x86vector.avx512.intr.vpmadd52l.uq.512"(%2, %11, %arg3) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %25 = "x86vector.avx512.intr.vpmadd52l.uq.512"(%24, %10, %arg4) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %26 = "x86vector.avx512.intr.vpmadd52l.uq.512"(%25, %9, %arg5) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %27 = "x86vector.avx512.intr.vpmadd52l.uq.512"(%2, %11, %arg4) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %28 = "x86vector.avx512.intr.vpmadd52l.uq.512"(%27, %10, %arg5) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %29 = "x86vector.avx512.intr.vpmadd52l.uq.512"(%2, %11, %arg5) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %30 = "x86vector.avx512.intr.vpmadd52h.uq.512"(%2, %6, %arg3) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %31 = "llvm.shl"(%30, %3) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %32 = "llvm.add"(%31, %14) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %33 = "x86vector.avx512.intr.vpmadd52h.uq.512"(%2, %7, %arg3) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %34 = "x86vector.avx512.intr.vpmadd52h.uq.512"(%33, %6, %arg4) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %35 = "llvm.shl"(%34, %3) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %36 = "llvm.add"(%35, %17) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %37 = "x86vector.avx512.intr.vpmadd52h.uq.512"(%2, %8, %arg3) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %38 = "x86vector.avx512.intr.vpmadd52h.uq.512"(%37, %7, %arg4) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %39 = "x86vector.avx512.intr.vpmadd52h.uq.512"(%38, %6, %arg5) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %40 = "llvm.shl"(%39, %3) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %41 = "llvm.add"(%40, %20) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %42 = "x86vector.avx512.intr.vpmadd52h.uq.512"(%2, %9, %arg3) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %43 = "x86vector.avx512.intr.vpmadd52h.uq.512"(%42, %8, %arg4) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %44 = "x86vector.avx512.intr.vpmadd52h.uq.512"(%43, %7, %arg5) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %45 = "llvm.shl"(%44, %3) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %46 = "llvm.add"(%45, %23) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %47 = "x86vector.avx512.intr.vpmadd52h.uq.512"(%2, %10, %arg3) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %48 = "x86vector.avx512.intr.vpmadd52h.uq.512"(%47, %9, %arg4) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %49 = "x86vector.avx512.intr.vpmadd52h.uq.512"(%48, %8, %arg5) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %50 = "llvm.shl"(%49, %3) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %51 = "llvm.add"(%50, %26) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %52 = "x86vector.avx512.intr.vpmadd52h.uq.512"(%2, %11, %arg3) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %53 = "x86vector.avx512.intr.vpmadd52h.uq.512"(%52, %10, %arg4) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %54 = "x86vector.avx512.intr.vpmadd52h.uq.512"(%53, %9, %arg5) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %55 = "llvm.shl"(%54, %3) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %56 = "llvm.add"(%55, %28) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %57 = "x86vector.avx512.intr.vpmadd52h.uq.512"(%2, %11, %arg4) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %58 = "x86vector.avx512.intr.vpmadd52h.uq.512"(%57, %10, %arg5) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %59 = "llvm.shl"(%58, %3) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %60 = "llvm.add"(%59, %29) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %61 = "x86vector.avx512.intr.vpmadd52h.uq.512"(%2, %11, %arg5) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %62 = "llvm.shl"(%61, %3) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %63 = "llvm.shufflevector"(%41, %0) <{mask = array<i32: 4, 5, 6, 7, 0, 1, 2, 3>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %64 = "llvm.shufflevector"(%46, %0) <{mask = array<i32: 4, 5, 6, 7, 0, 1, 2, 3>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %65 = "llvm.shufflevector"(%51, %0) <{mask = array<i32: 4, 5, 6, 7, 0, 1, 2, 3>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %66 = "llvm.add"(%63, %12) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %67 = "llvm.shufflevector"(%12, %66) <{mask = array<i32: 0, 1, 2, 3, 12, 13, 14, 15>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %68 = "llvm.add"(%64, %32) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %69 = "llvm.shufflevector"(%32, %68) <{mask = array<i32: 0, 1, 2, 3, 12, 13, 14, 15>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %70 = "llvm.add"(%65, %36) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %71 = "llvm.shufflevector"(%36, %70) <{mask = array<i32: 0, 1, 2, 3, 12, 13, 14, 15>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %72 = "llvm.add"(%56, %63) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %73 = "llvm.shufflevector"(%72, %56) <{mask = array<i32: 0, 1, 2, 3, 12, 13, 14, 15>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %74 = "llvm.add"(%60, %64) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %75 = "llvm.shufflevector"(%74, %60) <{mask = array<i32: 0, 1, 2, 3, 12, 13, 14, 15>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %76 = "llvm.add"(%62, %65) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %77 = "llvm.shufflevector"(%76, %62) <{mask = array<i32: 0, 1, 2, 3, 12, 13, 14, 15>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %78 = "llvm.shl"(%73, %4) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %79 = "llvm.add"(%78, %67) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %80 = "llvm.mul"(%73, %5) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %81 = "llvm.add"(%79, %80) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %82 = "llvm.shl"(%75, %4) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %83 = "llvm.add"(%82, %69) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %84 = "llvm.mul"(%75, %5) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %85 = "llvm.add"(%83, %84) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %86 = "llvm.shl"(%77, %4) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %87 = "llvm.add"(%86, %71) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %88 = "llvm.mul"(%77, %5) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %89 = "llvm.add"(%87, %88) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %90 = "llvm.shufflevector"(%81, %85) <{mask = array<i32: 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15>}> : (vector<8xi64>, vector<8xi64>) -> vector<16xi64>
    %91 = "llvm.shufflevector"(%89, %0) <{mask = array<i32: 0, 1, 2, 3, 4, 5, 6, 7, -1, -1, -1, -1, -1, -1, -1, -1>}> : (vector<8xi64>, vector<8xi64>) -> vector<16xi64>
    %92 = "llvm.shufflevector"(%90, %91) <{mask = array<i32: 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23>}> : (vector<16xi64>, vector<16xi64>) -> vector<24xi64>
    "llvm.return"(%92) : (vector<24xi64>) -> ()
}
]

end Firedancer.Avx512
