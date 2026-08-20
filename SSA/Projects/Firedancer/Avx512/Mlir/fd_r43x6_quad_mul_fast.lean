/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.SLLVM.Dialect

/-!
# `fd_r43x6_quad_mul_fast`, lifted with its memory writes intact

The program below is the MLIR translation of `fd_r43x6_quad_mul_fast` from
`firedancer/src/ballet/ed25519/avx512/fd_r43x6_inl.h`, taken **verbatim** from
the build artifact
`build/native/gcc/mlir/avx512/region/fd_r43x6_quad_mul_fast.mlir`.

This is the kernel as the compiler emits it, with no extraction probe around
it: it takes the three `fd_r43x6_t *` out-parameters as `!llvm.ptr` block
arguments and ends in three `llvm.store`s. Nothing here is rewritten -- not the
`!llvm.ptr` spelling, not the `(value, ptr)` operand order of `llvm.store`, not
the `alignment`, `ordering` and `tbaa` attributes.

`%81`, `%85` and `%89` are the results `z03`, `z14` and `z25`.

Block arguments enter the `Ctxt` in reverse declaration order, so the context
is `[y25, y14, y03, x25, x14, x03, z25ptr, z14ptr, z03ptr]`; see `quadValMem6`
in `Proof/Mem.lean`. The program is `.impure` throughout and returns nothing.
-/

namespace Firedancer.Avx512
open LeanMLIR SLLVM

/-- The region as an AST value, so it can be written once and used both as the
`Com` below and as the callee binding in `Mlir/fd_r43x6_ge_is_eq.lean`. -/
def fd_r43x6_quad_mul_fastRegion : MLIR.AST.Region 0 := [mlir_region|
{
  ^bb0(%arg0: !llvm.ptr, %arg1: !llvm.ptr, %arg2: !llvm.ptr, %arg3: vector<8xi64>, %arg4: vector<8xi64>, %arg5: vector<8xi64>, %arg6: vector<8xi64>, %arg7: vector<8xi64>, %arg8: vector<8xi64>):
    %0 = "llvm.mlir.poison"() : () -> vector<8xi64>
    %1 = "llvm.mlir.constant"() <{value = 0 : i64}> : () -> i64
    %2 = "llvm.mlir.constant"() <{value = dense<0> : vector<8xi64>}> : () -> vector<8xi64>
    %3 = "llvm.mlir.constant"() <{value = dense<9> : vector<8xi64>}> : () -> vector<8xi64>
    %4 = "llvm.mlir.constant"() <{value = dense<7> : vector<8xi64>}> : () -> vector<8xi64>
    %5 = "llvm.mlir.constant"() <{value = dense<24> : vector<8xi64>}> : () -> vector<8xi64>
    %6 = "llvm.shufflevector"(%arg3, %0) <{mask = array<i32: 0, 1, 2, 3, 0, 1, 2, 3>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %7 = "llvm.shufflevector"(%arg4, %0) <{mask = array<i32: 0, 1, 2, 3, 0, 1, 2, 3>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %8 = "llvm.shufflevector"(%arg5, %0) <{mask = array<i32: 0, 1, 2, 3, 0, 1, 2, 3>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %9 = "llvm.shufflevector"(%arg3, %0) <{mask = array<i32: 4, 5, 6, 7, 4, 5, 6, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %10 = "llvm.shufflevector"(%arg4, %0) <{mask = array<i32: 4, 5, 6, 7, 4, 5, 6, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %11 = "llvm.shufflevector"(%arg5, %0) <{mask = array<i32: 4, 5, 6, 7, 4, 5, 6, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %12 = "x86vector.avx512.intr.vpmadd52l.uq.512"(%2, %6, %arg6) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %13 = "x86vector.avx512.intr.vpmadd52l.uq.512"(%2, %7, %arg6) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %14 = "x86vector.avx512.intr.vpmadd52l.uq.512"(%13, %6, %arg7) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %15 = "x86vector.avx512.intr.vpmadd52l.uq.512"(%2, %8, %arg6) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %16 = "x86vector.avx512.intr.vpmadd52l.uq.512"(%15, %7, %arg7) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %17 = "x86vector.avx512.intr.vpmadd52l.uq.512"(%16, %6, %arg8) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %18 = "x86vector.avx512.intr.vpmadd52l.uq.512"(%2, %9, %arg6) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %19 = "x86vector.avx512.intr.vpmadd52l.uq.512"(%18, %8, %arg7) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %20 = "x86vector.avx512.intr.vpmadd52l.uq.512"(%19, %7, %arg8) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %21 = "x86vector.avx512.intr.vpmadd52l.uq.512"(%2, %10, %arg6) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %22 = "x86vector.avx512.intr.vpmadd52l.uq.512"(%21, %9, %arg7) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %23 = "x86vector.avx512.intr.vpmadd52l.uq.512"(%22, %8, %arg8) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %24 = "x86vector.avx512.intr.vpmadd52l.uq.512"(%2, %11, %arg6) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %25 = "x86vector.avx512.intr.vpmadd52l.uq.512"(%24, %10, %arg7) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %26 = "x86vector.avx512.intr.vpmadd52l.uq.512"(%25, %9, %arg8) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %27 = "x86vector.avx512.intr.vpmadd52l.uq.512"(%2, %11, %arg7) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %28 = "x86vector.avx512.intr.vpmadd52l.uq.512"(%27, %10, %arg8) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %29 = "x86vector.avx512.intr.vpmadd52l.uq.512"(%2, %11, %arg8) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %30 = "x86vector.avx512.intr.vpmadd52h.uq.512"(%2, %6, %arg6) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %31 = "llvm.shl"(%30, %3) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %32 = "llvm.add"(%31, %14) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %33 = "x86vector.avx512.intr.vpmadd52h.uq.512"(%2, %7, %arg6) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %34 = "x86vector.avx512.intr.vpmadd52h.uq.512"(%33, %6, %arg7) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %35 = "llvm.shl"(%34, %3) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %36 = "llvm.add"(%35, %17) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %37 = "x86vector.avx512.intr.vpmadd52h.uq.512"(%2, %8, %arg6) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %38 = "x86vector.avx512.intr.vpmadd52h.uq.512"(%37, %7, %arg7) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %39 = "x86vector.avx512.intr.vpmadd52h.uq.512"(%38, %6, %arg8) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %40 = "llvm.shl"(%39, %3) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %41 = "llvm.add"(%40, %20) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %42 = "x86vector.avx512.intr.vpmadd52h.uq.512"(%2, %9, %arg6) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %43 = "x86vector.avx512.intr.vpmadd52h.uq.512"(%42, %8, %arg7) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %44 = "x86vector.avx512.intr.vpmadd52h.uq.512"(%43, %7, %arg8) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %45 = "llvm.shl"(%44, %3) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %46 = "llvm.add"(%45, %23) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %47 = "x86vector.avx512.intr.vpmadd52h.uq.512"(%2, %10, %arg6) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %48 = "x86vector.avx512.intr.vpmadd52h.uq.512"(%47, %9, %arg7) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %49 = "x86vector.avx512.intr.vpmadd52h.uq.512"(%48, %8, %arg8) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %50 = "llvm.shl"(%49, %3) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %51 = "llvm.add"(%50, %26) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %52 = "x86vector.avx512.intr.vpmadd52h.uq.512"(%2, %11, %arg6) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %53 = "x86vector.avx512.intr.vpmadd52h.uq.512"(%52, %10, %arg7) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %54 = "x86vector.avx512.intr.vpmadd52h.uq.512"(%53, %9, %arg8) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %55 = "llvm.shl"(%54, %3) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %56 = "llvm.add"(%55, %28) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %57 = "x86vector.avx512.intr.vpmadd52h.uq.512"(%2, %11, %arg7) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %58 = "x86vector.avx512.intr.vpmadd52h.uq.512"(%57, %10, %arg8) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %59 = "llvm.shl"(%58, %3) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %60 = "llvm.add"(%59, %29) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %61 = "x86vector.avx512.intr.vpmadd52h.uq.512"(%2, %11, %arg8) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
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
    "llvm.store"(%81, %arg0) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (vector<8xi64>, !llvm.ptr) -> ()
    "llvm.store"(%85, %arg1) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (vector<8xi64>, !llvm.ptr) -> ()
    "llvm.store"(%89, %arg2) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (vector<8xi64>, !llvm.ptr) -> ()
    "llvm.return"() : () -> ()
}
]

def fd_r43x6_quad_mul_fast := [sllvm_of| fd_r43x6_quad_mul_fastRegion]

end Firedancer.Avx512
