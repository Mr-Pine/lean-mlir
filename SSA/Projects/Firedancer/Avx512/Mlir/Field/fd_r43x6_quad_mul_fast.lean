/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
-- build/native/gcc/mlir_canonicalized/avx512/region/fd_r43x6_quad_mul_fast.mlir
module

public import SSA.Projects.SLLVM.Dialect

@[expose] public section

namespace Firedancer.Avx512
open LeanMLIR SLLVM

def fd_r43x6_quad_mul_fast_region : MLIR.AST.Region 0 := [mlir_region|
{
  ^bb0(%arg0: !llvm.ptr, %arg1: !llvm.ptr, %arg2: !llvm.ptr, %arg3: vector<8xi64>, %arg4: vector<8xi64>, %arg5: vector<8xi64>, %arg6: vector<8xi64>, %arg7: vector<8xi64>, %arg8: vector<8xi64>):
    %0 = "llvm.mlir.constant"() <{value = dense<24> : vector<8xi64>}> : () -> vector<8xi64>
    %1 = "llvm.mlir.constant"() <{value = dense<7> : vector<8xi64>}> : () -> vector<8xi64>
    %2 = "llvm.mlir.constant"() <{value = dense<9> : vector<8xi64>}> : () -> vector<8xi64>
    %3 = "llvm.mlir.constant"() <{value = dense<0> : vector<8xi64>}> : () -> vector<8xi64>
    %4 = "llvm.mlir.poison"() : () -> vector<8xi64>
    %5 = "llvm.shufflevector"(%arg3, %4) <{mask = array<i32: 0, 1, 2, 3, 0, 1, 2, 3>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %6 = "llvm.shufflevector"(%arg4, %4) <{mask = array<i32: 0, 1, 2, 3, 0, 1, 2, 3>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %7 = "llvm.shufflevector"(%arg5, %4) <{mask = array<i32: 0, 1, 2, 3, 0, 1, 2, 3>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %8 = "llvm.shufflevector"(%arg3, %4) <{mask = array<i32: 4, 5, 6, 7, 4, 5, 6, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %9 = "llvm.shufflevector"(%arg4, %4) <{mask = array<i32: 4, 5, 6, 7, 4, 5, 6, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %10 = "llvm.shufflevector"(%arg5, %4) <{mask = array<i32: 4, 5, 6, 7, 4, 5, 6, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %11 = "x86vector.avx512.intr.vpmadd52l.uq.512"(%3, %5, %arg6) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %12 = "x86vector.avx512.intr.vpmadd52l.uq.512"(%3, %6, %arg6) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %13 = "x86vector.avx512.intr.vpmadd52l.uq.512"(%12, %5, %arg7) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %14 = "x86vector.avx512.intr.vpmadd52l.uq.512"(%3, %7, %arg6) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %15 = "x86vector.avx512.intr.vpmadd52l.uq.512"(%14, %6, %arg7) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %16 = "x86vector.avx512.intr.vpmadd52l.uq.512"(%15, %5, %arg8) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %17 = "x86vector.avx512.intr.vpmadd52l.uq.512"(%3, %8, %arg6) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %18 = "x86vector.avx512.intr.vpmadd52l.uq.512"(%17, %7, %arg7) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %19 = "x86vector.avx512.intr.vpmadd52l.uq.512"(%18, %6, %arg8) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %20 = "x86vector.avx512.intr.vpmadd52l.uq.512"(%3, %9, %arg6) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %21 = "x86vector.avx512.intr.vpmadd52l.uq.512"(%20, %8, %arg7) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %22 = "x86vector.avx512.intr.vpmadd52l.uq.512"(%21, %7, %arg8) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %23 = "x86vector.avx512.intr.vpmadd52l.uq.512"(%3, %10, %arg6) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %24 = "x86vector.avx512.intr.vpmadd52l.uq.512"(%23, %9, %arg7) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %25 = "x86vector.avx512.intr.vpmadd52l.uq.512"(%24, %8, %arg8) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %26 = "x86vector.avx512.intr.vpmadd52l.uq.512"(%3, %10, %arg7) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %27 = "x86vector.avx512.intr.vpmadd52l.uq.512"(%26, %9, %arg8) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %28 = "x86vector.avx512.intr.vpmadd52l.uq.512"(%3, %10, %arg8) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %29 = "x86vector.avx512.intr.vpmadd52h.uq.512"(%3, %5, %arg6) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %30 = "llvm.shl"(%29, %2) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %31 = "llvm.add"(%30, %13) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %32 = "x86vector.avx512.intr.vpmadd52h.uq.512"(%3, %6, %arg6) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %33 = "x86vector.avx512.intr.vpmadd52h.uq.512"(%32, %5, %arg7) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %34 = "llvm.shl"(%33, %2) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %35 = "llvm.add"(%34, %16) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %36 = "x86vector.avx512.intr.vpmadd52h.uq.512"(%3, %7, %arg6) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %37 = "x86vector.avx512.intr.vpmadd52h.uq.512"(%36, %6, %arg7) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %38 = "x86vector.avx512.intr.vpmadd52h.uq.512"(%37, %5, %arg8) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %39 = "llvm.shl"(%38, %2) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %40 = "llvm.add"(%39, %19) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %41 = "x86vector.avx512.intr.vpmadd52h.uq.512"(%3, %8, %arg6) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %42 = "x86vector.avx512.intr.vpmadd52h.uq.512"(%41, %7, %arg7) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %43 = "x86vector.avx512.intr.vpmadd52h.uq.512"(%42, %6, %arg8) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %44 = "llvm.shl"(%43, %2) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %45 = "llvm.add"(%44, %22) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %46 = "x86vector.avx512.intr.vpmadd52h.uq.512"(%3, %9, %arg6) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %47 = "x86vector.avx512.intr.vpmadd52h.uq.512"(%46, %8, %arg7) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %48 = "x86vector.avx512.intr.vpmadd52h.uq.512"(%47, %7, %arg8) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %49 = "llvm.shl"(%48, %2) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %50 = "llvm.add"(%49, %25) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %51 = "x86vector.avx512.intr.vpmadd52h.uq.512"(%3, %10, %arg6) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %52 = "x86vector.avx512.intr.vpmadd52h.uq.512"(%51, %9, %arg7) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %53 = "x86vector.avx512.intr.vpmadd52h.uq.512"(%52, %8, %arg8) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %54 = "llvm.shl"(%53, %2) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %55 = "llvm.add"(%54, %27) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %56 = "x86vector.avx512.intr.vpmadd52h.uq.512"(%3, %10, %arg7) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %57 = "x86vector.avx512.intr.vpmadd52h.uq.512"(%56, %9, %arg8) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %58 = "llvm.shl"(%57, %2) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %59 = "llvm.add"(%58, %28) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %60 = "x86vector.avx512.intr.vpmadd52h.uq.512"(%3, %10, %arg8) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %61 = "llvm.shl"(%60, %2) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %62 = "llvm.shufflevector"(%40, %4) <{mask = array<i32: 4, 5, 6, 7, 0, 1, 2, 3>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %63 = "llvm.shufflevector"(%45, %4) <{mask = array<i32: 4, 5, 6, 7, 0, 1, 2, 3>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %64 = "llvm.shufflevector"(%50, %4) <{mask = array<i32: 4, 5, 6, 7, 0, 1, 2, 3>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %65 = "llvm.add"(%62, %11) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %66 = "llvm.shufflevector"(%11, %65) <{mask = array<i32: 0, 1, 2, 3, 12, 13, 14, 15>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %67 = "llvm.add"(%63, %31) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %68 = "llvm.shufflevector"(%31, %67) <{mask = array<i32: 0, 1, 2, 3, 12, 13, 14, 15>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %69 = "llvm.add"(%64, %35) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %70 = "llvm.shufflevector"(%35, %69) <{mask = array<i32: 0, 1, 2, 3, 12, 13, 14, 15>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %71 = "llvm.add"(%55, %62) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %72 = "llvm.shufflevector"(%71, %55) <{mask = array<i32: 0, 1, 2, 3, 12, 13, 14, 15>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %73 = "llvm.add"(%59, %63) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %74 = "llvm.shufflevector"(%73, %59) <{mask = array<i32: 0, 1, 2, 3, 12, 13, 14, 15>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %75 = "llvm.add"(%61, %64) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %76 = "llvm.shufflevector"(%75, %61) <{mask = array<i32: 0, 1, 2, 3, 12, 13, 14, 15>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %77 = "llvm.shl"(%72, %1) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %78 = "llvm.add"(%77, %66) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %79 = "llvm.mul"(%72, %0) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %80 = "llvm.add"(%78, %79) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %81 = "llvm.shl"(%74, %1) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %82 = "llvm.add"(%81, %68) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %83 = "llvm.mul"(%74, %0) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %84 = "llvm.add"(%82, %83) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %85 = "llvm.shl"(%76, %1) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %86 = "llvm.add"(%85, %70) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %87 = "llvm.mul"(%76, %0) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %88 = "llvm.add"(%86, %87) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    "llvm.store"(%80, %arg0) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (vector<8xi64>, !llvm.ptr) -> ()
    "llvm.store"(%84, %arg1) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (vector<8xi64>, !llvm.ptr) -> ()
    "llvm.store"(%88, %arg2) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (vector<8xi64>, !llvm.ptr) -> ()
    "llvm.return"() : () -> ()
}
]

def fd_r43x6_quad_mul_fast := [sllvm_of| fd_r43x6_quad_mul_fast_region]

end Firedancer.Avx512
