/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
-- build/native/gcc/mlir_canonicalized/avx512/region/fd_r43x6_quad_sqr_fast.mlir
import SSA.Projects.SLLVM.Dialect

namespace Firedancer.Avx512
open LeanMLIR SLLVM

def fd_r43x6_quad_sqr_fast := [sllvm|
{
  ^bb0(%arg0: !llvm.ptr, %arg1: !llvm.ptr, %arg2: !llvm.ptr, %arg3: vector<8xi64>, %arg4: vector<8xi64>, %arg5: vector<8xi64>):
    %0 = "llvm.mlir.constant"() <{value = dense<24> : vector<8xi64>}> : () -> vector<8xi64>
    %1 = "llvm.mlir.constant"() <{value = dense<7> : vector<8xi64>}> : () -> vector<8xi64>
    %2 = "llvm.mlir.constant"() <{value = dense<9> : vector<8xi64>}> : () -> vector<8xi64>
    %3 = "llvm.mlir.constant"() <{value = dense<0> : vector<8xi64>}> : () -> vector<8xi64>
    %4 = "llvm.mlir.constant"() <{value = dense<1> : vector<8xi64>}> : () -> vector<8xi64>
    %5 = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
    %6 = "llvm.mlir.constant"() <{value = 6 : i32}> : () -> i32
    %7 = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
    %8 = "llvm.mlir.constant"() <{value = 4 : i32}> : () -> i32
    %9 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %10 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %11 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %12 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %13 = "llvm.mlir.constant"() <{value = 0 : i64}> : () -> i64
    %14 = "llvm.mlir.poison"() : () -> vector<8xi64>
    %15 = "llvm.mlir.poison"() : () -> i64
    %16 = "llvm.mlir.undef"() : () -> vector<8xi64>
    %17 = "llvm.insertelement"(%16, %13, %12) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %18 = "llvm.insertelement"(%17, %13, %11) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %19 = "llvm.insertelement"(%18, %13, %10) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %20 = "llvm.insertelement"(%19, %13, %9) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %21 = "llvm.insertelement"(%20, %15, %8) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %22 = "llvm.insertelement"(%21, %15, %7) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %23 = "llvm.insertelement"(%22, %15, %6) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %24 = "llvm.insertelement"(%23, %15, %5) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %25 = "llvm.mlir.undef"() : () -> vector<8xi64>
    %26 = "llvm.insertelement"(%25, %15, %12) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %27 = "llvm.insertelement"(%26, %15, %11) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %28 = "llvm.insertelement"(%27, %15, %10) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %29 = "llvm.insertelement"(%28, %15, %9) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %30 = "llvm.insertelement"(%29, %13, %8) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %31 = "llvm.insertelement"(%30, %13, %7) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %32 = "llvm.insertelement"(%31, %13, %6) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %33 = "llvm.insertelement"(%32, %13, %5) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %34 = "llvm.shufflevector"(%arg3, %arg5) <{mask = array<i32: 0, 1, 2, 3, 12, 13, 14, 15>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %35 = "llvm.shufflevector"(%arg4, %arg5) <{mask = array<i32: 0, 1, 2, 3, 8, 9, 10, 11>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %36 = "llvm.shufflevector"(%arg3, %arg4) <{mask = array<i32: 4, 5, 6, 7, 12, 13, 14, 15>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %37 = "llvm.shufflevector"(%arg4, %14) <{mask = array<i32: 4, 5, 6, 7, 0, 1, 2, 3>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %38 = "llvm.shufflevector"(%arg5, %arg3) <{mask = array<i32: 0, 1, 2, 3, 12, 13, 14, 15>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %39 = "llvm.shufflevector"(%arg5, %14) <{mask = array<i32: 4, 5, 6, 7, 0, 1, 2, 3>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %40 = "llvm.shufflevector"(%arg4, %24) <{mask = array<i32: 4, 5, 6, 7, 8, 9, 10, 11>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %41 = "llvm.shl"(%arg3, %4) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %42 = "llvm.shl"(%arg4, %4) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %43 = "llvm.shl"(%34, %4) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %44 = "llvm.shl"(%35, %4) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %45 = "x86vector.avx512.intr.vpmadd52l.uq.512"(%3, %34, %34) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %46 = "x86vector.avx512.intr.vpmadd52l.uq.512"(%3, %43, %arg4) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %47 = "x86vector.avx512.intr.vpmadd52l.uq.512"(%3, %arg4, %arg4) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %48 = "x86vector.avx512.intr.vpmadd52l.uq.512"(%47, %41, %arg5) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %49 = "x86vector.avx512.intr.vpmadd52l.uq.512"(%3, %41, %36) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %50 = "x86vector.avx512.intr.vpmadd52l.uq.512"(%49, %44, %arg5) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %51 = "x86vector.avx512.intr.vpmadd52l.uq.512"(%3, %38, %38) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %52 = "x86vector.avx512.intr.vpmadd52l.uq.512"(%51, %43, %37) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %53 = "x86vector.avx512.intr.vpmadd52l.uq.512"(%52, %44, %36) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %54 = "x86vector.avx512.intr.vpmadd52l.uq.512"(%3, %41, %39) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %55 = "x86vector.avx512.intr.vpmadd52l.uq.512"(%54, %42, %40) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %56 = "x86vector.avx512.intr.vpmadd52h.uq.512"(%3, %34, %34) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %57 = "llvm.shl"(%56, %2) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %58 = "x86vector.avx512.intr.vpmadd52h.uq.512"(%3, %43, %arg4) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %59 = "llvm.shl"(%58, %2) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %60 = "x86vector.avx512.intr.vpmadd52h.uq.512"(%3, %arg4, %arg4) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %61 = "x86vector.avx512.intr.vpmadd52h.uq.512"(%60, %41, %arg5) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %62 = "llvm.shl"(%61, %2) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %63 = "x86vector.avx512.intr.vpmadd52h.uq.512"(%3, %41, %36) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %64 = "x86vector.avx512.intr.vpmadd52h.uq.512"(%63, %44, %arg5) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %65 = "llvm.shl"(%64, %2) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %66 = "x86vector.avx512.intr.vpmadd52h.uq.512"(%3, %38, %38) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %67 = "x86vector.avx512.intr.vpmadd52h.uq.512"(%66, %43, %37) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %68 = "x86vector.avx512.intr.vpmadd52h.uq.512"(%67, %44, %36) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %69 = "llvm.shl"(%68, %2) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %70 = "x86vector.avx512.intr.vpmadd52h.uq.512"(%3, %41, %39) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %71 = "x86vector.avx512.intr.vpmadd52h.uq.512"(%70, %42, %40) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %72 = "llvm.shl"(%71, %2) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %73 = "llvm.shufflevector"(%45, %50) <{mask = array<i32: 0, 1, 2, 3, 8, 9, 10, 11>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %74 = "llvm.shufflevector"(%24, %62) <{mask = array<i32: 0, 1, 2, 3, 8, 9, 10, 11>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %75 = "llvm.add"(%74, %73) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %76 = "llvm.shufflevector"(%46, %53) <{mask = array<i32: 0, 1, 2, 3, 8, 9, 10, 11>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %77 = "llvm.shufflevector"(%57, %65) <{mask = array<i32: 0, 1, 2, 3, 8, 9, 10, 11>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %78 = "llvm.add"(%77, %76) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %79 = "llvm.shufflevector"(%48, %55) <{mask = array<i32: 0, 1, 2, 3, 8, 9, 10, 11>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %80 = "llvm.shufflevector"(%59, %69) <{mask = array<i32: 0, 1, 2, 3, 8, 9, 10, 11>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %81 = "llvm.shufflevector"(%24, %55) <{mask = array<i32: 0, 1, 2, 3, 12, 13, 14, 15>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %82 = "llvm.shufflevector"(%53, %46) <{mask = array<i32: 4, 5, 6, 7, 12, 13, 14, 15>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %83 = "llvm.shufflevector"(%72, %62) <{mask = array<i32: 4, 5, 6, 7, 12, 13, 14, 15>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %84 = "llvm.add"(%83, %82) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %85 = "llvm.shufflevector"(%72, %33) <{mask = array<i32: 0, 1, 2, 3, 12, 13, 14, 15>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %86 = "llvm.add"(%84, %85) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %87 = "llvm.shufflevector"(%50, %45) <{mask = array<i32: 4, 5, 6, 7, 12, 13, 14, 15>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %88 = "llvm.shufflevector"(%69, %59) <{mask = array<i32: 4, 5, 6, 7, 12, 13, 14, 15>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %89 = "llvm.add"(%88, %87) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %90 = "llvm.shufflevector"(%48, %33) <{mask = array<i32: 4, 5, 6, 7, 12, 13, 14, 15>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %91 = "llvm.shufflevector"(%65, %57) <{mask = array<i32: 4, 5, 6, 7, 12, 13, 14, 15>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %92 = "llvm.add"(%91, %90) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %93 = "llvm.shl"(%86, %1) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %94 = "llvm.add"(%75, %93) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %95 = "llvm.mul"(%86, %0) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %96 = "llvm.add"(%94, %95) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %97 = "llvm.shl"(%89, %1) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %98 = "llvm.add"(%78, %97) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %99 = "llvm.mul"(%89, %0) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %100 = "llvm.add"(%98, %99) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %101 = "llvm.shl"(%92, %1) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %102 = "llvm.mul"(%92, %0) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %103 = "llvm.add"(%81, %79) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %104 = "llvm.add"(%103, %101) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %105 = "llvm.add"(%104, %102) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %106 = "llvm.add"(%105, %80) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    "llvm.store"(%96, %arg0) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (vector<8xi64>, !llvm.ptr) -> ()
    "llvm.store"(%100, %arg1) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (vector<8xi64>, !llvm.ptr) -> ()
    "llvm.store"(%106, %arg2) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (vector<8xi64>, !llvm.ptr) -> ()
    "llvm.return"() : () -> ()
}
]

end Firedancer.Avx512
