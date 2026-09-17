/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
-- build/native/gcc/mlir_canonicalized/avx512/region/fd_r43x6_ge_decode2.mlir
import SSA.Projects.SLLVM.Cfg
import SSA.Projects.Firedancer.Avx512.Mlir.Util.wv_ld
import SSA.Projects.Firedancer.Avx512.Mlir.Field.fd_r43x6_unpack
import SSA.Projects.Firedancer.Avx512.Mlir.Field.fd_r43x6_diagnose
import SSA.Projects.Firedancer.Avx512.Mlir.Field.fd_r43x6_is_nonzero
import SSA.Projects.Firedancer.Avx512.Mlir.Field.fd_r43x6_pow22523_2

namespace Firedancer.Avx512
open LeanMLIR SLLVM

def fd_r43x6_ge_decode2_region : MLIR.AST.Region 0 := [mlir_region|
{
  ^bb0(%arg0: !llvm.ptr, %arg1: !llvm.ptr, %arg2: !llvm.ptr, %arg3: !llvm.ptr, %arg4: !llvm.ptr, %arg5: !llvm.ptr, %arg6: !llvm.ptr, %arg7: !llvm.ptr):
    %0 = "llvm.mlir.constant"() <{value = dense<[8796093022207, 8796093022207, 8796093022207, 8796093022207, 1099511627775, 1099511627775, 1099511627775, 1099511627775]> : vector<8xi64>}> : () -> vector<8xi64>
    %1 = "llvm.mlir.constant"() <{value = dense<8796093022207> : vector<8xi64>}> : () -> vector<8xi64>
    %2 = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
    %3 = "llvm.mlir.constant"() <{value = 6 : i32}> : () -> i32
    %4 = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
    %5 = "llvm.mlir.constant"() <{value = 4 : i32}> : () -> i32
    %6 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %7 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %8 = "llvm.mlir.constant"() <{value = 19 : i64}> : () -> i64
    %9 = "llvm.mlir.constant"() <{value = dense<[43, 43, 43, 43, 40, 40, 40, 40]> : vector<8xi64>}> : () -> vector<8xi64>
    %10 = "llvm.mlir.constant"() <{value = dense<43> : vector<8xi64>}> : () -> vector<8xi64>
    %11 = "llvm.mlir.constant"() <{value = dense<[2, 3, 10, 11, 6, 7, 12, 13]> : vector<8xi64>}> : () -> vector<8xi64>
    %12 = "llvm.mlir.constant"() <{value = dense<[0, 1, 8, 9, 4, 5, 12, 13]> : vector<8xi64>}> : () -> vector<8xi64>
    %13 = "llvm.mlir.constant"() <{value = dense<[3467281080496, 6582290652611, 5210002954932, 329084955603, 4526638806224, 373767602335, 0, 0]> : vector<8xi64>}> : () -> vector<8xi64>
    %14 = "llvm.mlir.constant"() <{value = -1 : i8}> : () -> i8
    %15 = "llvm.mlir.constant"() <{value = -2 : i32}> : () -> i32
    %16 = "llvm.mlir.constant"() <{value = -1 : i32}> : () -> i32
    %17 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %18 = "llvm.mlir.constant"() <{value = dense<[8795933638637, 8796091973631, 8796091973631, 8796091973631, 8796091973631, 1099510579199, 0, 0]> : vector<8xi64>}> : () -> vector<8xi64>
    %19 = "llvm.mlir.constant"() <{value = dense<[1, 0, 0, 0, 0, 0, 0, 0]> : vector<8xi64>}> : () -> vector<8xi64>
    %20 = "llvm.mlir.constant"() <{value = dense<[6365466163363, 253762649449, 7518893317, 260847760460, 7696165686388, 704489577558, 0, 0]> : vector<8xi64>}> : () -> vector<8xi64>
    %21 = "llvm.mlir.constant"() <{value = dense<[159383552, 1048576, 1048576, 1048576, 1048576, 1048576, 0, 0]> : vector<8xi64>}> : () -> vector<8xi64>
    %22 = "llvm.mlir.constant"() <{value = dense<[-1, 0, 0, 0, 0, 0, 0, 0]> : vector<8xi64>}> : () -> vector<8xi64>
    %23 = "llvm.mlir.constant"() <{value = dense<18> : vector<8xi64>}> : () -> vector<8xi64>
    %24 = "llvm.mlir.constant"() <{value = dense<0> : vector<8xi64>}> : () -> vector<8xi64>
    %25 = "llvm.mlir.constant"() <{value = dense<[5, 0, 1, 2, 3, 4, 8, 8]> : vector<8xi64>}> : () -> vector<8xi64>
    %26 = "llvm.mlir.constant"() <{value = dense<[8795933638636, 8796091973631, 8796091973631, 8796091973631, 8796091973631, 1099510579199, 0, 0]> : vector<8xi64>}> : () -> vector<8xi64>
    %27 = "llvm.mlir.constant"() <{value = dense<[19, 1, 1, 1, 1, 1, 0, 0]> : vector<8xi64>}> : () -> vector<8xi64>
    %28 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %29 = "llvm.mlir.constant"() <{value = 32 : i64}> : () -> i64
    %30 = "llvm.mlir.constant"() <{value = 63 : i64}> : () -> i64
    %31 = "llvm.mlir.constant"() <{value = 9223372036854775807 : i64}> : () -> i64
    %32 = "llvm.mlir.constant"() <{value = dense<[8796093022207, 8796093022207, 8796093022207, 8796093022207, 8796093022207, 1099511627775, 0, 0]> : vector<8xi64>}> : () -> vector<8xi64>
    %33 = "llvm.mlir.constant"() <{value = dense<[43, 43, 43, 43, 43, 40, 0, 0]> : vector<8xi64>}> : () -> vector<8xi64>
    %34 = "llvm.mlir.poison"() : () -> vector<8xi64>
    %35 = "llvm.mlir.poison"() : () -> i64
    %36 = "llvm.mlir.undef"() : () -> vector<8xi64>
    %37 = "llvm.insertelement"(%36, %35, %17) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %38 = "llvm.insertelement"(%37, %35, %28) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %39 = "llvm.insertelement"(%38, %35, %7) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %40 = "llvm.insertelement"(%39, %35, %6) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %41 = "llvm.insertelement"(%40, %8, %5) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %42 = "llvm.insertelement"(%41, %8, %4) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %43 = "llvm.insertelement"(%42, %8, %3) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %44 = "llvm.insertelement"(%43, %8, %2) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %45 = "llvm.alloca"(%28) <{alignment = 32 : i64, elem_type = !llvm.array<4 x i64>}> : (i32) -> !llvm.ptr
    %46 = "llvm.alloca"(%28) <{alignment = 32 : i64, elem_type = !llvm.array<4 x i64>}> : (i32) -> !llvm.ptr
    %47 = "llvm.alloca"(%28) <{alignment = 64 : i64, elem_type = vector<8xi64>}> : (i32) -> !llvm.ptr
    %48 = "llvm.alloca"(%28) <{alignment = 64 : i64, elem_type = vector<8xi64>}> : (i32) -> !llvm.ptr
    "llvm.intr.lifetime.start"(%45) <{size = 32 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%46) <{size = 32 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.memcpy"(%45, %arg3, %29) <{isVolatile = false}> : (!llvm.ptr, !llvm.ptr, i64) -> ()
    "llvm.intr.memcpy"(%46, %arg7, %29) <{isVolatile = false}> : (!llvm.ptr, !llvm.ptr, i64) -> ()
    %49 = "llvm.getelementptr"(%45) <{elem_type = !llvm.array<4 x i64>, inbounds, rawConstantIndices = array<i32: 0, 3>}> : (!llvm.ptr) -> !llvm.ptr
    %50 = "llvm.load"(%49) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    %51 = "llvm.getelementptr"(%46) <{elem_type = !llvm.array<4 x i64>, inbounds, rawConstantIndices = array<i32: 0, 3>}> : (!llvm.ptr) -> !llvm.ptr
    %52 = "llvm.load"(%51) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    %53 = "llvm.lshr"(%50, %30) : (i64, i64) -> i64
    %54 = "llvm.trunc"(%53) : (i64) -> i32
    %55 = "llvm.lshr"(%52, %30) : (i64, i64) -> i64
    %56 = "llvm.trunc"(%55) : (i64) -> i32
    %57 = "llvm.and"(%50, %31) : (i64, i64) -> i64
    %58 = "llvm.and"(%52, %31) : (i64, i64) -> i64
    "llvm.store"(%57, %49) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (i64, !llvm.ptr) -> ()
    "llvm.store"(%58, %51) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (i64, !llvm.ptr) -> ()
    %59 = "llvm.call"(%45) <{CConv = #llvm.cconv<fastcc>, callee = @wv_ld, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr) -> vector<4xi64>
    %60 = "llvm.call"(%59) <{CConv = #llvm.cconv<fastcc>, callee = @fd_r43x6_unpack, fastmathFlags = #llvm.fastmath<none>}> : (vector<4xi64>) -> vector<8xi64>
    %61 = "llvm.call"(%46) <{CConv = #llvm.cconv<fastcc>, callee = @wv_ld, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr) -> vector<4xi64>
    %62 = "llvm.call"(%61) <{CConv = #llvm.cconv<fastcc>, callee = @fd_r43x6_unpack, fastmathFlags = #llvm.fastmath<none>}> : (vector<4xi64>) -> vector<8xi64>
    %63 = "llvm.call"(%60) <{CConv = #llvm.cconv<fastcc>, callee = @fd_r43x6_sqr_fast, fastmathFlags = #llvm.fastmath<none>}> : (vector<8xi64>) -> vector<8xi64>
    %64 = "llvm.and"(%63, %32) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %65 = "llvm.lshr"(%63, %33) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %66 = "llvm.shufflevector"(%65, %34) <{mask = array<i32: 5, 0, 1, 2, 3, 4, 6, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %67 = "x86vector.avx512.intr.vpmadd52l.uq.512"(%64, %27, %66) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %68 = "llvm.call"(%62) <{CConv = #llvm.cconv<fastcc>, callee = @fd_r43x6_sqr_fast, fastmathFlags = #llvm.fastmath<none>}> : (vector<8xi64>) -> vector<8xi64>
    %69 = "llvm.and"(%68, %32) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %70 = "llvm.lshr"(%68, %33) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %71 = "llvm.shufflevector"(%70, %34) <{mask = array<i32: 5, 0, 1, 2, 3, 4, 6, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %72 = "x86vector.avx512.intr.vpmadd52l.uq.512"(%69, %27, %71) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %73 = "llvm.add"(%67, %26) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %74 = "llvm.and"(%73, %32) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %75 = "llvm.ashr"(%73, %33) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %76 = "x86vector.avx512.intr.vpermi2var.q.512"(%75, %25, %24) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %77 = "llvm.mul"(%76, %23) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %78 = "llvm.and"(%77, %22) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %79 = "llvm.add"(%76, %74) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %80 = "llvm.add"(%79, %78) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %81 = "llvm.add"(%80, %21) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %82 = "llvm.add"(%72, %26) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %83 = "llvm.and"(%82, %32) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %84 = "llvm.ashr"(%82, %33) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %85 = "x86vector.avx512.intr.vpermi2var.q.512"(%84, %25, %24) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %86 = "llvm.mul"(%85, %23) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %87 = "llvm.and"(%86, %22) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %88 = "llvm.add"(%83, %85) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %89 = "llvm.add"(%88, %87) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %90 = "llvm.add"(%89, %21) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %91 = "llvm.call"(%20, %67) <{CConv = #llvm.cconv<fastcc>, callee = @fd_r43x6_mul_fast, fastmathFlags = #llvm.fastmath<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %92 = "llvm.and"(%91, %32) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %93 = "llvm.lshr"(%91, %33) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %94 = "llvm.shufflevector"(%93, %34) <{mask = array<i32: 5, 0, 1, 2, 3, 4, 6, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %95 = "x86vector.avx512.intr.vpmadd52l.uq.512"(%92, %27, %94) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %96 = "llvm.add"(%95, %19) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %97 = "llvm.call"(%20, %72) <{CConv = #llvm.cconv<fastcc>, callee = @fd_r43x6_mul_fast, fastmathFlags = #llvm.fastmath<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %98 = "llvm.and"(%97, %32) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %99 = "llvm.lshr"(%97, %33) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %100 = "llvm.shufflevector"(%99, %34) <{mask = array<i32: 5, 0, 1, 2, 3, 4, 6, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %101 = "x86vector.avx512.intr.vpmadd52l.uq.512"(%98, %27, %100) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %102 = "llvm.add"(%101, %19) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %103 = "llvm.call"(%96) <{CConv = #llvm.cconv<fastcc>, callee = @fd_r43x6_sqr_fast, fastmathFlags = #llvm.fastmath<none>}> : (vector<8xi64>) -> vector<8xi64>
    %104 = "llvm.and"(%103, %32) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %105 = "llvm.lshr"(%103, %33) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %106 = "llvm.shufflevector"(%105, %34) <{mask = array<i32: 5, 0, 1, 2, 3, 4, 6, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %107 = "x86vector.avx512.intr.vpmadd52l.uq.512"(%104, %27, %106) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %108 = "llvm.call"(%102) <{CConv = #llvm.cconv<fastcc>, callee = @fd_r43x6_sqr_fast, fastmathFlags = #llvm.fastmath<none>}> : (vector<8xi64>) -> vector<8xi64>
    %109 = "llvm.and"(%108, %32) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %110 = "llvm.lshr"(%108, %33) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %111 = "llvm.shufflevector"(%110, %34) <{mask = array<i32: 5, 0, 1, 2, 3, 4, 6, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %112 = "x86vector.avx512.intr.vpmadd52l.uq.512"(%109, %27, %111) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %113 = "llvm.call"(%107) <{CConv = #llvm.cconv<fastcc>, callee = @fd_r43x6_sqr_fast, fastmathFlags = #llvm.fastmath<none>}> : (vector<8xi64>) -> vector<8xi64>
    %114 = "llvm.and"(%113, %32) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %115 = "llvm.lshr"(%113, %33) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %116 = "llvm.shufflevector"(%115, %34) <{mask = array<i32: 5, 0, 1, 2, 3, 4, 6, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %117 = "x86vector.avx512.intr.vpmadd52l.uq.512"(%114, %27, %116) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %118 = "llvm.call"(%112) <{CConv = #llvm.cconv<fastcc>, callee = @fd_r43x6_sqr_fast, fastmathFlags = #llvm.fastmath<none>}> : (vector<8xi64>) -> vector<8xi64>
    %119 = "llvm.and"(%118, %32) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %120 = "llvm.lshr"(%118, %33) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %121 = "llvm.shufflevector"(%120, %34) <{mask = array<i32: 5, 0, 1, 2, 3, 4, 6, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %122 = "x86vector.avx512.intr.vpmadd52l.uq.512"(%119, %27, %121) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %123 = "llvm.call"(%96, %107) <{CConv = #llvm.cconv<fastcc>, callee = @fd_r43x6_mul_fast, fastmathFlags = #llvm.fastmath<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %124 = "llvm.and"(%123, %32) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %125 = "llvm.lshr"(%123, %33) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %126 = "llvm.shufflevector"(%125, %34) <{mask = array<i32: 5, 0, 1, 2, 3, 4, 6, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %127 = "x86vector.avx512.intr.vpmadd52l.uq.512"(%124, %27, %126) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %128 = "llvm.call"(%102, %112) <{CConv = #llvm.cconv<fastcc>, callee = @fd_r43x6_mul_fast, fastmathFlags = #llvm.fastmath<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %129 = "llvm.and"(%128, %32) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %130 = "llvm.lshr"(%128, %33) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %131 = "llvm.shufflevector"(%130, %34) <{mask = array<i32: 5, 0, 1, 2, 3, 4, 6, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %132 = "x86vector.avx512.intr.vpmadd52l.uq.512"(%129, %27, %131) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %133 = "llvm.call"(%81, %127) <{CConv = #llvm.cconv<fastcc>, callee = @fd_r43x6_mul_fast, fastmathFlags = #llvm.fastmath<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %134 = "llvm.and"(%133, %32) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %135 = "llvm.lshr"(%133, %33) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %136 = "llvm.shufflevector"(%135, %34) <{mask = array<i32: 5, 0, 1, 2, 3, 4, 6, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %137 = "x86vector.avx512.intr.vpmadd52l.uq.512"(%134, %27, %136) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %138 = "llvm.call"(%90, %132) <{CConv = #llvm.cconv<fastcc>, callee = @fd_r43x6_mul_fast, fastmathFlags = #llvm.fastmath<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %139 = "llvm.and"(%138, %32) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %140 = "llvm.lshr"(%138, %33) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %141 = "llvm.shufflevector"(%140, %34) <{mask = array<i32: 5, 0, 1, 2, 3, 4, 6, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %142 = "x86vector.avx512.intr.vpmadd52l.uq.512"(%139, %27, %141) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %143 = "llvm.call"(%137, %117) <{CConv = #llvm.cconv<fastcc>, callee = @fd_r43x6_mul_fast, fastmathFlags = #llvm.fastmath<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %144 = "llvm.and"(%143, %32) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %145 = "llvm.lshr"(%143, %33) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %146 = "llvm.shufflevector"(%145, %34) <{mask = array<i32: 5, 0, 1, 2, 3, 4, 6, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %147 = "x86vector.avx512.intr.vpmadd52l.uq.512"(%144, %27, %146) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %148 = "llvm.call"(%142, %122) <{CConv = #llvm.cconv<fastcc>, callee = @fd_r43x6_mul_fast, fastmathFlags = #llvm.fastmath<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %149 = "llvm.and"(%148, %32) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %150 = "llvm.lshr"(%148, %33) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %151 = "llvm.shufflevector"(%150, %34) <{mask = array<i32: 5, 0, 1, 2, 3, 4, 6, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %152 = "x86vector.avx512.intr.vpmadd52l.uq.512"(%149, %27, %151) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    "llvm.intr.lifetime.start"(%47) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%48) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.call"(%47, %147, %48, %152) <{CConv = #llvm.cconv<ccc>, callee = @fd_r43x6_pow22523_2, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, vector<8xi64>, !llvm.ptr, vector<8xi64>) -> ()
    %153 = "llvm.load"(%47) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %154 = "llvm.load"(%48) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    "llvm.intr.lifetime.end"(%48) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%47) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    %155 = "llvm.call"(%137, %153) <{CConv = #llvm.cconv<fastcc>, callee = @fd_r43x6_mul_fast, fastmathFlags = #llvm.fastmath<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %156 = "llvm.and"(%155, %32) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %157 = "llvm.lshr"(%155, %33) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %158 = "llvm.shufflevector"(%157, %34) <{mask = array<i32: 5, 0, 1, 2, 3, 4, 6, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %159 = "x86vector.avx512.intr.vpmadd52l.uq.512"(%156, %27, %158) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %160 = "llvm.call"(%142, %154) <{CConv = #llvm.cconv<fastcc>, callee = @fd_r43x6_mul_fast, fastmathFlags = #llvm.fastmath<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %161 = "llvm.and"(%160, %32) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %162 = "llvm.lshr"(%160, %33) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %163 = "llvm.shufflevector"(%162, %34) <{mask = array<i32: 5, 0, 1, 2, 3, 4, 6, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %164 = "x86vector.avx512.intr.vpmadd52l.uq.512"(%161, %27, %163) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %165 = "llvm.call"(%159) <{CConv = #llvm.cconv<fastcc>, callee = @fd_r43x6_sqr_fast, fastmathFlags = #llvm.fastmath<none>}> : (vector<8xi64>) -> vector<8xi64>
    %166 = "llvm.and"(%165, %32) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %167 = "llvm.lshr"(%165, %33) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %168 = "llvm.shufflevector"(%167, %34) <{mask = array<i32: 5, 0, 1, 2, 3, 4, 6, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %169 = "x86vector.avx512.intr.vpmadd52l.uq.512"(%166, %27, %168) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %170 = "llvm.call"(%164) <{CConv = #llvm.cconv<fastcc>, callee = @fd_r43x6_sqr_fast, fastmathFlags = #llvm.fastmath<none>}> : (vector<8xi64>) -> vector<8xi64>
    %171 = "llvm.and"(%170, %32) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %172 = "llvm.lshr"(%170, %33) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %173 = "llvm.shufflevector"(%172, %34) <{mask = array<i32: 5, 0, 1, 2, 3, 4, 6, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %174 = "x86vector.avx512.intr.vpmadd52l.uq.512"(%171, %27, %173) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %175 = "llvm.call"(%96, %169) <{CConv = #llvm.cconv<fastcc>, callee = @fd_r43x6_mul_fast, fastmathFlags = #llvm.fastmath<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %176 = "llvm.and"(%175, %32) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %177 = "llvm.lshr"(%175, %33) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %178 = "llvm.shufflevector"(%177, %34) <{mask = array<i32: 5, 0, 1, 2, 3, 4, 6, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %179 = "x86vector.avx512.intr.vpmadd52l.uq.512"(%176, %27, %178) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %180 = "llvm.call"(%102, %174) <{CConv = #llvm.cconv<fastcc>, callee = @fd_r43x6_mul_fast, fastmathFlags = #llvm.fastmath<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %181 = "llvm.and"(%180, %32) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %182 = "llvm.lshr"(%180, %33) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %183 = "llvm.shufflevector"(%182, %34) <{mask = array<i32: 5, 0, 1, 2, 3, 4, 6, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %184 = "x86vector.avx512.intr.vpmadd52l.uq.512"(%181, %27, %183) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %185 = "llvm.sub"(%179, %80) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %186 = "llvm.add"(%185, %18) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %187 = "llvm.sub"(%184, %89) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %188 = "llvm.add"(%187, %18) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %189 = "llvm.add"(%179, %81) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %190 = "llvm.call"(%186) <{CConv = #llvm.cconv<fastcc>, callee = @fd_r43x6_is_nonzero, fastmathFlags = #llvm.fastmath<none>}> : (vector<8xi64>) -> i32
    %191 = "llvm.call"(%188) <{CConv = #llvm.cconv<fastcc>, callee = @fd_r43x6_is_nonzero, fastmathFlags = #llvm.fastmath<none>}> : (vector<8xi64>) -> i32
    %192 = "llvm.call"(%189) <{CConv = #llvm.cconv<fastcc>, callee = @fd_r43x6_is_nonzero, fastmathFlags = #llvm.fastmath<none>}> : (vector<8xi64>) -> i32
    %193 = "llvm.and"(%192, %190) : (i32, i32) -> i32
    %194 = "llvm.icmp"(%193, %17) <{predicate = 0 : i64}> : (i32, i32) -> i1
    "llvm.cond_br"(%194)[^bb1, ^bb3] <{branch_weights = array<i32: 2000, 1>, operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
  ^bb1:  // pred: ^bb0
    %195 = "llvm.add"(%184, %90) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %196 = "llvm.call"(%195) <{CConv = #llvm.cconv<fastcc>, callee = @fd_r43x6_is_nonzero, fastmathFlags = #llvm.fastmath<none>}> : (vector<8xi64>) -> i32
    %197 = "llvm.and"(%196, %191) : (i32, i32) -> i32
    %198 = "llvm.icmp"(%197, %17) <{predicate = 0 : i64}> : (i32, i32) -> i1
    "llvm.cond_br"(%198)[^bb2, ^bb4] <{branch_weights = array<i32: 2000, 1>, operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
  ^bb2:  // pred: ^bb1
    %199 = "llvm.trunc"(%190) : (i32) -> i8
    %200 = "llvm.add"(%199, %14) <{overflowFlags = #llvm.overflow<nsw>}> : (i8, i8) -> i8
    %201 = "llvm.bitcast"(%200) : (i8) -> vector<8xi1>
    %202 = "llvm.select"(%201, %19, %13) <{fastmathFlags = #llvm.fastmath<none>}> : (vector<8xi1>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %203 = "llvm.trunc"(%191) : (i32) -> i8
    %204 = "llvm.add"(%203, %14) <{overflowFlags = #llvm.overflow<nsw>}> : (i8, i8) -> i8
    %205 = "llvm.bitcast"(%204) : (i8) -> vector<8xi1>
    %206 = "llvm.select"(%205, %19, %13) <{fastmathFlags = #llvm.fastmath<none>}> : (vector<8xi1>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %207 = "llvm.call"(%159, %202) <{CConv = #llvm.cconv<fastcc>, callee = @fd_r43x6_mul_fast, fastmathFlags = #llvm.fastmath<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %208 = "llvm.and"(%207, %32) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %209 = "llvm.lshr"(%207, %33) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %210 = "llvm.shufflevector"(%209, %34) <{mask = array<i32: 5, 0, 1, 2, 3, 4, 6, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %211 = "x86vector.avx512.intr.vpmadd52l.uq.512"(%208, %27, %210) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %212 = "llvm.call"(%164, %206) <{CConv = #llvm.cconv<fastcc>, callee = @fd_r43x6_mul_fast, fastmathFlags = #llvm.fastmath<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %213 = "llvm.and"(%212, %32) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %214 = "llvm.lshr"(%212, %33) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %215 = "llvm.shufflevector"(%214, %34) <{mask = array<i32: 5, 0, 1, 2, 3, 4, 6, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %216 = "x86vector.avx512.intr.vpmadd52l.uq.512"(%213, %27, %215) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %217 = "llvm.call"(%211) <{CConv = #llvm.cconv<fastcc>, callee = @fd_r43x6_diagnose, fastmathFlags = #llvm.fastmath<none>}> : (vector<8xi64>) -> i32
    %218 = "llvm.call"(%216) <{CConv = #llvm.cconv<fastcc>, callee = @fd_r43x6_diagnose, fastmathFlags = #llvm.fastmath<none>}> : (vector<8xi64>) -> i32
    %219 = "llvm.icmp"(%217, %54) <{predicate = 0 : i64}> : (i32, i32) -> i1
    %220 = "llvm.sext"(%219) : (i1) -> i8
    %221 = "llvm.sub"(%18, %211) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %222 = "llvm.and"(%221, %32) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %223 = "llvm.ashr"(%221, %33) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %224 = "x86vector.avx512.intr.vpermi2var.q.512"(%223, %25, %24) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %225 = "llvm.mul"(%224, %23) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %226 = "llvm.and"(%225, %22) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %227 = "llvm.add"(%222, %21) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %228 = "llvm.add"(%227, %224) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %229 = "llvm.add"(%228, %226) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %230 = "llvm.bitcast"(%220) : (i8) -> vector<8xi1>
    %231 = "llvm.select"(%230, %211, %229) <{fastmathFlags = #llvm.fastmath<none>}> : (vector<8xi1>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %232 = "llvm.icmp"(%218, %56) <{predicate = 0 : i64}> : (i32, i32) -> i1
    %233 = "llvm.sext"(%232) : (i1) -> i8
    %234 = "llvm.sub"(%18, %216) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %235 = "llvm.and"(%234, %32) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %236 = "llvm.ashr"(%234, %33) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %237 = "x86vector.avx512.intr.vpermi2var.q.512"(%236, %25, %24) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %238 = "llvm.mul"(%237, %23) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %239 = "llvm.and"(%238, %22) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %240 = "llvm.add"(%235, %21) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %241 = "llvm.add"(%240, %237) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %242 = "llvm.add"(%241, %239) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %243 = "llvm.bitcast"(%233) : (i8) -> vector<8xi1>
    %244 = "llvm.select"(%243, %216, %242) <{fastmathFlags = #llvm.fastmath<none>}> : (vector<8xi1>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %245 = "llvm.call"(%231, %60) <{CConv = #llvm.cconv<fastcc>, callee = @fd_r43x6_mul_fast, fastmathFlags = #llvm.fastmath<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %246 = "llvm.and"(%245, %32) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %247 = "llvm.lshr"(%245, %33) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %248 = "llvm.shufflevector"(%247, %34) <{mask = array<i32: 5, 0, 1, 2, 3, 4, 6, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %249 = "x86vector.avx512.intr.vpmadd52l.uq.512"(%246, %27, %248) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %250 = "llvm.call"(%244, %62) <{CConv = #llvm.cconv<fastcc>, callee = @fd_r43x6_mul_fast, fastmathFlags = #llvm.fastmath<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %251 = "llvm.and"(%250, %32) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %252 = "llvm.lshr"(%250, %33) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %253 = "llvm.shufflevector"(%252, %34) <{mask = array<i32: 5, 0, 1, 2, 3, 4, 6, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %254 = "x86vector.avx512.intr.vpmadd52l.uq.512"(%251, %27, %253) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %255 = "x86vector.avx512.intr.vpermi2var.q.512"(%231, %12, %19) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %256 = "x86vector.avx512.intr.vpermi2var.q.512"(%60, %12, %249) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %257 = "x86vector.avx512.intr.vpermi2var.q.512"(%231, %11, %19) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %258 = "x86vector.avx512.intr.vpermi2var.q.512"(%60, %11, %249) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %259 = "llvm.shufflevector"(%255, %256) <{mask = array<i32: 0, 8, 2, 10, 4, 12, 6, 14>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %260 = "llvm.shufflevector"(%255, %256) <{mask = array<i32: 1, 9, 3, 11, 5, 13, 7, 15>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %261 = "llvm.shufflevector"(%257, %258) <{mask = array<i32: 0, 8, 2, 10, -1, -1, -1, -1>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %262 = "llvm.shufflevector"(%257, %258) <{mask = array<i32: 1, 9, 3, 11, -1, -1, -1, -1>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %263 = "llvm.shufflevector"(%259, %262) <{mask = array<i32: 0, 1, 2, 3, 8, 9, 10, 11>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    "llvm.store"(%263, %arg0) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (vector<8xi64>, !llvm.ptr) -> ()
    %264 = "llvm.shufflevector"(%260, %259) <{mask = array<i32: 0, 1, 2, 3, 12, 13, 14, 15>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    "llvm.store"(%264, %arg1) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (vector<8xi64>, !llvm.ptr) -> ()
    %265 = "llvm.shufflevector"(%261, %260) <{mask = array<i32: 0, 1, 2, 3, 12, 13, 14, 15>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    "llvm.store"(%265, %arg2) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (vector<8xi64>, !llvm.ptr) -> ()
    %266 = "x86vector.avx512.intr.vpermi2var.q.512"(%244, %12, %19) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %267 = "x86vector.avx512.intr.vpermi2var.q.512"(%62, %12, %254) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %268 = "x86vector.avx512.intr.vpermi2var.q.512"(%244, %11, %19) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %269 = "x86vector.avx512.intr.vpermi2var.q.512"(%62, %11, %254) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %270 = "llvm.shufflevector"(%266, %267) <{mask = array<i32: 0, 8, 2, 10, 4, 12, 6, 14>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %271 = "llvm.shufflevector"(%266, %267) <{mask = array<i32: 1, 9, 3, 11, 5, 13, 7, 15>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %272 = "llvm.shufflevector"(%268, %269) <{mask = array<i32: 0, 8, 2, 10, -1, -1, -1, -1>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %273 = "llvm.shufflevector"(%268, %269) <{mask = array<i32: 1, 9, 3, 11, -1, -1, -1, -1>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %274 = "llvm.shufflevector"(%270, %273) <{mask = array<i32: 0, 1, 2, 3, 8, 9, 10, 11>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    "llvm.store"(%274, %arg4) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (vector<8xi64>, !llvm.ptr) -> ()
    %275 = "llvm.shufflevector"(%271, %270) <{mask = array<i32: 0, 1, 2, 3, 12, 13, 14, 15>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    "llvm.store"(%275, %arg5) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (vector<8xi64>, !llvm.ptr) -> ()
    %276 = "llvm.shufflevector"(%272, %271) <{mask = array<i32: 0, 1, 2, 3, 12, 13, 14, 15>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    "llvm.store"(%276, %arg6) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (vector<8xi64>, !llvm.ptr) -> ()
    %277 = "llvm.load"(%arg0) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %278 = "llvm.lshr"(%277, %10) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %279 = "llvm.load"(%arg1) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %280 = "llvm.lshr"(%279, %10) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %281 = "llvm.load"(%arg2) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %282 = "llvm.lshr"(%281, %9) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %283 = "llvm.mul"(%282, %44) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %284 = "llvm.and"(%277, %1) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %285 = "llvm.shufflevector"(%283, %282) <{mask = array<i32: 4, 5, 6, 7, 8, 9, 10, 11>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %286 = "llvm.add"(%285, %284) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    "llvm.store"(%286, %arg0) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (vector<8xi64>, !llvm.ptr) -> ()
    %287 = "llvm.load"(%arg1) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %288 = "llvm.and"(%287, %1) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %289 = "llvm.add"(%288, %278) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    "llvm.store"(%289, %arg1) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (vector<8xi64>, !llvm.ptr) -> ()
    %290 = "llvm.load"(%arg2) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %291 = "llvm.and"(%290, %0) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %292 = "llvm.add"(%291, %280) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    "llvm.store"(%292, %arg2) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (vector<8xi64>, !llvm.ptr) -> ()
    %293 = "llvm.load"(%arg4) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %294 = "llvm.lshr"(%293, %10) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %295 = "llvm.load"(%arg5) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %296 = "llvm.lshr"(%295, %10) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %297 = "llvm.load"(%arg6) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %298 = "llvm.lshr"(%297, %9) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %299 = "llvm.mul"(%298, %44) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %300 = "llvm.and"(%293, %1) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %301 = "llvm.shufflevector"(%299, %298) <{mask = array<i32: 4, 5, 6, 7, 8, 9, 10, 11>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %302 = "llvm.add"(%301, %300) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    "llvm.store"(%302, %arg4) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (vector<8xi64>, !llvm.ptr) -> ()
    %303 = "llvm.load"(%arg5) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %304 = "llvm.and"(%303, %1) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %305 = "llvm.add"(%304, %294) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    "llvm.store"(%305, %arg5) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (vector<8xi64>, !llvm.ptr) -> ()
    %306 = "llvm.load"(%arg6) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %307 = "llvm.and"(%306, %0) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %308 = "llvm.add"(%307, %296) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    "llvm.br"(%308, %17)[^bb5] : (vector<8xi64>, i32) -> ()
  ^bb3:  // pred: ^bb0
    "llvm.store"(%24, %arg0) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (vector<8xi64>, !llvm.ptr) -> ()
    "llvm.store"(%24, %arg4) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (vector<8xi64>, !llvm.ptr) -> ()
    "llvm.store"(%24, %arg1) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (vector<8xi64>, !llvm.ptr) -> ()
    "llvm.store"(%24, %arg5) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (vector<8xi64>, !llvm.ptr) -> ()
    "llvm.store"(%24, %arg2) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (vector<8xi64>, !llvm.ptr) -> ()
    "llvm.br"(%24, %16)[^bb5] : (vector<8xi64>, i32) -> ()
  ^bb4:  // pred: ^bb1
    "llvm.store"(%24, %arg0) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (vector<8xi64>, !llvm.ptr) -> ()
    "llvm.store"(%24, %arg4) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (vector<8xi64>, !llvm.ptr) -> ()
    "llvm.store"(%24, %arg1) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (vector<8xi64>, !llvm.ptr) -> ()
    "llvm.store"(%24, %arg5) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (vector<8xi64>, !llvm.ptr) -> ()
    "llvm.store"(%24, %arg2) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (vector<8xi64>, !llvm.ptr) -> ()
    "llvm.br"(%24, %15)[^bb5] : (vector<8xi64>, i32) -> ()
  ^bb5(%309: vector<8xi64>, %310: i32):  // 3 preds: ^bb2, ^bb3, ^bb4
    "llvm.store"(%309, %arg6) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (vector<8xi64>, !llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%46) <{size = 32 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%45) <{size = 32 : i64}> : (!llvm.ptr) -> ()
    "llvm.return"(%310) : (i32) -> ()
}
]

set_option maxHeartbeats 1000000 in
sllvm_cfg_def fd_r43x6_ge_decode2 :
    Cfg (Ctxt.ofList [SLLVM.Ty.ptr, SLLVM.Ty.ptr, SLLVM.Ty.ptr, SLLVM.Ty.ptr,
      SLLVM.Ty.ptr, SLLVM.Ty.ptr, SLLVM.Ty.ptr, SLLVM.Ty.ptr]) [SLLVM.Ty.bitvec 32] :=
  [sllvm_cfg_of| fd_r43x6_ge_decode2_region with
    @wv_ld := wv_ld,
    @fd_r43x6_unpack := fd_r43x6_unpack_cfg,
    @fd_r43x6_diagnose := fd_r43x6_diagnose_cfg,
    @fd_r43x6_is_nonzero := fd_r43x6_is_nonzero_cfg,
    @fd_r43x6_sqr_fast := fd_r43x6_sqr_fast_cfg,
    @fd_r43x6_mul_fast := fd_r43x6_mul_fast_cfg,
    @fd_r43x6_pow22523_2 := fd_r43x6_pow22523_2,
    @fd_long_if := fd_long_if_cfg,
    @fd_int_if := fd_int_if_cfg]

end Firedancer.Avx512
