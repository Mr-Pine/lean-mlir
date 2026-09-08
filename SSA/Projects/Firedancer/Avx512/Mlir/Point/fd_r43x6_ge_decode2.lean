/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.SLLVM.Cfg
import SSA.Projects.Firedancer.Avx512.Mlir.Util.wv_ld
import SSA.Projects.Firedancer.Avx512.Mlir.Field.fd_r43x6_unpack
import SSA.Projects.Firedancer.Avx512.Mlir.Field.fd_r43x6_diagnose
import SSA.Projects.Firedancer.Avx512.Mlir.Field.fd_r43x6_is_nonzero
import SSA.Projects.Firedancer.Avx512.Mlir.Field.fd_r43x6_pow22523_2

/-!
# `fd_r43x6_ge_decode2` (avx512)

Byte-identical (modulo indentation) to
`build/native/gcc/mlir/avx512/region/fd_r43x6_ge_decode2.mlir`: two point decompressions, RFC 8032 §5.1.3 over the r43x6 representation.
-/

namespace Firedancer.Avx512
open LeanMLIR SLLVM

def fd_r43x6_ge_decode2_region : MLIR.AST.Region 0 := [mlir_region|
{
  ^bb0(%arg0: !llvm.ptr, %arg1: !llvm.ptr, %arg2: !llvm.ptr, %arg3: !llvm.ptr, %arg4: !llvm.ptr, %arg5: !llvm.ptr, %arg6: !llvm.ptr, %arg7: !llvm.ptr):
    %0 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %1 = "llvm.mlir.constant"() <{value = 32 : i64}> : () -> i64
    %2 = "llvm.mlir.constant"() <{value = 0 : i64}> : () -> i64
    %3 = "llvm.mlir.constant"() <{value = 3 : i64}> : () -> i64
    %4 = "llvm.mlir.constant"() <{value = 63 : i64}> : () -> i64
    %5 = "llvm.mlir.constant"() <{value = 9223372036854775807 : i64}> : () -> i64
    %6 = "llvm.mlir.constant"() <{value = dense<[8796093022207, 8796093022207, 8796093022207, 8796093022207, 8796093022207, 1099511627775, 0, 0]> : vector<8xi64>}> : () -> vector<8xi64>
    %7 = "llvm.mlir.constant"() <{value = dense<[43, 43, 43, 43, 43, 40, 0, 0]> : vector<8xi64>}> : () -> vector<8xi64>
    %8 = "llvm.mlir.poison"() : () -> vector<8xi64>
    %9 = "llvm.mlir.constant"() <{value = dense<[19, 1, 1, 1, 1, 1, 0, 0]> : vector<8xi64>}> : () -> vector<8xi64>
    %10 = "llvm.mlir.constant"() <{value = dense<[8795933638636, 8796091973631, 8796091973631, 8796091973631, 8796091973631, 1099510579199, 0, 0]> : vector<8xi64>}> : () -> vector<8xi64>
    %11 = "llvm.mlir.constant"() <{value = dense<[5, 0, 1, 2, 3, 4, 8, 8]> : vector<8xi64>}> : () -> vector<8xi64>
    %12 = "llvm.mlir.constant"() <{value = dense<0> : vector<8xi64>}> : () -> vector<8xi64>
    %13 = "llvm.mlir.constant"() <{value = dense<18> : vector<8xi64>}> : () -> vector<8xi64>
    %14 = "llvm.mlir.constant"() <{value = dense<[-1, 0, 0, 0, 0, 0, 0, 0]> : vector<8xi64>}> : () -> vector<8xi64>
    %15 = "llvm.mlir.constant"() <{value = dense<[159383552, 1048576, 1048576, 1048576, 1048576, 1048576, 0, 0]> : vector<8xi64>}> : () -> vector<8xi64>
    %16 = "llvm.mlir.constant"() <{value = dense<[6365466163363, 253762649449, 7518893317, 260847760460, 7696165686388, 704489577558, 0, 0]> : vector<8xi64>}> : () -> vector<8xi64>
    %17 = "llvm.mlir.constant"() <{value = dense<[1, 0, 0, 0, 0, 0, 0, 0]> : vector<8xi64>}> : () -> vector<8xi64>
    %18 = "llvm.mlir.constant"() <{value = dense<[8795933638637, 8796091973631, 8796091973631, 8796091973631, 8796091973631, 1099510579199, 0, 0]> : vector<8xi64>}> : () -> vector<8xi64>
    %19 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %20 = "llvm.mlir.constant"() <{value = -1 : i32}> : () -> i32
    %21 = "llvm.mlir.constant"() <{value = -2 : i32}> : () -> i32
    %22 = "llvm.mlir.constant"() <{value = -1 : i8}> : () -> i8
    %23 = "llvm.mlir.constant"() <{value = dense<[3467281080496, 6582290652611, 5210002954932, 329084955603, 4526638806224, 373767602335, 0, 0]> : vector<8xi64>}> : () -> vector<8xi64>
    %24 = "llvm.mlir.constant"() <{value = dense<[0, 1, 8, 9, 4, 5, 12, 13]> : vector<8xi64>}> : () -> vector<8xi64>
    %25 = "llvm.mlir.constant"() <{value = dense<[2, 3, 10, 11, 6, 7, 12, 13]> : vector<8xi64>}> : () -> vector<8xi64>
    %26 = "llvm.mlir.constant"() <{value = dense<43> : vector<8xi64>}> : () -> vector<8xi64>
    %27 = "llvm.mlir.constant"() <{value = dense<[43, 43, 43, 43, 40, 40, 40, 40]> : vector<8xi64>}> : () -> vector<8xi64>
    %28 = "llvm.mlir.constant"() <{value = 19 : i64}> : () -> i64
    %29 = "llvm.mlir.poison"() : () -> i64
    %30 = "llvm.mlir.undef"() : () -> vector<8xi64>
    %31 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %32 = "llvm.insertelement"(%30, %29, %31) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %33 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %34 = "llvm.insertelement"(%32, %29, %33) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %35 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %36 = "llvm.insertelement"(%34, %29, %35) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %37 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %38 = "llvm.insertelement"(%36, %29, %37) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %39 = "llvm.mlir.constant"() <{value = 4 : i32}> : () -> i32
    %40 = "llvm.insertelement"(%38, %28, %39) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %41 = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
    %42 = "llvm.insertelement"(%40, %28, %41) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %43 = "llvm.mlir.constant"() <{value = 6 : i32}> : () -> i32
    %44 = "llvm.insertelement"(%42, %28, %43) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %45 = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
    %46 = "llvm.insertelement"(%44, %28, %45) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %47 = "llvm.mlir.constant"() <{value = dense<8796093022207> : vector<8xi64>}> : () -> vector<8xi64>
    %48 = "llvm.mlir.constant"() <{value = dense<[8796093022207, 8796093022207, 8796093022207, 8796093022207, 1099511627775, 1099511627775, 1099511627775, 1099511627775]> : vector<8xi64>}> : () -> vector<8xi64>
    %49 = "llvm.alloca"(%0) <{alignment = 32 : i64, elem_type = !llvm.array<4 x i64>}> : (i32) -> !llvm.ptr
    %50 = "llvm.alloca"(%0) <{alignment = 32 : i64, elem_type = !llvm.array<4 x i64>}> : (i32) -> !llvm.ptr
    %51 = "llvm.alloca"(%0) <{alignment = 64 : i64, elem_type = vector<8xi64>}> : (i32) -> !llvm.ptr
    %52 = "llvm.alloca"(%0) <{alignment = 64 : i64, elem_type = vector<8xi64>}> : (i32) -> !llvm.ptr
    "llvm.intr.lifetime.start"(%49) <{size = 32 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%50) <{size = 32 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.memcpy"(%49, %arg3, %1) <{isVolatile = false}> : (!llvm.ptr, !llvm.ptr, i64) -> ()
    "llvm.intr.memcpy"(%50, %arg7, %1) <{isVolatile = false}> : (!llvm.ptr, !llvm.ptr, i64) -> ()
    %53 = "llvm.getelementptr"(%49, %2, %3) <{elem_type = !llvm.array<4 x i64>, inbounds, rawConstantIndices = array<i32: -2147483648, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr
    %54 = "llvm.load"(%53) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    %55 = "llvm.getelementptr"(%50, %2, %3) <{elem_type = !llvm.array<4 x i64>, inbounds, rawConstantIndices = array<i32: -2147483648, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr
    %56 = "llvm.load"(%55) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    %57 = "llvm.lshr"(%54, %4) : (i64, i64) -> i64
    %58 = "llvm.trunc"(%57) : (i64) -> i32
    %59 = "llvm.lshr"(%56, %4) : (i64, i64) -> i64
    %60 = "llvm.trunc"(%59) : (i64) -> i32
    %61 = "llvm.and"(%54, %5) : (i64, i64) -> i64
    %62 = "llvm.and"(%56, %5) : (i64, i64) -> i64
    "llvm.store"(%61, %53) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (i64, !llvm.ptr) -> ()
    "llvm.store"(%62, %55) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (i64, !llvm.ptr) -> ()
    %63 = "llvm.call"(%49) <{CConv = #llvm.cconv<fastcc>, callee = @wv_ld, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr) -> vector<4xi64>
    %64 = "llvm.call"(%63) <{CConv = #llvm.cconv<fastcc>, callee = @fd_r43x6_unpack, fastmathFlags = #llvm.fastmath<none>}> : (vector<4xi64>) -> vector<8xi64>
    %65 = "llvm.call"(%50) <{CConv = #llvm.cconv<fastcc>, callee = @wv_ld, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr) -> vector<4xi64>
    %66 = "llvm.call"(%65) <{CConv = #llvm.cconv<fastcc>, callee = @fd_r43x6_unpack, fastmathFlags = #llvm.fastmath<none>}> : (vector<4xi64>) -> vector<8xi64>
    %67 = "llvm.call"(%64) <{CConv = #llvm.cconv<fastcc>, callee = @fd_r43x6_sqr_fast, fastmathFlags = #llvm.fastmath<none>}> : (vector<8xi64>) -> vector<8xi64>
    %68 = "llvm.and"(%67, %6) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %69 = "llvm.lshr"(%67, %7) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %70 = "llvm.shufflevector"(%69, %8) <{mask = array<i32: 5, 0, 1, 2, 3, 4, 6, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %71 = "x86vector.avx512.intr.vpmadd52l.uq.512"(%68, %9, %70) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %72 = "llvm.call"(%66) <{CConv = #llvm.cconv<fastcc>, callee = @fd_r43x6_sqr_fast, fastmathFlags = #llvm.fastmath<none>}> : (vector<8xi64>) -> vector<8xi64>
    %73 = "llvm.and"(%72, %6) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %74 = "llvm.lshr"(%72, %7) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %75 = "llvm.shufflevector"(%74, %8) <{mask = array<i32: 5, 0, 1, 2, 3, 4, 6, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %76 = "x86vector.avx512.intr.vpmadd52l.uq.512"(%73, %9, %75) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %77 = "llvm.add"(%71, %10) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %78 = "llvm.and"(%77, %6) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %79 = "llvm.ashr"(%77, %7) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %80 = "x86vector.avx512.intr.vpermi2var.q.512"(%79, %11, %12) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %81 = "llvm.mul"(%80, %13) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %82 = "llvm.and"(%81, %14) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %83 = "llvm.add"(%80, %78) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %84 = "llvm.add"(%83, %82) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %85 = "llvm.add"(%84, %15) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %86 = "llvm.add"(%76, %10) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %87 = "llvm.and"(%86, %6) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %88 = "llvm.ashr"(%86, %7) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %89 = "x86vector.avx512.intr.vpermi2var.q.512"(%88, %11, %12) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %90 = "llvm.mul"(%89, %13) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %91 = "llvm.and"(%90, %14) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %92 = "llvm.add"(%87, %89) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %93 = "llvm.add"(%92, %91) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %94 = "llvm.add"(%93, %15) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %95 = "llvm.call"(%16, %71) <{CConv = #llvm.cconv<fastcc>, callee = @fd_r43x6_mul_fast, fastmathFlags = #llvm.fastmath<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %96 = "llvm.and"(%95, %6) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %97 = "llvm.lshr"(%95, %7) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %98 = "llvm.shufflevector"(%97, %8) <{mask = array<i32: 5, 0, 1, 2, 3, 4, 6, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %99 = "x86vector.avx512.intr.vpmadd52l.uq.512"(%96, %9, %98) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %100 = "llvm.add"(%99, %17) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %101 = "llvm.call"(%16, %76) <{CConv = #llvm.cconv<fastcc>, callee = @fd_r43x6_mul_fast, fastmathFlags = #llvm.fastmath<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %102 = "llvm.and"(%101, %6) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %103 = "llvm.lshr"(%101, %7) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %104 = "llvm.shufflevector"(%103, %8) <{mask = array<i32: 5, 0, 1, 2, 3, 4, 6, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %105 = "x86vector.avx512.intr.vpmadd52l.uq.512"(%102, %9, %104) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %106 = "llvm.add"(%105, %17) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %107 = "llvm.call"(%100) <{CConv = #llvm.cconv<fastcc>, callee = @fd_r43x6_sqr_fast, fastmathFlags = #llvm.fastmath<none>}> : (vector<8xi64>) -> vector<8xi64>
    %108 = "llvm.and"(%107, %6) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %109 = "llvm.lshr"(%107, %7) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %110 = "llvm.shufflevector"(%109, %8) <{mask = array<i32: 5, 0, 1, 2, 3, 4, 6, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %111 = "x86vector.avx512.intr.vpmadd52l.uq.512"(%108, %9, %110) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %112 = "llvm.call"(%106) <{CConv = #llvm.cconv<fastcc>, callee = @fd_r43x6_sqr_fast, fastmathFlags = #llvm.fastmath<none>}> : (vector<8xi64>) -> vector<8xi64>
    %113 = "llvm.and"(%112, %6) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %114 = "llvm.lshr"(%112, %7) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %115 = "llvm.shufflevector"(%114, %8) <{mask = array<i32: 5, 0, 1, 2, 3, 4, 6, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %116 = "x86vector.avx512.intr.vpmadd52l.uq.512"(%113, %9, %115) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %117 = "llvm.call"(%111) <{CConv = #llvm.cconv<fastcc>, callee = @fd_r43x6_sqr_fast, fastmathFlags = #llvm.fastmath<none>}> : (vector<8xi64>) -> vector<8xi64>
    %118 = "llvm.and"(%117, %6) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %119 = "llvm.lshr"(%117, %7) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %120 = "llvm.shufflevector"(%119, %8) <{mask = array<i32: 5, 0, 1, 2, 3, 4, 6, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %121 = "x86vector.avx512.intr.vpmadd52l.uq.512"(%118, %9, %120) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %122 = "llvm.call"(%116) <{CConv = #llvm.cconv<fastcc>, callee = @fd_r43x6_sqr_fast, fastmathFlags = #llvm.fastmath<none>}> : (vector<8xi64>) -> vector<8xi64>
    %123 = "llvm.and"(%122, %6) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %124 = "llvm.lshr"(%122, %7) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %125 = "llvm.shufflevector"(%124, %8) <{mask = array<i32: 5, 0, 1, 2, 3, 4, 6, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %126 = "x86vector.avx512.intr.vpmadd52l.uq.512"(%123, %9, %125) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %127 = "llvm.call"(%100, %111) <{CConv = #llvm.cconv<fastcc>, callee = @fd_r43x6_mul_fast, fastmathFlags = #llvm.fastmath<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %128 = "llvm.and"(%127, %6) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %129 = "llvm.lshr"(%127, %7) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %130 = "llvm.shufflevector"(%129, %8) <{mask = array<i32: 5, 0, 1, 2, 3, 4, 6, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %131 = "x86vector.avx512.intr.vpmadd52l.uq.512"(%128, %9, %130) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %132 = "llvm.call"(%106, %116) <{CConv = #llvm.cconv<fastcc>, callee = @fd_r43x6_mul_fast, fastmathFlags = #llvm.fastmath<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %133 = "llvm.and"(%132, %6) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %134 = "llvm.lshr"(%132, %7) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %135 = "llvm.shufflevector"(%134, %8) <{mask = array<i32: 5, 0, 1, 2, 3, 4, 6, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %136 = "x86vector.avx512.intr.vpmadd52l.uq.512"(%133, %9, %135) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %137 = "llvm.call"(%85, %131) <{CConv = #llvm.cconv<fastcc>, callee = @fd_r43x6_mul_fast, fastmathFlags = #llvm.fastmath<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %138 = "llvm.and"(%137, %6) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %139 = "llvm.lshr"(%137, %7) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %140 = "llvm.shufflevector"(%139, %8) <{mask = array<i32: 5, 0, 1, 2, 3, 4, 6, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %141 = "x86vector.avx512.intr.vpmadd52l.uq.512"(%138, %9, %140) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %142 = "llvm.call"(%94, %136) <{CConv = #llvm.cconv<fastcc>, callee = @fd_r43x6_mul_fast, fastmathFlags = #llvm.fastmath<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %143 = "llvm.and"(%142, %6) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %144 = "llvm.lshr"(%142, %7) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %145 = "llvm.shufflevector"(%144, %8) <{mask = array<i32: 5, 0, 1, 2, 3, 4, 6, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %146 = "x86vector.avx512.intr.vpmadd52l.uq.512"(%143, %9, %145) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %147 = "llvm.call"(%141, %121) <{CConv = #llvm.cconv<fastcc>, callee = @fd_r43x6_mul_fast, fastmathFlags = #llvm.fastmath<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %148 = "llvm.and"(%147, %6) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %149 = "llvm.lshr"(%147, %7) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %150 = "llvm.shufflevector"(%149, %8) <{mask = array<i32: 5, 0, 1, 2, 3, 4, 6, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %151 = "x86vector.avx512.intr.vpmadd52l.uq.512"(%148, %9, %150) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %152 = "llvm.call"(%146, %126) <{CConv = #llvm.cconv<fastcc>, callee = @fd_r43x6_mul_fast, fastmathFlags = #llvm.fastmath<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %153 = "llvm.and"(%152, %6) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %154 = "llvm.lshr"(%152, %7) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %155 = "llvm.shufflevector"(%154, %8) <{mask = array<i32: 5, 0, 1, 2, 3, 4, 6, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %156 = "x86vector.avx512.intr.vpmadd52l.uq.512"(%153, %9, %155) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    "llvm.intr.lifetime.start"(%51) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%52) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.call"(%51, %151, %52, %156) <{CConv = #llvm.cconv<ccc>, callee = @fd_r43x6_pow22523_2, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, vector<8xi64>, !llvm.ptr, vector<8xi64>) -> ()
    %157 = "llvm.load"(%51) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %158 = "llvm.load"(%52) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    "llvm.intr.lifetime.end"(%52) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%51) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    %159 = "llvm.call"(%141, %157) <{CConv = #llvm.cconv<fastcc>, callee = @fd_r43x6_mul_fast, fastmathFlags = #llvm.fastmath<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %160 = "llvm.and"(%159, %6) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %161 = "llvm.lshr"(%159, %7) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %162 = "llvm.shufflevector"(%161, %8) <{mask = array<i32: 5, 0, 1, 2, 3, 4, 6, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %163 = "x86vector.avx512.intr.vpmadd52l.uq.512"(%160, %9, %162) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %164 = "llvm.call"(%146, %158) <{CConv = #llvm.cconv<fastcc>, callee = @fd_r43x6_mul_fast, fastmathFlags = #llvm.fastmath<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %165 = "llvm.and"(%164, %6) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %166 = "llvm.lshr"(%164, %7) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %167 = "llvm.shufflevector"(%166, %8) <{mask = array<i32: 5, 0, 1, 2, 3, 4, 6, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %168 = "x86vector.avx512.intr.vpmadd52l.uq.512"(%165, %9, %167) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %169 = "llvm.call"(%163) <{CConv = #llvm.cconv<fastcc>, callee = @fd_r43x6_sqr_fast, fastmathFlags = #llvm.fastmath<none>}> : (vector<8xi64>) -> vector<8xi64>
    %170 = "llvm.and"(%169, %6) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %171 = "llvm.lshr"(%169, %7) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %172 = "llvm.shufflevector"(%171, %8) <{mask = array<i32: 5, 0, 1, 2, 3, 4, 6, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %173 = "x86vector.avx512.intr.vpmadd52l.uq.512"(%170, %9, %172) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %174 = "llvm.call"(%168) <{CConv = #llvm.cconv<fastcc>, callee = @fd_r43x6_sqr_fast, fastmathFlags = #llvm.fastmath<none>}> : (vector<8xi64>) -> vector<8xi64>
    %175 = "llvm.and"(%174, %6) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %176 = "llvm.lshr"(%174, %7) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %177 = "llvm.shufflevector"(%176, %8) <{mask = array<i32: 5, 0, 1, 2, 3, 4, 6, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %178 = "x86vector.avx512.intr.vpmadd52l.uq.512"(%175, %9, %177) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %179 = "llvm.call"(%100, %173) <{CConv = #llvm.cconv<fastcc>, callee = @fd_r43x6_mul_fast, fastmathFlags = #llvm.fastmath<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %180 = "llvm.and"(%179, %6) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %181 = "llvm.lshr"(%179, %7) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %182 = "llvm.shufflevector"(%181, %8) <{mask = array<i32: 5, 0, 1, 2, 3, 4, 6, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %183 = "x86vector.avx512.intr.vpmadd52l.uq.512"(%180, %9, %182) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %184 = "llvm.call"(%106, %178) <{CConv = #llvm.cconv<fastcc>, callee = @fd_r43x6_mul_fast, fastmathFlags = #llvm.fastmath<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %185 = "llvm.and"(%184, %6) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %186 = "llvm.lshr"(%184, %7) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %187 = "llvm.shufflevector"(%186, %8) <{mask = array<i32: 5, 0, 1, 2, 3, 4, 6, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %188 = "x86vector.avx512.intr.vpmadd52l.uq.512"(%185, %9, %187) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %189 = "llvm.sub"(%183, %84) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %190 = "llvm.add"(%189, %18) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %191 = "llvm.sub"(%188, %93) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %192 = "llvm.add"(%191, %18) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %193 = "llvm.add"(%183, %85) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %194 = "llvm.call"(%190) <{CConv = #llvm.cconv<fastcc>, callee = @fd_r43x6_is_nonzero, fastmathFlags = #llvm.fastmath<none>}> : (vector<8xi64>) -> i32
    %195 = "llvm.call"(%192) <{CConv = #llvm.cconv<fastcc>, callee = @fd_r43x6_is_nonzero, fastmathFlags = #llvm.fastmath<none>}> : (vector<8xi64>) -> i32
    %196 = "llvm.call"(%193) <{CConv = #llvm.cconv<fastcc>, callee = @fd_r43x6_is_nonzero, fastmathFlags = #llvm.fastmath<none>}> : (vector<8xi64>) -> i32
    %197 = "llvm.and"(%196, %194) : (i32, i32) -> i32
    %198 = "llvm.icmp"(%197, %19) <{predicate = 0 : i64}> : (i32, i32) -> i1
    "llvm.cond_br"(%198)[^bb1, ^bb3] <{branch_weights = array<i32: 2000, 1>, operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
  ^bb1:  // pred: ^bb0
    %199 = "llvm.add"(%188, %94) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %200 = "llvm.call"(%199) <{CConv = #llvm.cconv<fastcc>, callee = @fd_r43x6_is_nonzero, fastmathFlags = #llvm.fastmath<none>}> : (vector<8xi64>) -> i32
    %201 = "llvm.and"(%200, %195) : (i32, i32) -> i32
    %202 = "llvm.icmp"(%201, %19) <{predicate = 0 : i64}> : (i32, i32) -> i1
    "llvm.cond_br"(%202)[^bb2, ^bb4] <{branch_weights = array<i32: 2000, 1>, operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
  ^bb2:  // pred: ^bb1
    %203 = "llvm.trunc"(%194) : (i32) -> i8
    %204 = "llvm.add"(%203, %22) <{overflowFlags = #llvm.overflow<nsw>}> : (i8, i8) -> i8
    %205 = "llvm.bitcast"(%204) : (i8) -> vector<8xi1>
    %206 = "llvm.select"(%205, %17, %23) <{fastmathFlags = #llvm.fastmath<none>}> : (vector<8xi1>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %207 = "llvm.trunc"(%195) : (i32) -> i8
    %208 = "llvm.add"(%207, %22) <{overflowFlags = #llvm.overflow<nsw>}> : (i8, i8) -> i8
    %209 = "llvm.bitcast"(%208) : (i8) -> vector<8xi1>
    %210 = "llvm.select"(%209, %17, %23) <{fastmathFlags = #llvm.fastmath<none>}> : (vector<8xi1>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %211 = "llvm.call"(%163, %206) <{CConv = #llvm.cconv<fastcc>, callee = @fd_r43x6_mul_fast, fastmathFlags = #llvm.fastmath<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %212 = "llvm.and"(%211, %6) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %213 = "llvm.lshr"(%211, %7) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %214 = "llvm.shufflevector"(%213, %8) <{mask = array<i32: 5, 0, 1, 2, 3, 4, 6, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %215 = "x86vector.avx512.intr.vpmadd52l.uq.512"(%212, %9, %214) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %216 = "llvm.call"(%168, %210) <{CConv = #llvm.cconv<fastcc>, callee = @fd_r43x6_mul_fast, fastmathFlags = #llvm.fastmath<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %217 = "llvm.and"(%216, %6) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %218 = "llvm.lshr"(%216, %7) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %219 = "llvm.shufflevector"(%218, %8) <{mask = array<i32: 5, 0, 1, 2, 3, 4, 6, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %220 = "x86vector.avx512.intr.vpmadd52l.uq.512"(%217, %9, %219) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %221 = "llvm.call"(%215) <{CConv = #llvm.cconv<fastcc>, callee = @fd_r43x6_diagnose, fastmathFlags = #llvm.fastmath<none>}> : (vector<8xi64>) -> i32
    %222 = "llvm.call"(%220) <{CConv = #llvm.cconv<fastcc>, callee = @fd_r43x6_diagnose, fastmathFlags = #llvm.fastmath<none>}> : (vector<8xi64>) -> i32
    %223 = "llvm.icmp"(%221, %58) <{predicate = 0 : i64}> : (i32, i32) -> i1
    %224 = "llvm.sext"(%223) : (i1) -> i8
    %225 = "llvm.sub"(%18, %215) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %226 = "llvm.and"(%225, %6) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %227 = "llvm.ashr"(%225, %7) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %228 = "x86vector.avx512.intr.vpermi2var.q.512"(%227, %11, %12) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %229 = "llvm.mul"(%228, %13) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %230 = "llvm.and"(%229, %14) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %231 = "llvm.add"(%226, %15) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %232 = "llvm.add"(%231, %228) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %233 = "llvm.add"(%232, %230) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %234 = "llvm.bitcast"(%224) : (i8) -> vector<8xi1>
    %235 = "llvm.select"(%234, %215, %233) <{fastmathFlags = #llvm.fastmath<none>}> : (vector<8xi1>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %236 = "llvm.icmp"(%222, %60) <{predicate = 0 : i64}> : (i32, i32) -> i1
    %237 = "llvm.sext"(%236) : (i1) -> i8
    %238 = "llvm.sub"(%18, %220) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %239 = "llvm.and"(%238, %6) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %240 = "llvm.ashr"(%238, %7) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %241 = "x86vector.avx512.intr.vpermi2var.q.512"(%240, %11, %12) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %242 = "llvm.mul"(%241, %13) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %243 = "llvm.and"(%242, %14) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %244 = "llvm.add"(%239, %15) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %245 = "llvm.add"(%244, %241) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %246 = "llvm.add"(%245, %243) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %247 = "llvm.bitcast"(%237) : (i8) -> vector<8xi1>
    %248 = "llvm.select"(%247, %220, %246) <{fastmathFlags = #llvm.fastmath<none>}> : (vector<8xi1>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %249 = "llvm.call"(%235, %64) <{CConv = #llvm.cconv<fastcc>, callee = @fd_r43x6_mul_fast, fastmathFlags = #llvm.fastmath<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %250 = "llvm.and"(%249, %6) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %251 = "llvm.lshr"(%249, %7) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %252 = "llvm.shufflevector"(%251, %8) <{mask = array<i32: 5, 0, 1, 2, 3, 4, 6, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %253 = "x86vector.avx512.intr.vpmadd52l.uq.512"(%250, %9, %252) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %254 = "llvm.call"(%248, %66) <{CConv = #llvm.cconv<fastcc>, callee = @fd_r43x6_mul_fast, fastmathFlags = #llvm.fastmath<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %255 = "llvm.and"(%254, %6) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %256 = "llvm.lshr"(%254, %7) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %257 = "llvm.shufflevector"(%256, %8) <{mask = array<i32: 5, 0, 1, 2, 3, 4, 6, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %258 = "x86vector.avx512.intr.vpmadd52l.uq.512"(%255, %9, %257) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %259 = "x86vector.avx512.intr.vpermi2var.q.512"(%235, %24, %17) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %260 = "x86vector.avx512.intr.vpermi2var.q.512"(%64, %24, %253) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %261 = "x86vector.avx512.intr.vpermi2var.q.512"(%235, %25, %17) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %262 = "x86vector.avx512.intr.vpermi2var.q.512"(%64, %25, %253) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %263 = "llvm.shufflevector"(%259, %260) <{mask = array<i32: 0, 8, 2, 10, 4, 12, 6, 14>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %264 = "llvm.shufflevector"(%259, %260) <{mask = array<i32: 1, 9, 3, 11, 5, 13, 7, 15>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %265 = "llvm.shufflevector"(%261, %262) <{mask = array<i32: 0, 8, 2, 10, -1, -1, -1, -1>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %266 = "llvm.shufflevector"(%261, %262) <{mask = array<i32: 1, 9, 3, 11, -1, -1, -1, -1>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %267 = "llvm.shufflevector"(%263, %266) <{mask = array<i32: 0, 1, 2, 3, 8, 9, 10, 11>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    "llvm.store"(%267, %arg0) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (vector<8xi64>, !llvm.ptr) -> ()
    %268 = "llvm.shufflevector"(%264, %263) <{mask = array<i32: 0, 1, 2, 3, 12, 13, 14, 15>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    "llvm.store"(%268, %arg1) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (vector<8xi64>, !llvm.ptr) -> ()
    %269 = "llvm.shufflevector"(%265, %264) <{mask = array<i32: 0, 1, 2, 3, 12, 13, 14, 15>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    "llvm.store"(%269, %arg2) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (vector<8xi64>, !llvm.ptr) -> ()
    %270 = "x86vector.avx512.intr.vpermi2var.q.512"(%248, %24, %17) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %271 = "x86vector.avx512.intr.vpermi2var.q.512"(%66, %24, %258) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %272 = "x86vector.avx512.intr.vpermi2var.q.512"(%248, %25, %17) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %273 = "x86vector.avx512.intr.vpermi2var.q.512"(%66, %25, %258) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %274 = "llvm.shufflevector"(%270, %271) <{mask = array<i32: 0, 8, 2, 10, 4, 12, 6, 14>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %275 = "llvm.shufflevector"(%270, %271) <{mask = array<i32: 1, 9, 3, 11, 5, 13, 7, 15>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %276 = "llvm.shufflevector"(%272, %273) <{mask = array<i32: 0, 8, 2, 10, -1, -1, -1, -1>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %277 = "llvm.shufflevector"(%272, %273) <{mask = array<i32: 1, 9, 3, 11, -1, -1, -1, -1>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %278 = "llvm.shufflevector"(%274, %277) <{mask = array<i32: 0, 1, 2, 3, 8, 9, 10, 11>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    "llvm.store"(%278, %arg4) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (vector<8xi64>, !llvm.ptr) -> ()
    %279 = "llvm.shufflevector"(%275, %274) <{mask = array<i32: 0, 1, 2, 3, 12, 13, 14, 15>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    "llvm.store"(%279, %arg5) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (vector<8xi64>, !llvm.ptr) -> ()
    %280 = "llvm.shufflevector"(%276, %275) <{mask = array<i32: 0, 1, 2, 3, 12, 13, 14, 15>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    "llvm.store"(%280, %arg6) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (vector<8xi64>, !llvm.ptr) -> ()
    %281 = "llvm.load"(%arg0) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %282 = "llvm.lshr"(%281, %26) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %283 = "llvm.load"(%arg1) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %284 = "llvm.lshr"(%283, %26) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %285 = "llvm.load"(%arg2) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %286 = "llvm.lshr"(%285, %27) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %287 = "llvm.mul"(%286, %46) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %288 = "llvm.and"(%281, %47) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %289 = "llvm.shufflevector"(%287, %286) <{mask = array<i32: 4, 5, 6, 7, 8, 9, 10, 11>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %290 = "llvm.add"(%289, %288) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    "llvm.store"(%290, %arg0) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (vector<8xi64>, !llvm.ptr) -> ()
    %291 = "llvm.load"(%arg1) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %292 = "llvm.and"(%291, %47) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %293 = "llvm.add"(%292, %282) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    "llvm.store"(%293, %arg1) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (vector<8xi64>, !llvm.ptr) -> ()
    %294 = "llvm.load"(%arg2) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %295 = "llvm.and"(%294, %48) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %296 = "llvm.add"(%295, %284) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    "llvm.store"(%296, %arg2) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (vector<8xi64>, !llvm.ptr) -> ()
    %297 = "llvm.load"(%arg4) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %298 = "llvm.lshr"(%297, %26) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %299 = "llvm.load"(%arg5) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %300 = "llvm.lshr"(%299, %26) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %301 = "llvm.load"(%arg6) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %302 = "llvm.lshr"(%301, %27) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %303 = "llvm.mul"(%302, %46) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %304 = "llvm.and"(%297, %47) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %305 = "llvm.shufflevector"(%303, %302) <{mask = array<i32: 4, 5, 6, 7, 8, 9, 10, 11>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %306 = "llvm.add"(%305, %304) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    "llvm.store"(%306, %arg4) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (vector<8xi64>, !llvm.ptr) -> ()
    %307 = "llvm.load"(%arg5) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %308 = "llvm.and"(%307, %47) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %309 = "llvm.add"(%308, %298) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    "llvm.store"(%309, %arg5) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (vector<8xi64>, !llvm.ptr) -> ()
    %310 = "llvm.load"(%arg6) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %311 = "llvm.and"(%310, %48) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %312 = "llvm.add"(%311, %300) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    "llvm.br"(%312, %19)[^bb5] : (vector<8xi64>, i32) -> ()
  ^bb3:  // pred: ^bb0
    "llvm.store"(%12, %arg0) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (vector<8xi64>, !llvm.ptr) -> ()
    "llvm.store"(%12, %arg4) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (vector<8xi64>, !llvm.ptr) -> ()
    "llvm.store"(%12, %arg1) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (vector<8xi64>, !llvm.ptr) -> ()
    "llvm.store"(%12, %arg5) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (vector<8xi64>, !llvm.ptr) -> ()
    "llvm.store"(%12, %arg2) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (vector<8xi64>, !llvm.ptr) -> ()
    "llvm.br"(%12, %20)[^bb5] : (vector<8xi64>, i32) -> ()
  ^bb4:  // pred: ^bb1
    "llvm.store"(%12, %arg0) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (vector<8xi64>, !llvm.ptr) -> ()
    "llvm.store"(%12, %arg4) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (vector<8xi64>, !llvm.ptr) -> ()
    "llvm.store"(%12, %arg1) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (vector<8xi64>, !llvm.ptr) -> ()
    "llvm.store"(%12, %arg5) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (vector<8xi64>, !llvm.ptr) -> ()
    "llvm.store"(%12, %arg2) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (vector<8xi64>, !llvm.ptr) -> ()
    "llvm.br"(%12, %21)[^bb5] : (vector<8xi64>, i32) -> ()
  ^bb5(%313: vector<8xi64>, %314: i32):  // 3 preds: ^bb2, ^bb3, ^bb4
    "llvm.store"(%313, %arg6) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (vector<8xi64>, !llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%50) <{size = 32 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%49) <{size = 32 : i64}> : (!llvm.ptr) -> ()
    "llvm.return"(%314) : (i32) -> ()
}
]

set_option maxHeartbeats 1000000 in
/-- Six blocks and seven callees inlined; the elaboration is big but flat. -/
def fd_r43x6_ge_decode2 :
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
