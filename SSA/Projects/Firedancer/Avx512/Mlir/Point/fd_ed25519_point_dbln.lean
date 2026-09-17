/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
-- build/native/gcc/mlir_canonicalized/avx512/region/fd_ed25519_point_dbln.mlir
import SSA.Projects.SLLVM.Cfg
import SSA.Projects.Firedancer.Avx512.Mlir.Field.fd_r43x6_quad_sqr_fast
import SSA.Projects.Firedancer.Avx512.Mlir.Field.fd_r43x6_quad_mul_fast

namespace Firedancer.Avx512
open LeanMLIR SLLVM

-- `^bb0` is 264 operations, past the default depth of the region parser.
set_option maxRecDepth 4000 in
def fd_ed25519_point_dbln_region : MLIR.AST.Region 0 := [mlir_region|
{
  ^bb0(%arg0: !llvm.ptr, %arg1: !llvm.ptr, %arg2: i32):
    %0 = "llvm.mlir.constant"() <{value = 1 : i8}> : () -> i8
    %1 = "llvm.mlir.constant"() <{value = dense<[8796093022207, 8796093022207, 8796093022207, 8796093022207, 1099511627775, 1099511627775, 1099511627775, 1099511627775]> : vector<8xi64>}> : () -> vector<8xi64>
    %2 = "llvm.mlir.constant"() <{value = dense<1048576> : vector<8xi64>}> : () -> vector<8xi64>
    %3 = "llvm.mlir.constant"() <{value = dense<[159383552, 159383552, 159383552, 159383552, 1048576, 1048576, 1048576, 1048576]> : vector<8xi64>}> : () -> vector<8xi64>
    %4 = "llvm.mlir.constant"() <{value = dense<8796093022207> : vector<8xi64>}> : () -> vector<8xi64>
    %5 = "llvm.mlir.constant"() <{value = 19 : i64}> : () -> i64
    %6 = "llvm.mlir.constant"() <{value = dense<[43, 43, 43, 43, 40, 40, 40, 40]> : vector<8xi64>}> : () -> vector<8xi64>
    %7 = "llvm.mlir.constant"() <{value = dense<43> : vector<8xi64>}> : () -> vector<8xi64>
    %8 = "llvm.mlir.constant"() <{value = dense<-1048576> : vector<8xi64>}> : () -> vector<8xi64>
    %9 = "llvm.mlir.constant"() <{value = dense<[-159383552, -159383552, -159383552, -159383552, -1048576, -1048576, -1048576, -1048576]> : vector<8xi64>}> : () -> vector<8xi64>
    %10 = "llvm.mlir.constant"() <{value = 1099511627775 : i64}> : () -> i64
    %11 = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
    %12 = "llvm.mlir.constant"() <{value = 6 : i32}> : () -> i32
    %13 = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
    %14 = "llvm.mlir.constant"() <{value = 4 : i32}> : () -> i32
    %15 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %16 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %17 = "llvm.mlir.constant"() <{value = 8796093022189 : i64}> : () -> i64
    %18 = "llvm.mlir.constant"() <{value = 8796093022207 : i64}> : () -> i64
    %19 = "llvm.mlir.constant"() <{value = dense<[0, 0, 1, 0, 0, 0, 1, 0]> : vector<8xi64>}> : () -> vector<8xi64>
    %20 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %21 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %22 = "llvm.mlir.poison"() : () -> vector<8xi64>
    %23 = "llvm.mlir.poison"() : () -> i64
    %24 = "llvm.mlir.undef"() : () -> vector<8xi64>
    %25 = "llvm.insertelement"(%24, %23, %16) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %26 = "llvm.insertelement"(%25, %17, %21) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %27 = "llvm.insertelement"(%26, %17, %20) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %28 = "llvm.insertelement"(%27, %23, %15) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %29 = "llvm.insertelement"(%28, %23, %14) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %30 = "llvm.insertelement"(%29, %18, %13) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %31 = "llvm.insertelement"(%30, %18, %12) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %32 = "llvm.insertelement"(%31, %23, %11) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %33 = "llvm.mlir.undef"() : () -> vector<8xi64>
    %34 = "llvm.insertelement"(%33, %23, %16) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %35 = "llvm.insertelement"(%34, %18, %21) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %36 = "llvm.insertelement"(%35, %18, %20) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %37 = "llvm.insertelement"(%36, %23, %15) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %38 = "llvm.insertelement"(%37, %23, %14) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %39 = "llvm.insertelement"(%38, %18, %13) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %40 = "llvm.insertelement"(%39, %18, %12) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %41 = "llvm.insertelement"(%40, %23, %11) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %42 = "llvm.mlir.undef"() : () -> vector<8xi64>
    %43 = "llvm.insertelement"(%42, %23, %16) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %44 = "llvm.insertelement"(%43, %18, %21) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %45 = "llvm.insertelement"(%44, %18, %20) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %46 = "llvm.insertelement"(%45, %23, %15) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %47 = "llvm.insertelement"(%46, %23, %14) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %48 = "llvm.insertelement"(%47, %10, %13) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %49 = "llvm.insertelement"(%48, %10, %12) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %50 = "llvm.insertelement"(%49, %23, %11) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %51 = "llvm.mlir.undef"() : () -> vector<8xi64>
    %52 = "llvm.insertelement"(%51, %17, %16) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %53 = "llvm.insertelement"(%52, %23, %21) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %54 = "llvm.insertelement"(%53, %23, %20) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %55 = "llvm.insertelement"(%54, %23, %15) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %56 = "llvm.insertelement"(%55, %18, %14) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %57 = "llvm.insertelement"(%56, %23, %13) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %58 = "llvm.insertelement"(%57, %23, %12) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %59 = "llvm.insertelement"(%58, %23, %11) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %60 = "llvm.mlir.undef"() : () -> vector<8xi64>
    %61 = "llvm.insertelement"(%60, %18, %16) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %62 = "llvm.insertelement"(%61, %23, %21) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %63 = "llvm.insertelement"(%62, %23, %20) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %64 = "llvm.insertelement"(%63, %23, %15) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %65 = "llvm.insertelement"(%64, %18, %14) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %66 = "llvm.insertelement"(%65, %23, %13) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %67 = "llvm.insertelement"(%66, %23, %12) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %68 = "llvm.insertelement"(%67, %23, %11) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %69 = "llvm.mlir.undef"() : () -> vector<8xi64>
    %70 = "llvm.insertelement"(%69, %18, %16) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %71 = "llvm.insertelement"(%70, %23, %21) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %72 = "llvm.insertelement"(%71, %23, %20) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %73 = "llvm.insertelement"(%72, %23, %15) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %74 = "llvm.insertelement"(%73, %10, %14) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %75 = "llvm.insertelement"(%74, %23, %13) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %76 = "llvm.insertelement"(%75, %23, %12) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %77 = "llvm.insertelement"(%76, %23, %11) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %78 = "llvm.mlir.undef"() : () -> vector<8xi64>
    %79 = "llvm.insertelement"(%78, %23, %16) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %80 = "llvm.insertelement"(%79, %23, %21) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %81 = "llvm.insertelement"(%80, %23, %20) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %82 = "llvm.insertelement"(%81, %23, %15) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %83 = "llvm.insertelement"(%82, %5, %14) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %84 = "llvm.insertelement"(%83, %5, %13) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %85 = "llvm.insertelement"(%84, %5, %12) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %86 = "llvm.insertelement"(%85, %5, %11) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %87 = "llvm.alloca"(%21) <{alignment = 64 : i64, elem_type = vector<8xi64>}> : (i32) -> !llvm.ptr
    %88 = "llvm.alloca"(%21) <{alignment = 64 : i64, elem_type = vector<8xi64>}> : (i32) -> !llvm.ptr
    %89 = "llvm.alloca"(%21) <{alignment = 64 : i64, elem_type = vector<8xi64>}> : (i32) -> !llvm.ptr
    %90 = "llvm.alloca"(%21) <{alignment = 64 : i64, elem_type = vector<8xi64>}> : (i32) -> !llvm.ptr
    %91 = "llvm.alloca"(%21) <{alignment = 64 : i64, elem_type = vector<8xi64>}> : (i32) -> !llvm.ptr
    %92 = "llvm.alloca"(%21) <{alignment = 64 : i64, elem_type = vector<8xi64>}> : (i32) -> !llvm.ptr
    %93 = "llvm.alloca"(%21) <{alignment = 64 : i64, elem_type = vector<8xi64>}> : (i32) -> !llvm.ptr
    %94 = "llvm.alloca"(%21) <{alignment = 64 : i64, elem_type = vector<8xi64>}> : (i32) -> !llvm.ptr
    %95 = "llvm.alloca"(%21) <{alignment = 64 : i64, elem_type = vector<8xi64>}> : (i32) -> !llvm.ptr
    %96 = "llvm.alloca"(%21) <{alignment = 64 : i64, elem_type = vector<8xi64>}> : (i32) -> !llvm.ptr
    %97 = "llvm.alloca"(%21) <{alignment = 64 : i64, elem_type = vector<8xi64>}> : (i32) -> !llvm.ptr
    %98 = "llvm.alloca"(%21) <{alignment = 64 : i64, elem_type = vector<8xi64>}> : (i32) -> !llvm.ptr
    %99 = "llvm.load"(%arg1) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %100 = "llvm.shufflevector"(%99, %22) <{mask = array<i32: 1, 1, 2, 0, 5, 5, 6, 4>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %101 = "llvm.getelementptr"(%arg1) <{elem_type = !llvm.struct<"struct.fd_curve25519_edwards", (vector<8xi64>, vector<8xi64>, vector<8xi64>)>, inbounds, rawConstantIndices = array<i32: 0, 1>}> : (!llvm.ptr) -> !llvm.ptr
    %102 = "llvm.load"(%101) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %103 = "llvm.shufflevector"(%102, %22) <{mask = array<i32: 1, 1, 2, 0, 5, 5, 6, 4>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %104 = "llvm.getelementptr"(%arg1) <{elem_type = !llvm.struct<"struct.fd_curve25519_edwards", (vector<8xi64>, vector<8xi64>, vector<8xi64>)>, inbounds, rawConstantIndices = array<i32: 0, 2>}> : (!llvm.ptr) -> !llvm.ptr
    %105 = "llvm.load"(%104) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %106 = "llvm.shufflevector"(%105, %22) <{mask = array<i32: 1, 1, 2, 0, 5, 5, 6, 4>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %107 = "llvm.add"(%100, %99) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %108 = "llvm.shufflevector"(%107, %100) <{mask = array<i32: 0, 9, 10, 11, 4, 13, 14, 15>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %109 = "llvm.add"(%103, %102) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %110 = "llvm.shufflevector"(%109, %103) <{mask = array<i32: 0, 9, 10, 11, 4, 13, 14, 15>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %111 = "llvm.add"(%106, %105) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %112 = "llvm.shufflevector"(%111, %106) <{mask = array<i32: 0, 9, 10, 11, 4, 13, 14, 15>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    "llvm.intr.lifetime.start"(%87) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%88) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%89) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.call"(%87, %88, %89, %108, %110, %112) <{CConv = #llvm.cconv<fastcc>, callee = @fd_r43x6_quad_sqr_fast, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr, !llvm.ptr, vector<8xi64>, vector<8xi64>, vector<8xi64>) -> ()
    %113 = "llvm.load"(%87) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %114 = "llvm.load"(%88) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %115 = "llvm.load"(%89) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    "llvm.intr.lifetime.end"(%89) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%88) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%87) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    %116 = "llvm.shl"(%113, %19) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %117 = "llvm.shl"(%114, %19) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %118 = "llvm.shl"(%115, %19) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %119 = "llvm.shufflevector"(%116, %22) <{mask = array<i32: 3, 3, 3, 3, 7, 7, 7, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %120 = "llvm.shufflevector"(%117, %22) <{mask = array<i32: 3, 3, 3, 3, 7, 7, 7, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %121 = "llvm.shufflevector"(%118, %22) <{mask = array<i32: 3, 3, 3, 3, 7, 7, 7, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %122 = "llvm.shufflevector"(%116, %22) <{mask = array<i32: 1, 1, 1, 1, 5, 5, 5, 5>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %123 = "llvm.shufflevector"(%117, %22) <{mask = array<i32: 1, 1, 1, 1, 5, 5, 5, 5>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %124 = "llvm.shufflevector"(%118, %22) <{mask = array<i32: 1, 1, 1, 1, 5, 5, 5, 5>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %125 = "llvm.add"(%119, %122) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %126 = "llvm.shufflevector"(%125, %119) <{mask = array<i32: 0, 9, 10, 3, 4, 13, 14, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %127 = "llvm.add"(%120, %123) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %128 = "llvm.shufflevector"(%127, %120) <{mask = array<i32: 0, 9, 10, 3, 4, 13, 14, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %129 = "llvm.add"(%121, %124) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %130 = "llvm.shufflevector"(%129, %121) <{mask = array<i32: 0, 9, 10, 3, 4, 13, 14, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %131 = "llvm.sub"(%126, %122) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %132 = "llvm.add"(%131, %32) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %133 = "llvm.shufflevector"(%126, %132) <{mask = array<i32: 0, 9, 10, 3, 4, 13, 14, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %134 = "llvm.sub"(%128, %123) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %135 = "llvm.add"(%134, %41) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %136 = "llvm.shufflevector"(%128, %135) <{mask = array<i32: 0, 9, 10, 3, 4, 13, 14, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %137 = "llvm.sub"(%130, %124) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %138 = "llvm.add"(%137, %50) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %139 = "llvm.shufflevector"(%130, %138) <{mask = array<i32: 0, 9, 10, 3, 4, 13, 14, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %140 = "llvm.add"(%133, %116) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %141 = "llvm.shufflevector"(%133, %140) <{mask = array<i32: 0, 1, 10, 3, 4, 5, 14, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %142 = "llvm.add"(%136, %117) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %143 = "llvm.shufflevector"(%136, %142) <{mask = array<i32: 0, 1, 10, 3, 4, 5, 14, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %144 = "llvm.add"(%139, %118) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %145 = "llvm.shufflevector"(%139, %144) <{mask = array<i32: 0, 1, 10, 3, 4, 5, 14, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %146 = "llvm.sub"(%141, %116) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %147 = "llvm.add"(%146, %59) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %148 = "llvm.shufflevector"(%147, %141) <{mask = array<i32: 0, 9, 10, 11, 4, 13, 14, 15>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %149 = "llvm.sub"(%143, %117) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %150 = "llvm.add"(%149, %68) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %151 = "llvm.shufflevector"(%150, %143) <{mask = array<i32: 0, 9, 10, 11, 4, 13, 14, 15>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %152 = "llvm.sub"(%145, %118) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %153 = "llvm.add"(%152, %77) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %154 = "llvm.shufflevector"(%153, %145) <{mask = array<i32: 0, 9, 10, 11, 4, 13, 14, 15>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %155 = "llvm.add"(%148, %9) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %156 = "llvm.add"(%151, %8) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %157 = "llvm.add"(%154, %8) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %158 = "llvm.ashr"(%155, %7) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %159 = "llvm.ashr"(%156, %7) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %160 = "llvm.ashr"(%157, %6) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %161 = "llvm.mul"(%160, %86) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %162 = "llvm.and"(%155, %4) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %163 = "llvm.shufflevector"(%161, %160) <{mask = array<i32: 4, 5, 6, 7, 8, 9, 10, 11>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %164 = "llvm.add"(%162, %3) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %165 = "llvm.add"(%164, %163) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %166 = "llvm.and"(%156, %4) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %167 = "llvm.add"(%158, %2) <{overflowFlags = #llvm.overflow<nsw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %168 = "llvm.add"(%167, %166) <{overflowFlags = #llvm.overflow<nsw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %169 = "llvm.and"(%157, %1) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %170 = "llvm.add"(%159, %2) <{overflowFlags = #llvm.overflow<nsw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %171 = "llvm.add"(%170, %169) <{overflowFlags = #llvm.overflow<nsw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %172 = "llvm.shufflevector"(%165, %22) <{mask = array<i32: 0, 1, 1, 0, 4, 5, 5, 4>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %173 = "llvm.shufflevector"(%168, %22) <{mask = array<i32: 0, 1, 1, 0, 4, 5, 5, 4>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %174 = "llvm.shufflevector"(%171, %22) <{mask = array<i32: 0, 1, 1, 0, 4, 5, 5, 4>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %175 = "llvm.shufflevector"(%165, %22) <{mask = array<i32: 2, 3, 2, 3, 6, 7, 6, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %176 = "llvm.shufflevector"(%168, %22) <{mask = array<i32: 2, 3, 2, 3, 6, 7, 6, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %177 = "llvm.shufflevector"(%171, %22) <{mask = array<i32: 2, 3, 2, 3, 6, 7, 6, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    "llvm.intr.lifetime.start"(%90) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%91) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%92) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.call"(%90, %91, %92, %172, %173, %174, %175, %176, %177) <{CConv = #llvm.cconv<fastcc>, callee = @fd_r43x6_quad_mul_fast, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr, !llvm.ptr, vector<8xi64>, vector<8xi64>, vector<8xi64>, vector<8xi64>, vector<8xi64>, vector<8xi64>) -> ()
    %178 = "llvm.load"(%90) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %179 = "llvm.load"(%91) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %180 = "llvm.load"(%92) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    "llvm.intr.lifetime.end"(%92) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%91) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%90) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    %181 = "llvm.lshr"(%178, %7) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %182 = "llvm.lshr"(%179, %7) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %183 = "llvm.lshr"(%180, %6) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %184 = "llvm.mul"(%183, %86) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %185 = "llvm.and"(%178, %4) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %186 = "llvm.shufflevector"(%184, %183) <{mask = array<i32: 4, 5, 6, 7, 8, 9, 10, 11>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %187 = "llvm.add"(%186, %185) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    "llvm.store"(%187, %arg0) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (vector<8xi64>, !llvm.ptr) -> ()
    %188 = "llvm.and"(%179, %4) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %189 = "llvm.add"(%188, %181) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %190 = "llvm.getelementptr"(%arg0) <{elem_type = !llvm.struct<"struct.fd_curve25519_edwards", (vector<8xi64>, vector<8xi64>, vector<8xi64>)>, inbounds, rawConstantIndices = array<i32: 0, 1>}> : (!llvm.ptr) -> !llvm.ptr
    "llvm.store"(%189, %190) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (vector<8xi64>, !llvm.ptr) -> ()
    %191 = "llvm.and"(%180, %1) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %192 = "llvm.add"(%191, %182) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %193 = "llvm.getelementptr"(%arg0) <{elem_type = !llvm.struct<"struct.fd_curve25519_edwards", (vector<8xi64>, vector<8xi64>, vector<8xi64>)>, inbounds, rawConstantIndices = array<i32: 0, 2>}> : (!llvm.ptr) -> !llvm.ptr
    "llvm.store"(%192, %193) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (vector<8xi64>, !llvm.ptr) -> ()
    %194 = "llvm.icmp"(%arg2, %21) <{predicate = 4 : i64}> : (i32, i32) -> i1
    "llvm.cond_br"(%194, %192, %189, %187, %0)[^bb3, ^bb2] <{operandSegmentSizes = array<i32: 1, 4, 0>}> : (i1, vector<8xi64>, vector<8xi64>, vector<8xi64>, i8) -> ()
  ^bb1:  // pred: ^bb3
    "llvm.store"(%282, %arg0) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (vector<8xi64>, !llvm.ptr) -> ()
    "llvm.store"(%284, %190) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (vector<8xi64>, !llvm.ptr) -> ()
    "llvm.store"(%286, %193) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (vector<8xi64>, !llvm.ptr) -> ()
    "llvm.br"()[^bb2] : () -> ()
  ^bb2:  // 2 preds: ^bb0, ^bb1
    "llvm.return"(%arg0) : (!llvm.ptr) -> ()
  ^bb3(%195: vector<8xi64>, %196: vector<8xi64>, %197: vector<8xi64>, %198: i8):  // 2 preds: ^bb0, ^bb3
    %199 = "llvm.shufflevector"(%197, %22) <{mask = array<i32: 1, 1, 2, 0, 5, 5, 6, 4>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %200 = "llvm.shufflevector"(%196, %22) <{mask = array<i32: 1, 1, 2, 0, 5, 5, 6, 4>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %201 = "llvm.shufflevector"(%195, %22) <{mask = array<i32: 1, 1, 2, 0, 5, 5, 6, 4>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %202 = "llvm.add"(%199, %197) <{overflowFlags = #llvm.overflow<nsw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %203 = "llvm.shufflevector"(%202, %199) <{mask = array<i32: 0, 9, 10, 11, 4, 13, 14, 15>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %204 = "llvm.add"(%200, %196) <{overflowFlags = #llvm.overflow<nsw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %205 = "llvm.shufflevector"(%204, %200) <{mask = array<i32: 0, 9, 10, 11, 4, 13, 14, 15>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %206 = "llvm.add"(%201, %195) <{overflowFlags = #llvm.overflow<nsw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %207 = "llvm.shufflevector"(%206, %201) <{mask = array<i32: 0, 9, 10, 11, 4, 13, 14, 15>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    "llvm.intr.lifetime.start"(%93) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%94) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%95) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.call"(%93, %94, %95, %203, %205, %207) <{CConv = #llvm.cconv<fastcc>, callee = @fd_r43x6_quad_sqr_fast, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr, !llvm.ptr, vector<8xi64>, vector<8xi64>, vector<8xi64>) -> ()
    %208 = "llvm.load"(%93) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %209 = "llvm.load"(%94) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %210 = "llvm.load"(%95) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    "llvm.intr.lifetime.end"(%95) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%94) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%93) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    %211 = "llvm.shl"(%208, %19) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %212 = "llvm.shl"(%209, %19) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %213 = "llvm.shl"(%210, %19) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %214 = "llvm.shufflevector"(%211, %22) <{mask = array<i32: 3, 3, 3, 3, 7, 7, 7, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %215 = "llvm.shufflevector"(%212, %22) <{mask = array<i32: 3, 3, 3, 3, 7, 7, 7, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %216 = "llvm.shufflevector"(%213, %22) <{mask = array<i32: 3, 3, 3, 3, 7, 7, 7, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %217 = "llvm.shufflevector"(%211, %22) <{mask = array<i32: 1, 1, 1, 1, 5, 5, 5, 5>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %218 = "llvm.shufflevector"(%212, %22) <{mask = array<i32: 1, 1, 1, 1, 5, 5, 5, 5>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %219 = "llvm.shufflevector"(%213, %22) <{mask = array<i32: 1, 1, 1, 1, 5, 5, 5, 5>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %220 = "llvm.add"(%214, %217) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %221 = "llvm.shufflevector"(%220, %214) <{mask = array<i32: 0, 9, 10, 3, 4, 13, 14, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %222 = "llvm.add"(%215, %218) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %223 = "llvm.shufflevector"(%222, %215) <{mask = array<i32: 0, 9, 10, 3, 4, 13, 14, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %224 = "llvm.add"(%216, %219) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %225 = "llvm.shufflevector"(%224, %216) <{mask = array<i32: 0, 9, 10, 3, 4, 13, 14, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %226 = "llvm.sub"(%221, %217) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %227 = "llvm.add"(%226, %32) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %228 = "llvm.shufflevector"(%221, %227) <{mask = array<i32: 0, 9, 10, 3, 4, 13, 14, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %229 = "llvm.sub"(%223, %218) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %230 = "llvm.add"(%229, %41) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %231 = "llvm.shufflevector"(%223, %230) <{mask = array<i32: 0, 9, 10, 3, 4, 13, 14, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %232 = "llvm.sub"(%225, %219) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %233 = "llvm.add"(%232, %50) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %234 = "llvm.shufflevector"(%225, %233) <{mask = array<i32: 0, 9, 10, 3, 4, 13, 14, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %235 = "llvm.add"(%228, %211) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %236 = "llvm.shufflevector"(%228, %235) <{mask = array<i32: 0, 1, 10, 3, 4, 5, 14, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %237 = "llvm.add"(%231, %212) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %238 = "llvm.shufflevector"(%231, %237) <{mask = array<i32: 0, 1, 10, 3, 4, 5, 14, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %239 = "llvm.add"(%234, %213) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %240 = "llvm.shufflevector"(%234, %239) <{mask = array<i32: 0, 1, 10, 3, 4, 5, 14, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %241 = "llvm.sub"(%236, %211) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %242 = "llvm.add"(%241, %59) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %243 = "llvm.shufflevector"(%242, %236) <{mask = array<i32: 0, 9, 10, 11, 4, 13, 14, 15>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %244 = "llvm.sub"(%238, %212) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %245 = "llvm.add"(%244, %68) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %246 = "llvm.shufflevector"(%245, %238) <{mask = array<i32: 0, 9, 10, 11, 4, 13, 14, 15>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %247 = "llvm.sub"(%240, %213) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %248 = "llvm.add"(%247, %77) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %249 = "llvm.shufflevector"(%248, %240) <{mask = array<i32: 0, 9, 10, 11, 4, 13, 14, 15>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %250 = "llvm.add"(%243, %9) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %251 = "llvm.add"(%246, %8) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %252 = "llvm.add"(%249, %8) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %253 = "llvm.ashr"(%250, %7) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %254 = "llvm.ashr"(%251, %7) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %255 = "llvm.ashr"(%252, %6) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %256 = "llvm.mul"(%255, %86) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %257 = "llvm.and"(%250, %4) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %258 = "llvm.shufflevector"(%256, %255) <{mask = array<i32: 4, 5, 6, 7, 8, 9, 10, 11>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %259 = "llvm.add"(%257, %3) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %260 = "llvm.add"(%259, %258) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %261 = "llvm.and"(%251, %4) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %262 = "llvm.add"(%253, %2) <{overflowFlags = #llvm.overflow<nsw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %263 = "llvm.add"(%262, %261) <{overflowFlags = #llvm.overflow<nsw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %264 = "llvm.and"(%252, %1) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %265 = "llvm.add"(%254, %2) <{overflowFlags = #llvm.overflow<nsw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %266 = "llvm.add"(%265, %264) <{overflowFlags = #llvm.overflow<nsw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %267 = "llvm.shufflevector"(%260, %22) <{mask = array<i32: 0, 1, 1, 0, 4, 5, 5, 4>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %268 = "llvm.shufflevector"(%263, %22) <{mask = array<i32: 0, 1, 1, 0, 4, 5, 5, 4>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %269 = "llvm.shufflevector"(%266, %22) <{mask = array<i32: 0, 1, 1, 0, 4, 5, 5, 4>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %270 = "llvm.shufflevector"(%260, %22) <{mask = array<i32: 2, 3, 2, 3, 6, 7, 6, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %271 = "llvm.shufflevector"(%263, %22) <{mask = array<i32: 2, 3, 2, 3, 6, 7, 6, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %272 = "llvm.shufflevector"(%266, %22) <{mask = array<i32: 2, 3, 2, 3, 6, 7, 6, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    "llvm.intr.lifetime.start"(%96) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%97) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%98) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.call"(%96, %97, %98, %267, %268, %269, %270, %271, %272) <{CConv = #llvm.cconv<fastcc>, callee = @fd_r43x6_quad_mul_fast, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr, !llvm.ptr, vector<8xi64>, vector<8xi64>, vector<8xi64>, vector<8xi64>, vector<8xi64>, vector<8xi64>) -> ()
    %273 = "llvm.load"(%96) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %274 = "llvm.load"(%97) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %275 = "llvm.load"(%98) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    "llvm.intr.lifetime.end"(%98) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%97) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%96) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    %276 = "llvm.lshr"(%273, %7) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %277 = "llvm.lshr"(%274, %7) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %278 = "llvm.lshr"(%275, %6) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %279 = "llvm.mul"(%278, %86) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %280 = "llvm.and"(%273, %4) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %281 = "llvm.shufflevector"(%279, %278) <{mask = array<i32: 4, 5, 6, 7, 8, 9, 10, 11>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %282 = "llvm.add"(%281, %280) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %283 = "llvm.and"(%274, %4) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %284 = "llvm.add"(%283, %276) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %285 = "llvm.and"(%275, %1) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %286 = "llvm.add"(%285, %277) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %287 = "llvm.add"(%198, %0) <{overflowFlags = #llvm.overflow<none>}> : (i8, i8) -> i8
    %288 = "llvm.zext"(%287) : (i8) -> i32
    %289 = "llvm.icmp"(%288, %arg2) <{predicate = 6 : i64}> : (i32, i32) -> i1
    "llvm.cond_br"(%289, %286, %284, %282, %287)[^bb3, ^bb1] <{loop_annotation = #loop_annotation, operandSegmentSizes = array<i32: 1, 4, 0>}> : (i1, vector<8xi64>, vector<8xi64>, vector<8xi64>, i8) -> ()
}
]

sllvm_cfg_def fd_ed25519_point_dbln :
    Cfg (Ctxt.ofList [SLLVM.Ty.bitvec 32, SLLVM.Ty.ptr, SLLVM.Ty.ptr])
      [SLLVM.Ty.ptr] :=
  [sllvm_cfg_of| fd_ed25519_point_dbln_region with
    @fd_r43x6_quad_sqr_fast := fd_r43x6_quad_sqr_fast,
    @fd_r43x6_quad_mul_fast := fd_r43x6_quad_mul_fast]

end Firedancer.Avx512
