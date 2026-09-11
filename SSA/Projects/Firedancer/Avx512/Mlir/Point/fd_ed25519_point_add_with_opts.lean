/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
-- build/native/gcc/mlir_canonicalized/avx512/region/fd_ed25519_point_add_with_opts.mlir
import SSA.Projects.SLLVM.Cfg
import SSA.Projects.Firedancer.Avx512.Mlir.Field.fd_r43x6_quad_mul_fast

namespace Firedancer.Avx512
open LeanMLIR SLLVM

def fd_ed25519_point_add_with_opts_region : MLIR.AST.Region 0 := [mlir_region|
{
  ^bb0(%arg0: !llvm.ptr, %arg1: !llvm.ptr, %arg2: !llvm.ptr, %arg3: i32):
    %0 = "llvm.mlir.constant"() <{value = dense<[0, 0, 0, 15037786634, 0, 0, 0, 309467527341]> : vector<8xi64>}> : () -> vector<8xi64>
    %1 = "llvm.mlir.constant"() <{value = dense<[0, 0, 0, 507525298899, 0, 0, 0, 6596238350568]> : vector<8xi64>}> : () -> vector<8xi64>
    %2 = "llvm.mlir.constant"() <{value = dense<[1, 1, 1, 3934839304537, 0, 0, 0, 521695520920]> : vector<8xi64>}> : () -> vector<8xi64>
    %3 = "llvm.mlir.constant"() <{value = dense<[8796093022207, 8796093022207, 8796093022207, 8796093022207, 1099511627775, 1099511627775, 1099511627775, 1099511627775]> : vector<8xi64>}> : () -> vector<8xi64>
    %4 = "llvm.mlir.constant"() <{value = dense<1048576> : vector<8xi64>}> : () -> vector<8xi64>
    %5 = "llvm.mlir.constant"() <{value = dense<[159383552, 159383552, 159383552, 159383552, 1048576, 1048576, 1048576, 1048576]> : vector<8xi64>}> : () -> vector<8xi64>
    %6 = "llvm.mlir.constant"() <{value = dense<8796093022207> : vector<8xi64>}> : () -> vector<8xi64>
    %7 = "llvm.mlir.constant"() <{value = 19 : i64}> : () -> i64
    %8 = "llvm.mlir.constant"() <{value = dense<[43, 43, 43, 43, 40, 40, 40, 40]> : vector<8xi64>}> : () -> vector<8xi64>
    %9 = "llvm.mlir.constant"() <{value = dense<43> : vector<8xi64>}> : () -> vector<8xi64>
    %10 = "llvm.mlir.constant"() <{value = dense<-1048576> : vector<8xi64>}> : () -> vector<8xi64>
    %11 = "llvm.mlir.constant"() <{value = dense<[-159383552, -159383552, -159383552, -159383552, -1048576, -1048576, -1048576, -1048576]> : vector<8xi64>}> : () -> vector<8xi64>
    %12 = "llvm.mlir.constant"() <{value = 1099511627775 : i64}> : () -> i64
    %13 = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
    %14 = "llvm.mlir.constant"() <{value = 6 : i32}> : () -> i32
    %15 = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
    %16 = "llvm.mlir.constant"() <{value = 4 : i32}> : () -> i32
    %17 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %18 = "llvm.mlir.constant"() <{value = 8796093022189 : i64}> : () -> i64
    %19 = "llvm.mlir.constant"() <{value = 8796093022207 : i64}> : () -> i64
    %20 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %21 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %22 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %23 = "llvm.mlir.poison"() : () -> vector<8xi64>
    %24 = "llvm.mlir.poison"() : () -> i64
    %25 = "llvm.mlir.undef"() : () -> vector<8xi64>
    %26 = "llvm.insertelement"(%25, %18, %21) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %27 = "llvm.insertelement"(%26, %24, %20) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %28 = "llvm.insertelement"(%27, %24, %22) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %29 = "llvm.insertelement"(%28, %24, %17) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %30 = "llvm.insertelement"(%29, %19, %16) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %31 = "llvm.insertelement"(%30, %24, %15) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %32 = "llvm.insertelement"(%31, %24, %14) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %33 = "llvm.insertelement"(%32, %24, %13) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %34 = "llvm.mlir.undef"() : () -> vector<8xi64>
    %35 = "llvm.insertelement"(%34, %19, %21) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %36 = "llvm.insertelement"(%35, %24, %20) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %37 = "llvm.insertelement"(%36, %24, %22) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %38 = "llvm.insertelement"(%37, %24, %17) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %39 = "llvm.insertelement"(%38, %19, %16) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %40 = "llvm.insertelement"(%39, %24, %15) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %41 = "llvm.insertelement"(%40, %24, %14) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %42 = "llvm.insertelement"(%41, %24, %13) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %43 = "llvm.mlir.undef"() : () -> vector<8xi64>
    %44 = "llvm.insertelement"(%43, %19, %21) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %45 = "llvm.insertelement"(%44, %24, %20) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %46 = "llvm.insertelement"(%45, %24, %22) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %47 = "llvm.insertelement"(%46, %24, %17) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %48 = "llvm.insertelement"(%47, %12, %16) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %49 = "llvm.insertelement"(%48, %24, %15) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %50 = "llvm.insertelement"(%49, %24, %14) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %51 = "llvm.insertelement"(%50, %24, %13) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %52 = "llvm.mlir.undef"() : () -> vector<8xi64>
    %53 = "llvm.insertelement"(%52, %24, %21) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %54 = "llvm.insertelement"(%53, %24, %20) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %55 = "llvm.insertelement"(%54, %24, %22) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %56 = "llvm.insertelement"(%55, %24, %17) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %57 = "llvm.insertelement"(%56, %7, %16) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %58 = "llvm.insertelement"(%57, %7, %15) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %59 = "llvm.insertelement"(%58, %7, %14) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %60 = "llvm.insertelement"(%59, %7, %13) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %61 = "llvm.mlir.undef"() : () -> vector<8xi64>
    %62 = "llvm.insertelement"(%61, %18, %21) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %63 = "llvm.insertelement"(%62, %24, %20) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %64 = "llvm.insertelement"(%63, %24, %22) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %65 = "llvm.insertelement"(%64, %18, %17) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %66 = "llvm.insertelement"(%65, %19, %16) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %67 = "llvm.insertelement"(%66, %24, %15) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %68 = "llvm.insertelement"(%67, %24, %14) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %69 = "llvm.insertelement"(%68, %19, %13) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %70 = "llvm.mlir.undef"() : () -> vector<8xi64>
    %71 = "llvm.insertelement"(%70, %19, %21) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %72 = "llvm.insertelement"(%71, %24, %20) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %73 = "llvm.insertelement"(%72, %24, %22) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %74 = "llvm.insertelement"(%73, %19, %17) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %75 = "llvm.insertelement"(%74, %19, %16) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %76 = "llvm.insertelement"(%75, %24, %15) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %77 = "llvm.insertelement"(%76, %24, %14) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %78 = "llvm.insertelement"(%77, %19, %13) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %79 = "llvm.mlir.undef"() : () -> vector<8xi64>
    %80 = "llvm.insertelement"(%79, %19, %21) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %81 = "llvm.insertelement"(%80, %24, %20) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %82 = "llvm.insertelement"(%81, %24, %22) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %83 = "llvm.insertelement"(%82, %19, %17) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %84 = "llvm.insertelement"(%83, %12, %16) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %85 = "llvm.insertelement"(%84, %24, %15) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %86 = "llvm.insertelement"(%85, %24, %14) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %87 = "llvm.insertelement"(%86, %12, %13) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %88 = "llvm.alloca"(%20) <{alignment = 64 : i64, elem_type = vector<8xi64>}> : (i32) -> !llvm.ptr
    %89 = "llvm.alloca"(%20) <{alignment = 64 : i64, elem_type = vector<8xi64>}> : (i32) -> !llvm.ptr
    %90 = "llvm.alloca"(%20) <{alignment = 64 : i64, elem_type = vector<8xi64>}> : (i32) -> !llvm.ptr
    %91 = "llvm.alloca"(%20) <{alignment = 64 : i64, elem_type = vector<8xi64>}> : (i32) -> !llvm.ptr
    %92 = "llvm.alloca"(%20) <{alignment = 64 : i64, elem_type = vector<8xi64>}> : (i32) -> !llvm.ptr
    %93 = "llvm.alloca"(%20) <{alignment = 64 : i64, elem_type = vector<8xi64>}> : (i32) -> !llvm.ptr
    %94 = "llvm.alloca"(%20) <{alignment = 64 : i64, elem_type = vector<8xi64>}> : (i32) -> !llvm.ptr
    %95 = "llvm.alloca"(%20) <{alignment = 64 : i64, elem_type = vector<8xi64>}> : (i32) -> !llvm.ptr
    %96 = "llvm.alloca"(%20) <{alignment = 64 : i64, elem_type = vector<8xi64>}> : (i32) -> !llvm.ptr
    %97 = "llvm.alloca"(%20) <{alignment = 64 : i64, elem_type = vector<8xi64>}> : (i32) -> !llvm.ptr
    %98 = "llvm.alloca"(%20) <{alignment = 64 : i64, elem_type = vector<8xi64>}> : (i32) -> !llvm.ptr
    %99 = "llvm.alloca"(%20) <{alignment = 64 : i64, elem_type = vector<8xi64>}> : (i32) -> !llvm.ptr
    %100 = "llvm.alloca"(%20) <{alignment = 64 : i64, elem_type = vector<8xi64>}> : (i32) -> !llvm.ptr
    %101 = "llvm.alloca"(%20) <{alignment = 64 : i64, elem_type = vector<8xi64>}> : (i32) -> !llvm.ptr
    %102 = "llvm.alloca"(%20) <{alignment = 64 : i64, elem_type = vector<8xi64>}> : (i32) -> !llvm.ptr
    %103 = "llvm.icmp"(%arg3, %21) <{predicate = 0 : i64}> : (i32, i32) -> i1
    "llvm.cond_br"(%103)[^bb2, ^bb1] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
  ^bb1:  // pred: ^bb0
    %104 = "llvm.load"(%arg2) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %105 = "llvm.getelementptr"(%arg2) <{elem_type = !llvm.struct<"struct.fd_curve25519_edwards", (vector<8xi64>, vector<8xi64>, vector<8xi64>)>, inbounds, rawConstantIndices = array<i32: 0, 1>}> : (!llvm.ptr) -> !llvm.ptr
    %106 = "llvm.load"(%105) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %107 = "llvm.getelementptr"(%arg2) <{elem_type = !llvm.struct<"struct.fd_curve25519_edwards", (vector<8xi64>, vector<8xi64>, vector<8xi64>)>, inbounds, rawConstantIndices = array<i32: 0, 2>}> : (!llvm.ptr) -> !llvm.ptr
    %108 = "llvm.load"(%107) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %109 = "llvm.load"(%arg1) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %110 = "llvm.shufflevector"(%109, %23) <{mask = array<i32: 1, 0, 2, 3, 5, 4, 6, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %111 = "llvm.getelementptr"(%arg1) <{elem_type = !llvm.struct<"struct.fd_curve25519_edwards", (vector<8xi64>, vector<8xi64>, vector<8xi64>)>, inbounds, rawConstantIndices = array<i32: 0, 1>}> : (!llvm.ptr) -> !llvm.ptr
    %112 = "llvm.load"(%111) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %113 = "llvm.shufflevector"(%112, %23) <{mask = array<i32: 1, 0, 2, 3, 5, 4, 6, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %114 = "llvm.getelementptr"(%arg1) <{elem_type = !llvm.struct<"struct.fd_curve25519_edwards", (vector<8xi64>, vector<8xi64>, vector<8xi64>)>, inbounds, rawConstantIndices = array<i32: 0, 2>}> : (!llvm.ptr) -> !llvm.ptr
    %115 = "llvm.load"(%114) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %116 = "llvm.shufflevector"(%115, %23) <{mask = array<i32: 1, 0, 2, 3, 5, 4, 6, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %117 = "llvm.sub"(%110, %109) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %118 = "llvm.add"(%117, %33) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %119 = "llvm.shufflevector"(%118, %110) <{mask = array<i32: 0, 9, 10, 11, 4, 13, 14, 15>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %120 = "llvm.sub"(%113, %112) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %121 = "llvm.add"(%120, %42) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %122 = "llvm.shufflevector"(%121, %113) <{mask = array<i32: 0, 9, 10, 11, 4, 13, 14, 15>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %123 = "llvm.sub"(%116, %115) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %124 = "llvm.add"(%123, %51) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %125 = "llvm.shufflevector"(%124, %116) <{mask = array<i32: 0, 9, 10, 11, 4, 13, 14, 15>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %126 = "llvm.add"(%119, %109) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %127 = "llvm.shufflevector"(%119, %126) <{mask = array<i32: 0, 9, 10, 3, 4, 13, 14, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %128 = "llvm.add"(%122, %112) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %129 = "llvm.shufflevector"(%122, %128) <{mask = array<i32: 0, 9, 10, 3, 4, 13, 14, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %130 = "llvm.add"(%125, %115) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %131 = "llvm.shufflevector"(%125, %130) <{mask = array<i32: 0, 9, 10, 3, 4, 13, 14, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %132 = "llvm.add"(%127, %11) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %133 = "llvm.add"(%129, %10) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %134 = "llvm.add"(%131, %10) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %135 = "llvm.ashr"(%132, %9) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %136 = "llvm.ashr"(%133, %9) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %137 = "llvm.ashr"(%134, %8) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %138 = "llvm.mul"(%137, %60) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %139 = "llvm.and"(%132, %6) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %140 = "llvm.shufflevector"(%138, %137) <{mask = array<i32: 4, 5, 6, 7, 8, 9, 10, 11>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %141 = "llvm.add"(%139, %5) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %142 = "llvm.add"(%141, %140) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %143 = "llvm.and"(%133, %6) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %144 = "llvm.add"(%135, %4) <{overflowFlags = #llvm.overflow<nsw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %145 = "llvm.add"(%144, %143) <{overflowFlags = #llvm.overflow<nsw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %146 = "llvm.and"(%134, %3) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %147 = "llvm.add"(%136, %4) <{overflowFlags = #llvm.overflow<nsw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %148 = "llvm.add"(%147, %146) <{overflowFlags = #llvm.overflow<nsw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    "llvm.intr.lifetime.start"(%88) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%89) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%90) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.call"(%88, %89, %90, %104, %106, %108, %142, %145, %148) <{CConv = #llvm.cconv<fastcc>, callee = @fd_r43x6_quad_mul_fast, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr, !llvm.ptr, vector<8xi64>, vector<8xi64>, vector<8xi64>, vector<8xi64>, vector<8xi64>, vector<8xi64>) -> ()
    %149 = "llvm.load"(%88) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %150 = "llvm.load"(%89) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %151 = "llvm.load"(%90) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    "llvm.intr.lifetime.end"(%90) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%89) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%88) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    %152 = "llvm.lshr"(%149, %9) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %153 = "llvm.lshr"(%150, %9) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %154 = "llvm.lshr"(%151, %8) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %155 = "llvm.mul"(%154, %60) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %156 = "llvm.and"(%149, %6) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %157 = "llvm.shufflevector"(%155, %154) <{mask = array<i32: 4, 5, 6, 7, 8, 9, 10, 11>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %158 = "llvm.add"(%157, %156) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %159 = "llvm.and"(%150, %6) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %160 = "llvm.add"(%159, %152) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %161 = "llvm.and"(%151, %3) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %162 = "llvm.add"(%161, %153) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %163 = "llvm.shufflevector"(%158, %23) <{mask = array<i32: 1, 0, 3, 2, 5, 4, 7, 6>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %164 = "llvm.shufflevector"(%160, %23) <{mask = array<i32: 1, 0, 3, 2, 5, 4, 7, 6>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %165 = "llvm.shufflevector"(%162, %23) <{mask = array<i32: 1, 0, 3, 2, 5, 4, 7, 6>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %166 = "llvm.sub"(%163, %158) <{overflowFlags = #llvm.overflow<nsw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %167 = "llvm.add"(%166, %69) <{overflowFlags = #llvm.overflow<nsw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %168 = "llvm.shufflevector"(%167, %163) <{mask = array<i32: 0, 9, 10, 3, 4, 13, 14, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %169 = "llvm.sub"(%164, %160) <{overflowFlags = #llvm.overflow<nsw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %170 = "llvm.add"(%169, %78) <{overflowFlags = #llvm.overflow<nsw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %171 = "llvm.shufflevector"(%170, %164) <{mask = array<i32: 0, 9, 10, 3, 4, 13, 14, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %172 = "llvm.sub"(%165, %162) <{overflowFlags = #llvm.overflow<nsw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %173 = "llvm.add"(%172, %87) <{overflowFlags = #llvm.overflow<nsw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %174 = "llvm.shufflevector"(%173, %165) <{mask = array<i32: 0, 9, 10, 3, 4, 13, 14, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %175 = "llvm.add"(%168, %158) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %176 = "llvm.shufflevector"(%168, %175) <{mask = array<i32: 0, 9, 10, 3, 4, 13, 14, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %177 = "llvm.add"(%171, %160) <{overflowFlags = #llvm.overflow<nsw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %178 = "llvm.shufflevector"(%171, %177) <{mask = array<i32: 0, 9, 10, 3, 4, 13, 14, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %179 = "llvm.add"(%174, %162) <{overflowFlags = #llvm.overflow<nsw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %180 = "llvm.shufflevector"(%174, %179) <{mask = array<i32: 0, 9, 10, 3, 4, 13, 14, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %181 = "llvm.add"(%176, %11) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %182 = "llvm.add"(%178, %10) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %183 = "llvm.add"(%180, %10) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %184 = "llvm.ashr"(%181, %9) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %185 = "llvm.ashr"(%182, %9) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %186 = "llvm.ashr"(%183, %8) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %187 = "llvm.mul"(%186, %60) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %188 = "llvm.and"(%181, %6) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %189 = "llvm.shufflevector"(%187, %186) <{mask = array<i32: 4, 5, 6, 7, 8, 9, 10, 11>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %190 = "llvm.add"(%189, %5) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %191 = "llvm.add"(%190, %188) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %192 = "llvm.and"(%182, %6) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %193 = "llvm.add"(%192, %4) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %194 = "llvm.add"(%193, %184) <{overflowFlags = #llvm.overflow<nsw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %195 = "llvm.and"(%183, %3) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %196 = "llvm.add"(%185, %4) <{overflowFlags = #llvm.overflow<nsw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %197 = "llvm.add"(%196, %195) <{overflowFlags = #llvm.overflow<nsw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %198 = "llvm.shufflevector"(%191, %23) <{mask = array<i32: 0, 2, 2, 0, 4, 6, 6, 4>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %199 = "llvm.shufflevector"(%194, %23) <{mask = array<i32: 0, 2, 2, 0, 4, 6, 6, 4>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %200 = "llvm.shufflevector"(%197, %23) <{mask = array<i32: 0, 2, 2, 0, 4, 6, 6, 4>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %201 = "llvm.shufflevector"(%191, %23) <{mask = array<i32: 3, 1, 3, 1, 7, 5, 7, 5>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %202 = "llvm.shufflevector"(%194, %23) <{mask = array<i32: 3, 1, 3, 1, 7, 5, 7, 5>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %203 = "llvm.shufflevector"(%197, %23) <{mask = array<i32: 3, 1, 3, 1, 7, 5, 7, 5>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    "llvm.intr.lifetime.start"(%91) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%92) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%93) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.call"(%91, %92, %93, %198, %199, %200, %201, %202, %203) <{CConv = #llvm.cconv<fastcc>, callee = @fd_r43x6_quad_mul_fast, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr, !llvm.ptr, vector<8xi64>, vector<8xi64>, vector<8xi64>, vector<8xi64>, vector<8xi64>, vector<8xi64>) -> ()
    %204 = "llvm.load"(%91) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %205 = "llvm.load"(%92) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %206 = "llvm.load"(%93) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    "llvm.intr.lifetime.end"(%93) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%92) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%91) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.br"(%204, %205, %206)[^bb3] : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> ()
  ^bb2:  // pred: ^bb0
    %207 = "llvm.load"(%arg1) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %208 = "llvm.shufflevector"(%207, %23) <{mask = array<i32: 1, 0, 2, 3, 5, 4, 6, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %209 = "llvm.getelementptr"(%arg1) <{elem_type = !llvm.struct<"struct.fd_curve25519_edwards", (vector<8xi64>, vector<8xi64>, vector<8xi64>)>, inbounds, rawConstantIndices = array<i32: 0, 1>}> : (!llvm.ptr) -> !llvm.ptr
    %210 = "llvm.load"(%209) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %211 = "llvm.shufflevector"(%210, %23) <{mask = array<i32: 1, 0, 2, 3, 5, 4, 6, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %212 = "llvm.getelementptr"(%arg1) <{elem_type = !llvm.struct<"struct.fd_curve25519_edwards", (vector<8xi64>, vector<8xi64>, vector<8xi64>)>, inbounds, rawConstantIndices = array<i32: 0, 2>}> : (!llvm.ptr) -> !llvm.ptr
    %213 = "llvm.load"(%212) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %214 = "llvm.shufflevector"(%213, %23) <{mask = array<i32: 1, 0, 2, 3, 5, 4, 6, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %215 = "llvm.load"(%arg2) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %216 = "llvm.shufflevector"(%215, %23) <{mask = array<i32: 1, 0, 2, 3, 5, 4, 6, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %217 = "llvm.getelementptr"(%arg2) <{elem_type = !llvm.struct<"struct.fd_curve25519_edwards", (vector<8xi64>, vector<8xi64>, vector<8xi64>)>, inbounds, rawConstantIndices = array<i32: 0, 1>}> : (!llvm.ptr) -> !llvm.ptr
    %218 = "llvm.load"(%217) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %219 = "llvm.shufflevector"(%218, %23) <{mask = array<i32: 1, 0, 2, 3, 5, 4, 6, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %220 = "llvm.getelementptr"(%arg2) <{elem_type = !llvm.struct<"struct.fd_curve25519_edwards", (vector<8xi64>, vector<8xi64>, vector<8xi64>)>, inbounds, rawConstantIndices = array<i32: 0, 2>}> : (!llvm.ptr) -> !llvm.ptr
    %221 = "llvm.load"(%220) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %222 = "llvm.shufflevector"(%221, %23) <{mask = array<i32: 1, 0, 2, 3, 5, 4, 6, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %223 = "llvm.sub"(%208, %207) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %224 = "llvm.add"(%223, %33) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %225 = "llvm.shufflevector"(%224, %208) <{mask = array<i32: 0, 9, 10, 11, 4, 13, 14, 15>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %226 = "llvm.sub"(%211, %210) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %227 = "llvm.add"(%226, %42) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %228 = "llvm.shufflevector"(%227, %211) <{mask = array<i32: 0, 9, 10, 11, 4, 13, 14, 15>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %229 = "llvm.sub"(%214, %213) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %230 = "llvm.add"(%229, %51) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %231 = "llvm.shufflevector"(%230, %214) <{mask = array<i32: 0, 9, 10, 11, 4, 13, 14, 15>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %232 = "llvm.sub"(%216, %215) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %233 = "llvm.add"(%232, %33) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %234 = "llvm.shufflevector"(%233, %216) <{mask = array<i32: 0, 9, 10, 11, 4, 13, 14, 15>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %235 = "llvm.sub"(%219, %218) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %236 = "llvm.add"(%235, %42) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %237 = "llvm.shufflevector"(%236, %219) <{mask = array<i32: 0, 9, 10, 11, 4, 13, 14, 15>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %238 = "llvm.sub"(%222, %221) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %239 = "llvm.add"(%238, %51) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %240 = "llvm.shufflevector"(%239, %222) <{mask = array<i32: 0, 9, 10, 11, 4, 13, 14, 15>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %241 = "llvm.add"(%225, %207) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %242 = "llvm.shufflevector"(%225, %241) <{mask = array<i32: 0, 9, 10, 3, 4, 13, 14, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %243 = "llvm.add"(%228, %210) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %244 = "llvm.shufflevector"(%228, %243) <{mask = array<i32: 0, 9, 10, 3, 4, 13, 14, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %245 = "llvm.add"(%231, %213) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %246 = "llvm.shufflevector"(%231, %245) <{mask = array<i32: 0, 9, 10, 3, 4, 13, 14, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %247 = "llvm.add"(%234, %215) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %248 = "llvm.shufflevector"(%234, %247) <{mask = array<i32: 0, 9, 2, 3, 4, 13, 6, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %249 = "llvm.add"(%237, %218) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %250 = "llvm.shufflevector"(%237, %249) <{mask = array<i32: 0, 9, 2, 3, 4, 13, 6, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %251 = "llvm.add"(%240, %221) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %252 = "llvm.shufflevector"(%240, %251) <{mask = array<i32: 0, 9, 2, 3, 4, 13, 6, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %253 = "llvm.add"(%242, %11) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %254 = "llvm.add"(%244, %10) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %255 = "llvm.add"(%246, %10) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %256 = "llvm.ashr"(%253, %9) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %257 = "llvm.ashr"(%254, %9) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %258 = "llvm.ashr"(%255, %8) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %259 = "llvm.mul"(%258, %60) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %260 = "llvm.and"(%253, %6) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %261 = "llvm.shufflevector"(%259, %258) <{mask = array<i32: 4, 5, 6, 7, 8, 9, 10, 11>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %262 = "llvm.add"(%260, %5) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %263 = "llvm.add"(%262, %261) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %264 = "llvm.and"(%254, %6) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %265 = "llvm.add"(%256, %4) <{overflowFlags = #llvm.overflow<nsw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %266 = "llvm.add"(%265, %264) <{overflowFlags = #llvm.overflow<nsw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %267 = "llvm.and"(%255, %3) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %268 = "llvm.add"(%257, %4) <{overflowFlags = #llvm.overflow<nsw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %269 = "llvm.add"(%268, %267) <{overflowFlags = #llvm.overflow<nsw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %270 = "llvm.add"(%248, %11) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %271 = "llvm.add"(%250, %10) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %272 = "llvm.add"(%252, %10) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %273 = "llvm.ashr"(%270, %9) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %274 = "llvm.ashr"(%271, %9) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %275 = "llvm.ashr"(%272, %8) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %276 = "llvm.mul"(%275, %60) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %277 = "llvm.and"(%270, %6) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %278 = "llvm.shufflevector"(%276, %275) <{mask = array<i32: 4, 5, 6, 7, 8, 9, 10, 11>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %279 = "llvm.add"(%277, %5) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %280 = "llvm.add"(%279, %278) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %281 = "llvm.and"(%271, %6) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %282 = "llvm.add"(%273, %4) <{overflowFlags = #llvm.overflow<nsw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %283 = "llvm.add"(%282, %281) <{overflowFlags = #llvm.overflow<nsw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %284 = "llvm.and"(%272, %3) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %285 = "llvm.add"(%274, %4) <{overflowFlags = #llvm.overflow<nsw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %286 = "llvm.add"(%285, %284) <{overflowFlags = #llvm.overflow<nsw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    "llvm.intr.lifetime.start"(%94) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%95) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%96) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.call"(%94, %95, %96, %263, %266, %269, %2, %1, %0) <{CConv = #llvm.cconv<fastcc>, callee = @fd_r43x6_quad_mul_fast, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr, !llvm.ptr, vector<8xi64>, vector<8xi64>, vector<8xi64>, vector<8xi64>, vector<8xi64>, vector<8xi64>) -> ()
    %287 = "llvm.load"(%94) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %288 = "llvm.load"(%95) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %289 = "llvm.load"(%96) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    "llvm.intr.lifetime.end"(%96) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%95) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%94) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    %290 = "llvm.lshr"(%287, %9) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %291 = "llvm.lshr"(%288, %9) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %292 = "llvm.lshr"(%289, %8) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %293 = "llvm.mul"(%292, %60) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %294 = "llvm.and"(%287, %6) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %295 = "llvm.shufflevector"(%293, %292) <{mask = array<i32: 4, 5, 6, 7, 8, 9, 10, 11>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %296 = "llvm.add"(%295, %294) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %297 = "llvm.and"(%288, %6) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %298 = "llvm.add"(%297, %290) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %299 = "llvm.and"(%289, %3) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %300 = "llvm.add"(%299, %291) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    "llvm.intr.lifetime.start"(%97) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%98) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%99) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.call"(%97, %98, %99, %296, %298, %300, %280, %283, %286) <{CConv = #llvm.cconv<fastcc>, callee = @fd_r43x6_quad_mul_fast, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr, !llvm.ptr, vector<8xi64>, vector<8xi64>, vector<8xi64>, vector<8xi64>, vector<8xi64>, vector<8xi64>) -> ()
    %301 = "llvm.load"(%97) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %302 = "llvm.load"(%98) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %303 = "llvm.load"(%99) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    "llvm.intr.lifetime.end"(%99) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%98) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%97) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    %304 = "llvm.shufflevector"(%301, %23) <{mask = array<i32: 1, 0, 3, 2, 5, 4, 7, 6>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %305 = "llvm.shufflevector"(%302, %23) <{mask = array<i32: 1, 0, 3, 2, 5, 4, 7, 6>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %306 = "llvm.shufflevector"(%303, %23) <{mask = array<i32: 1, 0, 3, 2, 5, 4, 7, 6>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %307 = "llvm.sub"(%304, %301) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %308 = "llvm.add"(%307, %69) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %309 = "llvm.shufflevector"(%308, %304) <{mask = array<i32: 0, 9, 10, 3, 4, 13, 14, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %310 = "llvm.sub"(%305, %302) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %311 = "llvm.add"(%310, %78) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %312 = "llvm.shufflevector"(%311, %305) <{mask = array<i32: 0, 9, 10, 3, 4, 13, 14, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %313 = "llvm.sub"(%306, %303) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %314 = "llvm.add"(%313, %87) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %315 = "llvm.shufflevector"(%314, %306) <{mask = array<i32: 0, 9, 10, 3, 4, 13, 14, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %316 = "llvm.add"(%309, %301) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %317 = "llvm.shufflevector"(%309, %316) <{mask = array<i32: 0, 9, 10, 3, 4, 13, 14, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %318 = "llvm.add"(%312, %302) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %319 = "llvm.shufflevector"(%312, %318) <{mask = array<i32: 0, 9, 10, 3, 4, 13, 14, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %320 = "llvm.add"(%315, %303) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %321 = "llvm.shufflevector"(%315, %320) <{mask = array<i32: 0, 9, 10, 3, 4, 13, 14, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %322 = "llvm.add"(%317, %11) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %323 = "llvm.add"(%319, %10) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %324 = "llvm.add"(%321, %10) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %325 = "llvm.ashr"(%322, %9) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %326 = "llvm.ashr"(%323, %9) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %327 = "llvm.ashr"(%324, %8) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %328 = "llvm.mul"(%327, %60) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %329 = "llvm.and"(%322, %6) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %330 = "llvm.shufflevector"(%328, %327) <{mask = array<i32: 4, 5, 6, 7, 8, 9, 10, 11>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %331 = "llvm.add"(%329, %5) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %332 = "llvm.add"(%331, %330) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %333 = "llvm.and"(%323, %6) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %334 = "llvm.add"(%325, %4) <{overflowFlags = #llvm.overflow<nsw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %335 = "llvm.add"(%334, %333) <{overflowFlags = #llvm.overflow<nsw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %336 = "llvm.and"(%324, %3) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %337 = "llvm.add"(%326, %4) <{overflowFlags = #llvm.overflow<nsw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %338 = "llvm.add"(%337, %336) <{overflowFlags = #llvm.overflow<nsw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %339 = "llvm.shufflevector"(%332, %23) <{mask = array<i32: 0, 2, 2, 0, 4, 6, 6, 4>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %340 = "llvm.shufflevector"(%335, %23) <{mask = array<i32: 0, 2, 2, 0, 4, 6, 6, 4>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %341 = "llvm.shufflevector"(%338, %23) <{mask = array<i32: 0, 2, 2, 0, 4, 6, 6, 4>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %342 = "llvm.shufflevector"(%332, %23) <{mask = array<i32: 3, 1, 3, 1, 7, 5, 7, 5>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %343 = "llvm.shufflevector"(%335, %23) <{mask = array<i32: 3, 1, 3, 1, 7, 5, 7, 5>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %344 = "llvm.shufflevector"(%338, %23) <{mask = array<i32: 3, 1, 3, 1, 7, 5, 7, 5>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    "llvm.intr.lifetime.start"(%100) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%101) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%102) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.call"(%100, %101, %102, %339, %340, %341, %342, %343, %344) <{CConv = #llvm.cconv<fastcc>, callee = @fd_r43x6_quad_mul_fast, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr, !llvm.ptr, vector<8xi64>, vector<8xi64>, vector<8xi64>, vector<8xi64>, vector<8xi64>, vector<8xi64>) -> ()
    %345 = "llvm.load"(%100) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %346 = "llvm.load"(%101) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %347 = "llvm.load"(%102) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    "llvm.intr.lifetime.end"(%102) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%101) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%100) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.br"(%345, %346, %347)[^bb3] : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> ()
  ^bb3(%348: vector<8xi64>, %349: vector<8xi64>, %350: vector<8xi64>):  // 2 preds: ^bb1, ^bb2
    %351 = "llvm.lshr"(%348, %9) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %352 = "llvm.lshr"(%349, %9) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %353 = "llvm.lshr"(%350, %8) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %354 = "llvm.mul"(%353, %60) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %355 = "llvm.and"(%348, %6) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %356 = "llvm.shufflevector"(%354, %353) <{mask = array<i32: 4, 5, 6, 7, 8, 9, 10, 11>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %357 = "llvm.add"(%356, %355) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    "llvm.store"(%357, %arg0) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (vector<8xi64>, !llvm.ptr) -> ()
    %358 = "llvm.and"(%349, %6) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %359 = "llvm.add"(%358, %351) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %360 = "llvm.getelementptr"(%arg0) <{elem_type = !llvm.struct<"struct.fd_curve25519_edwards", (vector<8xi64>, vector<8xi64>, vector<8xi64>)>, inbounds, rawConstantIndices = array<i32: 0, 1>}> : (!llvm.ptr) -> !llvm.ptr
    "llvm.store"(%359, %360) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (vector<8xi64>, !llvm.ptr) -> ()
    %361 = "llvm.and"(%350, %3) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %362 = "llvm.add"(%361, %352) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %363 = "llvm.getelementptr"(%arg0) <{elem_type = !llvm.struct<"struct.fd_curve25519_edwards", (vector<8xi64>, vector<8xi64>, vector<8xi64>)>, inbounds, rawConstantIndices = array<i32: 0, 2>}> : (!llvm.ptr) -> !llvm.ptr
    "llvm.store"(%362, %363) <{alignment = 64 : i64, ordering = 0 : i64}> : (vector<8xi64>, !llvm.ptr) -> ()
    "llvm.return"(%arg0) : (!llvm.ptr) -> ()
}
]

def fd_ed25519_point_add_with_opts :
    Cfg (Ctxt.ofList [SLLVM.Ty.bitvec 32, SLLVM.Ty.ptr, SLLVM.Ty.ptr, SLLVM.Ty.ptr])
      [SLLVM.Ty.ptr] :=
  [sllvm_cfg_of| fd_ed25519_point_add_with_opts_region with
    @fd_r43x6_quad_mul_fast := fd_r43x6_quad_mul_fast]

end Firedancer.Avx512
