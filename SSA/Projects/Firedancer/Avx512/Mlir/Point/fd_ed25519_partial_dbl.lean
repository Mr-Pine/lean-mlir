/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
-- build/native/gcc/mlir_canonicalized/avx512/region/fd_ed25519_partial_dbl.mlir
module

public import SSA.Projects.SLLVM.Cfg
public import SSA.Projects.Firedancer.Avx512.Mlir.Field.fd_r43x6_quad_sqr_fast
public import SSA.Projects.Firedancer.Avx512.Mlir.Field.fd_r43x6_quad_mul_fast
-- callee bindings are evaluated while elaborating
public meta import SSA.Projects.Firedancer.Avx512.Mlir.Field.fd_r43x6_quad_sqr_fast
public meta import SSA.Projects.Firedancer.Avx512.Mlir.Field.fd_r43x6_quad_mul_fast

@[expose] public section

namespace Firedancer.Avx512
open LeanMLIR SLLVM

def fd_ed25519_partial_dbl_region : MLIR.AST.Region 0 := [mlir_region|
{
  ^bb0(%arg0: !llvm.ptr, %arg1: !llvm.ptr):
    %0 = "llvm.mlir.constant"() <{value = dense<[8796093022207, 8796093022207, 8796093022207, 8796093022207, 1099511627775, 1099511627775, 1099511627775, 1099511627775]> : vector<8xi64>}> : () -> vector<8xi64>
    %1 = "llvm.mlir.constant"() <{value = dense<1048576> : vector<8xi64>}> : () -> vector<8xi64>
    %2 = "llvm.mlir.constant"() <{value = dense<[159383552, 159383552, 159383552, 159383552, 1048576, 1048576, 1048576, 1048576]> : vector<8xi64>}> : () -> vector<8xi64>
    %3 = "llvm.mlir.constant"() <{value = dense<8796093022207> : vector<8xi64>}> : () -> vector<8xi64>
    %4 = "llvm.mlir.constant"() <{value = 19 : i64}> : () -> i64
    %5 = "llvm.mlir.constant"() <{value = dense<[43, 43, 43, 43, 40, 40, 40, 40]> : vector<8xi64>}> : () -> vector<8xi64>
    %6 = "llvm.mlir.constant"() <{value = dense<43> : vector<8xi64>}> : () -> vector<8xi64>
    %7 = "llvm.mlir.constant"() <{value = dense<-1048576> : vector<8xi64>}> : () -> vector<8xi64>
    %8 = "llvm.mlir.constant"() <{value = dense<[-159383552, -159383552, -159383552, -159383552, -1048576, -1048576, -1048576, -1048576]> : vector<8xi64>}> : () -> vector<8xi64>
    %9 = "llvm.mlir.constant"() <{value = 1099511627775 : i64}> : () -> i64
    %10 = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
    %11 = "llvm.mlir.constant"() <{value = 6 : i32}> : () -> i32
    %12 = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
    %13 = "llvm.mlir.constant"() <{value = 4 : i32}> : () -> i32
    %14 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %15 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %16 = "llvm.mlir.constant"() <{value = 8796093022189 : i64}> : () -> i64
    %17 = "llvm.mlir.constant"() <{value = 8796093022207 : i64}> : () -> i64
    %18 = "llvm.mlir.constant"() <{value = dense<[0, 0, 1, 0, 0, 0, 1, 0]> : vector<8xi64>}> : () -> vector<8xi64>
    %19 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %20 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %21 = "llvm.mlir.poison"() : () -> vector<8xi64>
    %22 = "llvm.mlir.poison"() : () -> i64
    %23 = "llvm.mlir.undef"() : () -> vector<8xi64>
    %24 = "llvm.insertelement"(%23, %22, %15) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %25 = "llvm.insertelement"(%24, %16, %20) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %26 = "llvm.insertelement"(%25, %16, %19) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %27 = "llvm.insertelement"(%26, %22, %14) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %28 = "llvm.insertelement"(%27, %22, %13) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %29 = "llvm.insertelement"(%28, %17, %12) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %30 = "llvm.insertelement"(%29, %17, %11) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %31 = "llvm.insertelement"(%30, %22, %10) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %32 = "llvm.mlir.undef"() : () -> vector<8xi64>
    %33 = "llvm.insertelement"(%32, %22, %15) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %34 = "llvm.insertelement"(%33, %17, %20) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %35 = "llvm.insertelement"(%34, %17, %19) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %36 = "llvm.insertelement"(%35, %22, %14) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %37 = "llvm.insertelement"(%36, %22, %13) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %38 = "llvm.insertelement"(%37, %17, %12) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %39 = "llvm.insertelement"(%38, %17, %11) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %40 = "llvm.insertelement"(%39, %22, %10) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %41 = "llvm.mlir.undef"() : () -> vector<8xi64>
    %42 = "llvm.insertelement"(%41, %22, %15) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %43 = "llvm.insertelement"(%42, %17, %20) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %44 = "llvm.insertelement"(%43, %17, %19) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %45 = "llvm.insertelement"(%44, %22, %14) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %46 = "llvm.insertelement"(%45, %22, %13) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %47 = "llvm.insertelement"(%46, %9, %12) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %48 = "llvm.insertelement"(%47, %9, %11) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %49 = "llvm.insertelement"(%48, %22, %10) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %50 = "llvm.mlir.undef"() : () -> vector<8xi64>
    %51 = "llvm.insertelement"(%50, %16, %15) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %52 = "llvm.insertelement"(%51, %22, %20) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %53 = "llvm.insertelement"(%52, %22, %19) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %54 = "llvm.insertelement"(%53, %22, %14) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %55 = "llvm.insertelement"(%54, %17, %13) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %56 = "llvm.insertelement"(%55, %22, %12) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %57 = "llvm.insertelement"(%56, %22, %11) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %58 = "llvm.insertelement"(%57, %22, %10) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %59 = "llvm.mlir.undef"() : () -> vector<8xi64>
    %60 = "llvm.insertelement"(%59, %17, %15) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %61 = "llvm.insertelement"(%60, %22, %20) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %62 = "llvm.insertelement"(%61, %22, %19) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %63 = "llvm.insertelement"(%62, %22, %14) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %64 = "llvm.insertelement"(%63, %17, %13) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %65 = "llvm.insertelement"(%64, %22, %12) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %66 = "llvm.insertelement"(%65, %22, %11) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %67 = "llvm.insertelement"(%66, %22, %10) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %68 = "llvm.mlir.undef"() : () -> vector<8xi64>
    %69 = "llvm.insertelement"(%68, %17, %15) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %70 = "llvm.insertelement"(%69, %22, %20) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %71 = "llvm.insertelement"(%70, %22, %19) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %72 = "llvm.insertelement"(%71, %22, %14) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %73 = "llvm.insertelement"(%72, %9, %13) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %74 = "llvm.insertelement"(%73, %22, %12) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %75 = "llvm.insertelement"(%74, %22, %11) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %76 = "llvm.insertelement"(%75, %22, %10) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %77 = "llvm.mlir.undef"() : () -> vector<8xi64>
    %78 = "llvm.insertelement"(%77, %22, %15) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %79 = "llvm.insertelement"(%78, %22, %20) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %80 = "llvm.insertelement"(%79, %22, %19) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %81 = "llvm.insertelement"(%80, %22, %14) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %82 = "llvm.insertelement"(%81, %4, %13) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %83 = "llvm.insertelement"(%82, %4, %12) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %84 = "llvm.insertelement"(%83, %4, %11) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %85 = "llvm.insertelement"(%84, %4, %10) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %86 = "llvm.alloca"(%20) <{alignment = 64 : i64, elem_type = vector<8xi64>}> : (i32) -> !llvm.ptr
    %87 = "llvm.alloca"(%20) <{alignment = 64 : i64, elem_type = vector<8xi64>}> : (i32) -> !llvm.ptr
    %88 = "llvm.alloca"(%20) <{alignment = 64 : i64, elem_type = vector<8xi64>}> : (i32) -> !llvm.ptr
    %89 = "llvm.alloca"(%20) <{alignment = 64 : i64, elem_type = vector<8xi64>}> : (i32) -> !llvm.ptr
    %90 = "llvm.alloca"(%20) <{alignment = 64 : i64, elem_type = vector<8xi64>}> : (i32) -> !llvm.ptr
    %91 = "llvm.alloca"(%20) <{alignment = 64 : i64, elem_type = vector<8xi64>}> : (i32) -> !llvm.ptr
    %92 = "llvm.load"(%arg1) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %93 = "llvm.shufflevector"(%92, %21) <{mask = array<i32: 1, 1, 2, 0, 5, 5, 6, 4>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %94 = "llvm.getelementptr"(%arg1) <{elem_type = !llvm.struct<"struct.fd_curve25519_edwards", (vector<8xi64>, vector<8xi64>, vector<8xi64>)>, inbounds, rawConstantIndices = array<i32: 0, 1>}> : (!llvm.ptr) -> !llvm.ptr
    %95 = "llvm.load"(%94) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %96 = "llvm.shufflevector"(%95, %21) <{mask = array<i32: 1, 1, 2, 0, 5, 5, 6, 4>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %97 = "llvm.getelementptr"(%arg1) <{elem_type = !llvm.struct<"struct.fd_curve25519_edwards", (vector<8xi64>, vector<8xi64>, vector<8xi64>)>, inbounds, rawConstantIndices = array<i32: 0, 2>}> : (!llvm.ptr) -> !llvm.ptr
    %98 = "llvm.load"(%97) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %99 = "llvm.shufflevector"(%98, %21) <{mask = array<i32: 1, 1, 2, 0, 5, 5, 6, 4>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %100 = "llvm.add"(%93, %92) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %101 = "llvm.shufflevector"(%100, %93) <{mask = array<i32: 0, 9, 10, 11, 4, 13, 14, 15>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %102 = "llvm.add"(%96, %95) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %103 = "llvm.shufflevector"(%102, %96) <{mask = array<i32: 0, 9, 10, 11, 4, 13, 14, 15>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %104 = "llvm.add"(%99, %98) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %105 = "llvm.shufflevector"(%104, %99) <{mask = array<i32: 0, 9, 10, 11, 4, 13, 14, 15>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    "llvm.intr.lifetime.start"(%86) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%87) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%88) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.call"(%86, %87, %88, %101, %103, %105) <{CConv = #llvm.cconv<fastcc>, callee = @fd_r43x6_quad_sqr_fast, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr, !llvm.ptr, vector<8xi64>, vector<8xi64>, vector<8xi64>) -> ()
    %106 = "llvm.load"(%86) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %107 = "llvm.load"(%87) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %108 = "llvm.load"(%88) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    "llvm.intr.lifetime.end"(%88) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%87) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%86) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    %109 = "llvm.shl"(%106, %18) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %110 = "llvm.shl"(%107, %18) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %111 = "llvm.shl"(%108, %18) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %112 = "llvm.shufflevector"(%109, %21) <{mask = array<i32: 3, 3, 3, 3, 7, 7, 7, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %113 = "llvm.shufflevector"(%110, %21) <{mask = array<i32: 3, 3, 3, 3, 7, 7, 7, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %114 = "llvm.shufflevector"(%111, %21) <{mask = array<i32: 3, 3, 3, 3, 7, 7, 7, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %115 = "llvm.shufflevector"(%109, %21) <{mask = array<i32: 1, 1, 1, 1, 5, 5, 5, 5>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %116 = "llvm.shufflevector"(%110, %21) <{mask = array<i32: 1, 1, 1, 1, 5, 5, 5, 5>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %117 = "llvm.shufflevector"(%111, %21) <{mask = array<i32: 1, 1, 1, 1, 5, 5, 5, 5>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %118 = "llvm.add"(%112, %115) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %119 = "llvm.shufflevector"(%118, %112) <{mask = array<i32: 0, 9, 10, 3, 4, 13, 14, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %120 = "llvm.add"(%113, %116) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %121 = "llvm.shufflevector"(%120, %113) <{mask = array<i32: 0, 9, 10, 3, 4, 13, 14, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %122 = "llvm.add"(%114, %117) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %123 = "llvm.shufflevector"(%122, %114) <{mask = array<i32: 0, 9, 10, 3, 4, 13, 14, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %124 = "llvm.sub"(%119, %115) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %125 = "llvm.add"(%124, %31) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %126 = "llvm.shufflevector"(%119, %125) <{mask = array<i32: 0, 9, 10, 3, 4, 13, 14, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %127 = "llvm.sub"(%121, %116) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %128 = "llvm.add"(%127, %40) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %129 = "llvm.shufflevector"(%121, %128) <{mask = array<i32: 0, 9, 10, 3, 4, 13, 14, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %130 = "llvm.sub"(%123, %117) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %131 = "llvm.add"(%130, %49) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %132 = "llvm.shufflevector"(%123, %131) <{mask = array<i32: 0, 9, 10, 3, 4, 13, 14, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %133 = "llvm.add"(%126, %109) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %134 = "llvm.shufflevector"(%126, %133) <{mask = array<i32: 0, 1, 10, 3, 4, 5, 14, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %135 = "llvm.add"(%129, %110) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %136 = "llvm.shufflevector"(%129, %135) <{mask = array<i32: 0, 1, 10, 3, 4, 5, 14, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %137 = "llvm.add"(%132, %111) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %138 = "llvm.shufflevector"(%132, %137) <{mask = array<i32: 0, 1, 10, 3, 4, 5, 14, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %139 = "llvm.sub"(%134, %109) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %140 = "llvm.add"(%139, %58) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %141 = "llvm.shufflevector"(%140, %134) <{mask = array<i32: 0, 9, 10, 11, 4, 13, 14, 15>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %142 = "llvm.sub"(%136, %110) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %143 = "llvm.add"(%142, %67) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %144 = "llvm.shufflevector"(%143, %136) <{mask = array<i32: 0, 9, 10, 11, 4, 13, 14, 15>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %145 = "llvm.sub"(%138, %111) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %146 = "llvm.add"(%145, %76) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %147 = "llvm.shufflevector"(%146, %138) <{mask = array<i32: 0, 9, 10, 11, 4, 13, 14, 15>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %148 = "llvm.add"(%141, %8) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %149 = "llvm.add"(%144, %7) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %150 = "llvm.add"(%147, %7) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %151 = "llvm.ashr"(%148, %6) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %152 = "llvm.ashr"(%149, %6) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %153 = "llvm.ashr"(%150, %5) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %154 = "llvm.mul"(%153, %85) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %155 = "llvm.and"(%148, %3) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %156 = "llvm.shufflevector"(%154, %153) <{mask = array<i32: 4, 5, 6, 7, 8, 9, 10, 11>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %157 = "llvm.add"(%155, %2) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %158 = "llvm.add"(%157, %156) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %159 = "llvm.and"(%149, %3) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %160 = "llvm.add"(%151, %1) <{overflowFlags = #llvm.overflow<nsw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %161 = "llvm.add"(%160, %159) <{overflowFlags = #llvm.overflow<nsw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %162 = "llvm.and"(%150, %0) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %163 = "llvm.add"(%152, %1) <{overflowFlags = #llvm.overflow<nsw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %164 = "llvm.add"(%163, %162) <{overflowFlags = #llvm.overflow<nsw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %165 = "llvm.shufflevector"(%158, %21) <{mask = array<i32: 0, 1, 1, 0, 4, 5, 5, 4>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %166 = "llvm.shufflevector"(%161, %21) <{mask = array<i32: 0, 1, 1, 0, 4, 5, 5, 4>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %167 = "llvm.shufflevector"(%164, %21) <{mask = array<i32: 0, 1, 1, 0, 4, 5, 5, 4>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %168 = "llvm.shufflevector"(%158, %21) <{mask = array<i32: 2, 3, 2, 3, 6, 7, 6, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %169 = "llvm.shufflevector"(%161, %21) <{mask = array<i32: 2, 3, 2, 3, 6, 7, 6, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %170 = "llvm.shufflevector"(%164, %21) <{mask = array<i32: 2, 3, 2, 3, 6, 7, 6, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    "llvm.intr.lifetime.start"(%89) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%90) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%91) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.call"(%89, %90, %91, %165, %166, %167, %168, %169, %170) <{CConv = #llvm.cconv<fastcc>, callee = @fd_r43x6_quad_mul_fast, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr, !llvm.ptr, vector<8xi64>, vector<8xi64>, vector<8xi64>, vector<8xi64>, vector<8xi64>, vector<8xi64>) -> ()
    %171 = "llvm.load"(%89) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %172 = "llvm.load"(%90) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %173 = "llvm.load"(%91) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    "llvm.intr.lifetime.end"(%91) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%90) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%89) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    %174 = "llvm.lshr"(%171, %6) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %175 = "llvm.lshr"(%172, %6) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %176 = "llvm.lshr"(%173, %5) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %177 = "llvm.mul"(%176, %85) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %178 = "llvm.and"(%171, %3) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %179 = "llvm.shufflevector"(%177, %176) <{mask = array<i32: 4, 5, 6, 7, 8, 9, 10, 11>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %180 = "llvm.add"(%179, %178) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    "llvm.store"(%180, %arg0) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (vector<8xi64>, !llvm.ptr) -> ()
    %181 = "llvm.and"(%172, %3) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %182 = "llvm.add"(%181, %174) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %183 = "llvm.getelementptr"(%arg0) <{elem_type = !llvm.struct<"struct.fd_curve25519_edwards", (vector<8xi64>, vector<8xi64>, vector<8xi64>)>, inbounds, rawConstantIndices = array<i32: 0, 1>}> : (!llvm.ptr) -> !llvm.ptr
    "llvm.store"(%182, %183) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (vector<8xi64>, !llvm.ptr) -> ()
    %184 = "llvm.and"(%173, %0) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %185 = "llvm.add"(%184, %175) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %186 = "llvm.getelementptr"(%arg0) <{elem_type = !llvm.struct<"struct.fd_curve25519_edwards", (vector<8xi64>, vector<8xi64>, vector<8xi64>)>, inbounds, rawConstantIndices = array<i32: 0, 2>}> : (!llvm.ptr) -> !llvm.ptr
    "llvm.store"(%185, %186) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (vector<8xi64>, !llvm.ptr) -> ()
    "llvm.return"(%arg0) : (!llvm.ptr) -> ()
}
]

sllvm_cfg_def fd_ed25519_partial_dbl :
    Cfg (Ctxt.ofList [SLLVM.Ty.ptr, SLLVM.Ty.ptr])
      [SLLVM.Ty.ptr] :=
  [sllvm_cfg_of| fd_ed25519_partial_dbl_region with
    @fd_r43x6_quad_sqr_fast := fd_r43x6_quad_sqr_fast,
    @fd_r43x6_quad_mul_fast := fd_r43x6_quad_mul_fast]

end Firedancer.Avx512
