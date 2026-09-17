/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
-- build/native/gcc/mlir_canonicalized/ref/region/fiat_25519_to_bytes.mlir
module

public import SSA.Projects.SLLVM.Cfg
public import SSA.Projects.Firedancer.Ref.Mlir.Fiat.fiat_25519_addcarryx_u51
public import SSA.Projects.Firedancer.Ref.Mlir.Fiat.fiat_25519_subborrowx_u51
public import SSA.Projects.Firedancer.Ref.Mlir.Fiat.fiat_25519_cmovznz_u64
-- callee bindings are evaluated while elaborating
public meta import SSA.Projects.Firedancer.Ref.Mlir.Fiat.fiat_25519_addcarryx_u51
public meta import SSA.Projects.Firedancer.Ref.Mlir.Fiat.fiat_25519_subborrowx_u51
public meta import SSA.Projects.Firedancer.Ref.Mlir.Fiat.fiat_25519_cmovznz_u64

@[expose] public section

namespace Firedancer.Ref
open LeanMLIR SLLVM

set_option maxRecDepth 20000 in
def fiat_25519_to_bytes_region : MLIR.AST.Region 0 := [mlir_region|
{
  ^bb0(%arg0: !llvm.ptr, %arg1: !llvm.ptr):
    %0 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %1 = "llvm.mlir.constant"() <{value = 0 : i8}> : () -> i8
    %2 = "llvm.mlir.constant"() <{value = 2251799813685229 : i64}> : () -> i64
    %3 = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %4 = "llvm.mlir.constant"() <{value = 2251799813685247 : i64}> : () -> i64
    %5 = "llvm.mlir.constant"() <{value = 3 : i64}> : () -> i64
    %6 = "llvm.mlir.constant"() <{value = 4 : i64}> : () -> i64
    %7 = "llvm.mlir.constant"() <{value = 0 : i64}> : () -> i64
    %8 = "llvm.mlir.constant"() <{value = -1 : i64}> : () -> i64
    %9 = "llvm.mlir.constant"() <{value = 6 : i64}> : () -> i64
    %10 = "llvm.mlir.constant"() <{value = 8 : i64}> : () -> i64
    %11 = "llvm.mlir.constant"() <{value = 16 : i64}> : () -> i64
    %12 = "llvm.mlir.constant"() <{value = 24 : i64}> : () -> i64
    %13 = "llvm.mlir.constant"() <{value = 32 : i64}> : () -> i64
    %14 = "llvm.mlir.constant"() <{value = 40 : i64}> : () -> i64
    %15 = "llvm.mlir.constant"() <{value = 48 : i64}> : () -> i64
    %16 = "llvm.mlir.constant"() <{value = 255 : i64}> : () -> i64
    %17 = "llvm.mlir.constant"() <{value = 56 : i64}> : () -> i64
    %18 = "llvm.alloca"(%0) <{alignment = 8 : i64, elem_type = i64}> : (i32) -> !llvm.ptr
    %19 = "llvm.alloca"(%0) <{alignment = 1 : i64, elem_type = i8}> : (i32) -> !llvm.ptr
    %20 = "llvm.alloca"(%0) <{alignment = 8 : i64, elem_type = i64}> : (i32) -> !llvm.ptr
    %21 = "llvm.alloca"(%0) <{alignment = 1 : i64, elem_type = i8}> : (i32) -> !llvm.ptr
    %22 = "llvm.alloca"(%0) <{alignment = 8 : i64, elem_type = i64}> : (i32) -> !llvm.ptr
    %23 = "llvm.alloca"(%0) <{alignment = 1 : i64, elem_type = i8}> : (i32) -> !llvm.ptr
    %24 = "llvm.alloca"(%0) <{alignment = 8 : i64, elem_type = i64}> : (i32) -> !llvm.ptr
    %25 = "llvm.alloca"(%0) <{alignment = 1 : i64, elem_type = i8}> : (i32) -> !llvm.ptr
    %26 = "llvm.alloca"(%0) <{alignment = 8 : i64, elem_type = i64}> : (i32) -> !llvm.ptr
    %27 = "llvm.alloca"(%0) <{alignment = 1 : i64, elem_type = i8}> : (i32) -> !llvm.ptr
    %28 = "llvm.alloca"(%0) <{alignment = 8 : i64, elem_type = i64}> : (i32) -> !llvm.ptr
    %29 = "llvm.alloca"(%0) <{alignment = 8 : i64, elem_type = i64}> : (i32) -> !llvm.ptr
    %30 = "llvm.alloca"(%0) <{alignment = 1 : i64, elem_type = i8}> : (i32) -> !llvm.ptr
    %31 = "llvm.alloca"(%0) <{alignment = 8 : i64, elem_type = i64}> : (i32) -> !llvm.ptr
    %32 = "llvm.alloca"(%0) <{alignment = 1 : i64, elem_type = i8}> : (i32) -> !llvm.ptr
    %33 = "llvm.alloca"(%0) <{alignment = 8 : i64, elem_type = i64}> : (i32) -> !llvm.ptr
    %34 = "llvm.alloca"(%0) <{alignment = 1 : i64, elem_type = i8}> : (i32) -> !llvm.ptr
    %35 = "llvm.alloca"(%0) <{alignment = 8 : i64, elem_type = i64}> : (i32) -> !llvm.ptr
    %36 = "llvm.alloca"(%0) <{alignment = 1 : i64, elem_type = i8}> : (i32) -> !llvm.ptr
    %37 = "llvm.alloca"(%0) <{alignment = 8 : i64, elem_type = i64}> : (i32) -> !llvm.ptr
    %38 = "llvm.alloca"(%0) <{alignment = 1 : i64, elem_type = i8}> : (i32) -> !llvm.ptr
    "llvm.intr.lifetime.start"(%18) <{size = 8 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%19) <{size = 1 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%20) <{size = 8 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%21) <{size = 1 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%22) <{size = 8 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%23) <{size = 1 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%24) <{size = 8 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%25) <{size = 1 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%26) <{size = 8 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%27) <{size = 1 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%28) <{size = 8 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%29) <{size = 8 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%30) <{size = 1 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%31) <{size = 8 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%32) <{size = 1 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%33) <{size = 8 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%34) <{size = 1 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%35) <{size = 8 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%36) <{size = 1 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%37) <{size = 8 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%38) <{size = 1 : i64}> : (!llvm.ptr) -> ()
    %39 = "llvm.load"(%arg1) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    "llvm.call"(%18, %19, %1, %39, %2) <{CConv = #llvm.cconv<fastcc>, callee = @fiat_25519_subborrowx_u51, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr, i8, i64, i64) -> ()
    %40 = "llvm.load"(%19) <{alignment = 1 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> i8
    %41 = "llvm.getelementptr"(%arg1) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: 1>}> : (!llvm.ptr) -> !llvm.ptr
    %42 = "llvm.load"(%41) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    "llvm.call"(%20, %21, %40, %42, %4) <{CConv = #llvm.cconv<fastcc>, callee = @fiat_25519_subborrowx_u51, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr, i8, i64, i64) -> ()
    %43 = "llvm.load"(%21) <{alignment = 1 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> i8
    %44 = "llvm.getelementptr"(%arg1) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: 2>}> : (!llvm.ptr) -> !llvm.ptr
    %45 = "llvm.load"(%44) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    "llvm.call"(%22, %23, %43, %45, %4) <{CConv = #llvm.cconv<fastcc>, callee = @fiat_25519_subborrowx_u51, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr, i8, i64, i64) -> ()
    %46 = "llvm.load"(%23) <{alignment = 1 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> i8
    %47 = "llvm.getelementptr"(%arg1) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: 3>}> : (!llvm.ptr) -> !llvm.ptr
    %48 = "llvm.load"(%47) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    "llvm.call"(%24, %25, %46, %48, %4) <{CConv = #llvm.cconv<fastcc>, callee = @fiat_25519_subborrowx_u51, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr, i8, i64, i64) -> ()
    %49 = "llvm.load"(%25) <{alignment = 1 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> i8
    %50 = "llvm.getelementptr"(%arg1) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: 4>}> : (!llvm.ptr) -> !llvm.ptr
    %51 = "llvm.load"(%50) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    "llvm.call"(%26, %27, %49, %51, %4) <{CConv = #llvm.cconv<fastcc>, callee = @fiat_25519_subborrowx_u51, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr, i8, i64, i64) -> ()
    %52 = "llvm.load"(%27) <{alignment = 1 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> i8
    "llvm.call"(%28, %52, %7, %8) <{CConv = #llvm.cconv<fastcc>, callee = @fiat_25519_cmovznz_u64, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, i8, i64, i64) -> ()
    %53 = "llvm.load"(%18) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    %54 = "llvm.load"(%28) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    %55 = "llvm.and"(%54, %2) : (i64, i64) -> i64
    "llvm.call"(%29, %30, %1, %53, %55) <{CConv = #llvm.cconv<fastcc>, callee = @fiat_25519_addcarryx_u51, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr, i8, i64, i64) -> ()
    %56 = "llvm.load"(%30) <{alignment = 1 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> i8
    %57 = "llvm.load"(%20) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    %58 = "llvm.and"(%54, %4) : (i64, i64) -> i64
    "llvm.call"(%31, %32, %56, %57, %58) <{CConv = #llvm.cconv<fastcc>, callee = @fiat_25519_addcarryx_u51, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr, i8, i64, i64) -> ()
    %59 = "llvm.load"(%32) <{alignment = 1 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> i8
    %60 = "llvm.load"(%22) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    "llvm.call"(%33, %34, %59, %60, %58) <{CConv = #llvm.cconv<fastcc>, callee = @fiat_25519_addcarryx_u51, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr, i8, i64, i64) -> ()
    %61 = "llvm.load"(%34) <{alignment = 1 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> i8
    %62 = "llvm.load"(%24) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    "llvm.call"(%35, %36, %61, %62, %58) <{CConv = #llvm.cconv<fastcc>, callee = @fiat_25519_addcarryx_u51, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr, i8, i64, i64) -> ()
    %63 = "llvm.load"(%36) <{alignment = 1 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> i8
    %64 = "llvm.load"(%26) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    "llvm.call"(%37, %38, %63, %64, %58) <{CConv = #llvm.cconv<fastcc>, callee = @fiat_25519_addcarryx_u51, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr, i8, i64, i64) -> ()
    %65 = "llvm.load"(%37) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    %66 = "llvm.shl"(%65, %6) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %67 = "llvm.load"(%35) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    %68 = "llvm.shl"(%67, %3) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %69 = "llvm.load"(%33) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    %70 = "llvm.shl"(%69, %9) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %71 = "llvm.load"(%31) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    %72 = "llvm.shl"(%71, %5) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %73 = "llvm.load"(%29) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    %74 = "llvm.trunc"(%73) : (i64) -> i8
    %75 = "llvm.lshr"(%73, %10) : (i64, i64) -> i64
    %76 = "llvm.trunc"(%75) : (i64) -> i8
    %77 = "llvm.lshr"(%73, %11) : (i64, i64) -> i64
    %78 = "llvm.trunc"(%77) : (i64) -> i8
    %79 = "llvm.lshr"(%73, %12) : (i64, i64) -> i64
    %80 = "llvm.trunc"(%79) : (i64) -> i8
    %81 = "llvm.lshr"(%73, %13) : (i64, i64) -> i64
    %82 = "llvm.trunc"(%81) : (i64) -> i8
    %83 = "llvm.lshr"(%73, %14) : (i64, i64) -> i64
    %84 = "llvm.trunc"(%83) : (i64) -> i8
    %85 = "llvm.lshr"(%73, %15) : (i64, i64) -> i64
    %86 = "llvm.and"(%85, %16) : (i64, i64) -> i64
    %87 = "llvm.add"(%86, %72) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %88 = "llvm.trunc"(%87) : (i64) -> i8
    %89 = "llvm.lshr"(%87, %10) : (i64, i64) -> i64
    %90 = "llvm.trunc"(%89) : (i64) -> i8
    %91 = "llvm.lshr"(%87, %11) : (i64, i64) -> i64
    %92 = "llvm.trunc"(%91) : (i64) -> i8
    %93 = "llvm.lshr"(%87, %12) : (i64, i64) -> i64
    %94 = "llvm.trunc"(%93) : (i64) -> i8
    %95 = "llvm.lshr"(%87, %13) : (i64, i64) -> i64
    %96 = "llvm.trunc"(%95) : (i64) -> i8
    %97 = "llvm.lshr"(%87, %14) : (i64, i64) -> i64
    %98 = "llvm.trunc"(%97) : (i64) -> i8
    %99 = "llvm.lshr"(%87, %15) : (i64, i64) -> i64
    %100 = "llvm.and"(%99, %16) : (i64, i64) -> i64
    %101 = "llvm.add"(%100, %70) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %102 = "llvm.trunc"(%101) : (i64) -> i8
    %103 = "llvm.lshr"(%101, %10) : (i64, i64) -> i64
    %104 = "llvm.trunc"(%103) : (i64) -> i8
    %105 = "llvm.lshr"(%101, %11) : (i64, i64) -> i64
    %106 = "llvm.trunc"(%105) : (i64) -> i8
    %107 = "llvm.lshr"(%101, %12) : (i64, i64) -> i64
    %108 = "llvm.trunc"(%107) : (i64) -> i8
    %109 = "llvm.lshr"(%101, %13) : (i64, i64) -> i64
    %110 = "llvm.trunc"(%109) : (i64) -> i8
    %111 = "llvm.lshr"(%101, %14) : (i64, i64) -> i64
    %112 = "llvm.trunc"(%111) : (i64) -> i8
    %113 = "llvm.lshr"(%101, %15) : (i64, i64) -> i64
    %114 = "llvm.trunc"(%113) : (i64) -> i8
    %115 = "llvm.lshr"(%101, %17) : (i64, i64) -> i64
    %116 = "llvm.add"(%115, %68) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %117 = "llvm.trunc"(%116) : (i64) -> i8
    %118 = "llvm.lshr"(%116, %10) : (i64, i64) -> i64
    %119 = "llvm.trunc"(%118) : (i64) -> i8
    %120 = "llvm.lshr"(%116, %11) : (i64, i64) -> i64
    %121 = "llvm.trunc"(%120) : (i64) -> i8
    %122 = "llvm.lshr"(%116, %12) : (i64, i64) -> i64
    %123 = "llvm.trunc"(%122) : (i64) -> i8
    %124 = "llvm.lshr"(%116, %13) : (i64, i64) -> i64
    %125 = "llvm.trunc"(%124) : (i64) -> i8
    %126 = "llvm.lshr"(%116, %14) : (i64, i64) -> i64
    %127 = "llvm.trunc"(%126) : (i64) -> i8
    %128 = "llvm.lshr"(%116, %15) : (i64, i64) -> i64
    %129 = "llvm.and"(%128, %16) : (i64, i64) -> i64
    %130 = "llvm.add"(%129, %66) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %131 = "llvm.trunc"(%130) : (i64) -> i8
    %132 = "llvm.lshr"(%130, %10) : (i64, i64) -> i64
    %133 = "llvm.trunc"(%132) : (i64) -> i8
    %134 = "llvm.lshr"(%130, %11) : (i64, i64) -> i64
    %135 = "llvm.trunc"(%134) : (i64) -> i8
    %136 = "llvm.lshr"(%130, %12) : (i64, i64) -> i64
    %137 = "llvm.trunc"(%136) : (i64) -> i8
    %138 = "llvm.lshr"(%130, %13) : (i64, i64) -> i64
    %139 = "llvm.trunc"(%138) : (i64) -> i8
    %140 = "llvm.lshr"(%130, %14) : (i64, i64) -> i64
    %141 = "llvm.trunc"(%140) : (i64) -> i8
    %142 = "llvm.lshr"(%130, %15) : (i64, i64) -> i64
    %143 = "llvm.trunc"(%142) : (i64) -> i8
    "llvm.store"(%74, %arg0) <{alignment = 1 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (i8, !llvm.ptr) -> ()
    %144 = "llvm.getelementptr"(%arg0) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: 1>}> : (!llvm.ptr) -> !llvm.ptr
    "llvm.store"(%76, %144) <{alignment = 1 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (i8, !llvm.ptr) -> ()
    %145 = "llvm.getelementptr"(%arg0) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: 2>}> : (!llvm.ptr) -> !llvm.ptr
    "llvm.store"(%78, %145) <{alignment = 1 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (i8, !llvm.ptr) -> ()
    %146 = "llvm.getelementptr"(%arg0) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: 3>}> : (!llvm.ptr) -> !llvm.ptr
    "llvm.store"(%80, %146) <{alignment = 1 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (i8, !llvm.ptr) -> ()
    %147 = "llvm.getelementptr"(%arg0) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: 4>}> : (!llvm.ptr) -> !llvm.ptr
    "llvm.store"(%82, %147) <{alignment = 1 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (i8, !llvm.ptr) -> ()
    %148 = "llvm.getelementptr"(%arg0) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: 5>}> : (!llvm.ptr) -> !llvm.ptr
    "llvm.store"(%84, %148) <{alignment = 1 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (i8, !llvm.ptr) -> ()
    %149 = "llvm.getelementptr"(%arg0) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: 6>}> : (!llvm.ptr) -> !llvm.ptr
    "llvm.store"(%88, %149) <{alignment = 1 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (i8, !llvm.ptr) -> ()
    %150 = "llvm.getelementptr"(%arg0) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: 7>}> : (!llvm.ptr) -> !llvm.ptr
    "llvm.store"(%90, %150) <{alignment = 1 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (i8, !llvm.ptr) -> ()
    %151 = "llvm.getelementptr"(%arg0) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: 8>}> : (!llvm.ptr) -> !llvm.ptr
    "llvm.store"(%92, %151) <{alignment = 1 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (i8, !llvm.ptr) -> ()
    %152 = "llvm.getelementptr"(%arg0) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: 9>}> : (!llvm.ptr) -> !llvm.ptr
    "llvm.store"(%94, %152) <{alignment = 1 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (i8, !llvm.ptr) -> ()
    %153 = "llvm.getelementptr"(%arg0) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: 10>}> : (!llvm.ptr) -> !llvm.ptr
    "llvm.store"(%96, %153) <{alignment = 1 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (i8, !llvm.ptr) -> ()
    %154 = "llvm.getelementptr"(%arg0) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: 11>}> : (!llvm.ptr) -> !llvm.ptr
    "llvm.store"(%98, %154) <{alignment = 1 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (i8, !llvm.ptr) -> ()
    %155 = "llvm.getelementptr"(%arg0) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: 12>}> : (!llvm.ptr) -> !llvm.ptr
    "llvm.store"(%102, %155) <{alignment = 1 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (i8, !llvm.ptr) -> ()
    %156 = "llvm.getelementptr"(%arg0) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: 13>}> : (!llvm.ptr) -> !llvm.ptr
    "llvm.store"(%104, %156) <{alignment = 1 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (i8, !llvm.ptr) -> ()
    %157 = "llvm.getelementptr"(%arg0) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: 14>}> : (!llvm.ptr) -> !llvm.ptr
    "llvm.store"(%106, %157) <{alignment = 1 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (i8, !llvm.ptr) -> ()
    %158 = "llvm.getelementptr"(%arg0) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: 15>}> : (!llvm.ptr) -> !llvm.ptr
    "llvm.store"(%108, %158) <{alignment = 1 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (i8, !llvm.ptr) -> ()
    %159 = "llvm.getelementptr"(%arg0) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: 16>}> : (!llvm.ptr) -> !llvm.ptr
    "llvm.store"(%110, %159) <{alignment = 1 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (i8, !llvm.ptr) -> ()
    %160 = "llvm.getelementptr"(%arg0) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: 17>}> : (!llvm.ptr) -> !llvm.ptr
    "llvm.store"(%112, %160) <{alignment = 1 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (i8, !llvm.ptr) -> ()
    %161 = "llvm.getelementptr"(%arg0) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: 18>}> : (!llvm.ptr) -> !llvm.ptr
    "llvm.store"(%114, %161) <{alignment = 1 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (i8, !llvm.ptr) -> ()
    %162 = "llvm.getelementptr"(%arg0) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: 19>}> : (!llvm.ptr) -> !llvm.ptr
    "llvm.store"(%117, %162) <{alignment = 1 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (i8, !llvm.ptr) -> ()
    %163 = "llvm.getelementptr"(%arg0) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: 20>}> : (!llvm.ptr) -> !llvm.ptr
    "llvm.store"(%119, %163) <{alignment = 1 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (i8, !llvm.ptr) -> ()
    %164 = "llvm.getelementptr"(%arg0) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: 21>}> : (!llvm.ptr) -> !llvm.ptr
    "llvm.store"(%121, %164) <{alignment = 1 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (i8, !llvm.ptr) -> ()
    %165 = "llvm.getelementptr"(%arg0) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: 22>}> : (!llvm.ptr) -> !llvm.ptr
    "llvm.store"(%123, %165) <{alignment = 1 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (i8, !llvm.ptr) -> ()
    %166 = "llvm.getelementptr"(%arg0) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: 23>}> : (!llvm.ptr) -> !llvm.ptr
    "llvm.store"(%125, %166) <{alignment = 1 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (i8, !llvm.ptr) -> ()
    %167 = "llvm.getelementptr"(%arg0) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: 24>}> : (!llvm.ptr) -> !llvm.ptr
    "llvm.store"(%127, %167) <{alignment = 1 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (i8, !llvm.ptr) -> ()
    %168 = "llvm.getelementptr"(%arg0) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: 25>}> : (!llvm.ptr) -> !llvm.ptr
    "llvm.store"(%131, %168) <{alignment = 1 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (i8, !llvm.ptr) -> ()
    %169 = "llvm.getelementptr"(%arg0) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: 26>}> : (!llvm.ptr) -> !llvm.ptr
    "llvm.store"(%133, %169) <{alignment = 1 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (i8, !llvm.ptr) -> ()
    %170 = "llvm.getelementptr"(%arg0) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: 27>}> : (!llvm.ptr) -> !llvm.ptr
    "llvm.store"(%135, %170) <{alignment = 1 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (i8, !llvm.ptr) -> ()
    %171 = "llvm.getelementptr"(%arg0) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: 28>}> : (!llvm.ptr) -> !llvm.ptr
    "llvm.store"(%137, %171) <{alignment = 1 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (i8, !llvm.ptr) -> ()
    %172 = "llvm.getelementptr"(%arg0) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: 29>}> : (!llvm.ptr) -> !llvm.ptr
    "llvm.store"(%139, %172) <{alignment = 1 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (i8, !llvm.ptr) -> ()
    %173 = "llvm.getelementptr"(%arg0) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: 30>}> : (!llvm.ptr) -> !llvm.ptr
    "llvm.store"(%141, %173) <{alignment = 1 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (i8, !llvm.ptr) -> ()
    %174 = "llvm.getelementptr"(%arg0) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: 31>}> : (!llvm.ptr) -> !llvm.ptr
    "llvm.store"(%143, %174) <{alignment = 1 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (i8, !llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%38) <{size = 1 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%37) <{size = 8 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%36) <{size = 1 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%35) <{size = 8 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%34) <{size = 1 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%33) <{size = 8 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%32) <{size = 1 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%31) <{size = 8 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%30) <{size = 1 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%29) <{size = 8 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%28) <{size = 8 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%27) <{size = 1 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%26) <{size = 8 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%25) <{size = 1 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%24) <{size = 8 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%23) <{size = 1 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%22) <{size = 8 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%21) <{size = 1 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%20) <{size = 8 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%19) <{size = 1 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%18) <{size = 8 : i64}> : (!llvm.ptr) -> ()
    "llvm.return"() : () -> ()
}
]

set_option maxRecDepth 20000 in
sllvm_cfg_def fiat_25519_to_bytes : Cfg (Ctxt.ofList [SLLVM.Ty.ptr, SLLVM.Ty.ptr]) [] :=
  [sllvm_cfg_of| fiat_25519_to_bytes_region with
    @fiat_25519_addcarryx_u51 := fiat_25519_addcarryx_u51,
    @fiat_25519_subborrowx_u51 := fiat_25519_subborrowx_u51,
    @fiat_25519_cmovznz_u64 := fiat_25519_cmovznz_u64]

end Firedancer.Ref
