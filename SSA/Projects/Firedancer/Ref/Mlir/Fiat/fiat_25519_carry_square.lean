/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.SLLVM.Cfg

namespace Firedancer.Ref
open LeanMLIR SLLVM

def fiat_25519_carry_square_region : MLIR.AST.Region 0 := [mlir_region|
{
  ^bb0(%arg0: !llvm.ptr, %arg1: !llvm.ptr):
    %0 = "llvm.mlir.constant"() <{value = 4 : i64}> : () -> i64
    %1 = "llvm.mlir.constant"() <{value = 19 : i64}> : () -> i64
    %2 = "llvm.mlir.constant"() <{value = 38 : i64}> : () -> i64
    %3 = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %4 = "llvm.mlir.constant"() <{value = 3 : i64}> : () -> i64
    %5 = "llvm.mlir.constant"() <{value = 2 : i64}> : () -> i64
    %6 = "llvm.mlir.constant"() <{value = 51 : i128}> : () -> i128
    %7 = "llvm.mlir.constant"() <{value = 2251799813685247 : i64}> : () -> i64
    %8 = "llvm.mlir.constant"() <{value = 18446744073709551615 : i128}> : () -> i128
    %9 = "llvm.mlir.constant"() <{value = 51 : i64}> : () -> i64
    %10 = "llvm.getelementptr"(%arg1, %0) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %11 = "llvm.load"(%10) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    %12 = "llvm.mul"(%11, %1) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %13 = "llvm.mul"(%11, %2) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %14 = "llvm.shl"(%11, %3) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %15 = "llvm.getelementptr"(%arg1, %4) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %16 = "llvm.load"(%15) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    %17 = "llvm.mul"(%16, %1) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %18 = "llvm.mul"(%16, %2) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %19 = "llvm.shl"(%16, %3) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %20 = "llvm.getelementptr"(%arg1, %5) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %21 = "llvm.load"(%20) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    %22 = "llvm.shl"(%21, %3) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %23 = "llvm.getelementptr"(%arg1, %3) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %24 = "llvm.load"(%23) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    %25 = "llvm.shl"(%24, %3) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %26 = "llvm.zext"(%11) : (i64) -> i128
    %27 = "llvm.zext"(%12) : (i64) -> i128
    %28 = "llvm.mul"(%27, %26) <{overflowFlags = #llvm.overflow<nuw>}> : (i128, i128) -> i128
    %29 = "llvm.zext"(%16) : (i64) -> i128
    %30 = "llvm.zext"(%13) : (i64) -> i128
    %31 = "llvm.mul"(%29, %30) <{overflowFlags = #llvm.overflow<nuw>}> : (i128, i128) -> i128
    %32 = "llvm.zext"(%17) : (i64) -> i128
    %33 = "llvm.mul"(%32, %29) <{overflowFlags = #llvm.overflow<nuw>}> : (i128, i128) -> i128
    %34 = "llvm.zext"(%21) : (i64) -> i128
    %35 = "llvm.mul"(%34, %30) <{overflowFlags = #llvm.overflow<nuw>}> : (i128, i128) -> i128
    %36 = "llvm.zext"(%18) : (i64) -> i128
    %37 = "llvm.mul"(%34, %36) <{overflowFlags = #llvm.overflow<nuw>}> : (i128, i128) -> i128
    %38 = "llvm.mul"(%34, %34) <{overflowFlags = #llvm.overflow<nuw>}> : (i128, i128) -> i128
    %39 = "llvm.zext"(%24) : (i64) -> i128
    %40 = "llvm.mul"(%39, %30) <{overflowFlags = #llvm.overflow<nuw>}> : (i128, i128) -> i128
    %41 = "llvm.zext"(%19) : (i64) -> i128
    %42 = "llvm.mul"(%39, %41) <{overflowFlags = #llvm.overflow<nuw>}> : (i128, i128) -> i128
    %43 = "llvm.zext"(%22) : (i64) -> i128
    %44 = "llvm.mul"(%39, %43) <{overflowFlags = #llvm.overflow<nuw>}> : (i128, i128) -> i128
    %45 = "llvm.mul"(%39, %39) <{overflowFlags = #llvm.overflow<nuw>}> : (i128, i128) -> i128
    %46 = "llvm.load"(%arg1) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    %47 = "llvm.zext"(%46) : (i64) -> i128
    %48 = "llvm.zext"(%14) : (i64) -> i128
    %49 = "llvm.mul"(%47, %48) <{overflowFlags = #llvm.overflow<nuw>}> : (i128, i128) -> i128
    %50 = "llvm.mul"(%47, %41) <{overflowFlags = #llvm.overflow<nuw>}> : (i128, i128) -> i128
    %51 = "llvm.mul"(%47, %43) <{overflowFlags = #llvm.overflow<nuw>}> : (i128, i128) -> i128
    %52 = "llvm.zext"(%25) : (i64) -> i128
    %53 = "llvm.mul"(%47, %52) <{overflowFlags = #llvm.overflow<nuw>}> : (i128, i128) -> i128
    %54 = "llvm.mul"(%47, %47) <{overflowFlags = #llvm.overflow<nuw>}> : (i128, i128) -> i128
    %55 = "llvm.add"(%40, %37) <{overflowFlags = #llvm.overflow<none>}> : (i128, i128) -> i128
    %56 = "llvm.add"(%55, %54) <{overflowFlags = #llvm.overflow<none>}> : (i128, i128) -> i128
    %57 = "llvm.lshr"(%56, %6) : (i128, i128) -> i128
    %58 = "llvm.trunc"(%56) : (i128) -> i64
    %59 = "llvm.and"(%58, %7) : (i64, i64) -> i64
    %60 = "llvm.add"(%42, %38) <{overflowFlags = #llvm.overflow<none>}> : (i128, i128) -> i128
    %61 = "llvm.add"(%60, %49) <{overflowFlags = #llvm.overflow<none>}> : (i128, i128) -> i128
    %62 = "llvm.add"(%44, %28) <{overflowFlags = #llvm.overflow<none>}> : (i128, i128) -> i128
    %63 = "llvm.add"(%62, %50) <{overflowFlags = #llvm.overflow<none>}> : (i128, i128) -> i128
    %64 = "llvm.add"(%45, %31) <{overflowFlags = #llvm.overflow<none>}> : (i128, i128) -> i128
    %65 = "llvm.add"(%64, %51) <{overflowFlags = #llvm.overflow<none>}> : (i128, i128) -> i128
    %66 = "llvm.add"(%35, %33) <{overflowFlags = #llvm.overflow<none>}> : (i128, i128) -> i128
    %67 = "llvm.add"(%66, %53) <{overflowFlags = #llvm.overflow<none>}> : (i128, i128) -> i128
    %68 = "llvm.and"(%57, %8) : (i128, i128) -> i128
    %69 = "llvm.add"(%67, %68) <{overflowFlags = #llvm.overflow<none>}> : (i128, i128) -> i128
    %70 = "llvm.lshr"(%69, %6) : (i128, i128) -> i128
    %71 = "llvm.trunc"(%69) : (i128) -> i64
    %72 = "llvm.and"(%71, %7) : (i64, i64) -> i64
    %73 = "llvm.and"(%70, %8) : (i128, i128) -> i128
    %74 = "llvm.add"(%65, %73) <{overflowFlags = #llvm.overflow<none>}> : (i128, i128) -> i128
    %75 = "llvm.lshr"(%74, %6) : (i128, i128) -> i128
    %76 = "llvm.trunc"(%74) : (i128) -> i64
    %77 = "llvm.and"(%76, %7) : (i64, i64) -> i64
    %78 = "llvm.and"(%75, %8) : (i128, i128) -> i128
    %79 = "llvm.add"(%63, %78) <{overflowFlags = #llvm.overflow<none>}> : (i128, i128) -> i128
    %80 = "llvm.lshr"(%79, %6) : (i128, i128) -> i128
    %81 = "llvm.trunc"(%79) : (i128) -> i64
    %82 = "llvm.and"(%81, %7) : (i64, i64) -> i64
    %83 = "llvm.and"(%80, %8) : (i128, i128) -> i128
    %84 = "llvm.add"(%61, %83) <{overflowFlags = #llvm.overflow<none>}> : (i128, i128) -> i128
    %85 = "llvm.lshr"(%84, %6) : (i128, i128) -> i128
    %86 = "llvm.trunc"(%85) : (i128) -> i64
    %87 = "llvm.trunc"(%84) : (i128) -> i64
    %88 = "llvm.and"(%87, %7) : (i64, i64) -> i64
    %89 = "llvm.mul"(%86, %1) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %90 = "llvm.add"(%89, %59) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %91 = "llvm.lshr"(%90, %9) : (i64, i64) -> i64
    %92 = "llvm.and"(%90, %7) : (i64, i64) -> i64
    %93 = "llvm.add"(%91, %72) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %94 = "llvm.lshr"(%93, %9) : (i64, i64) -> i64
    %95 = "llvm.and"(%93, %7) : (i64, i64) -> i64
    %96 = "llvm.add"(%94, %77) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    "llvm.store"(%92, %arg0) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (i64, !llvm.ptr) -> ()
    %97 = "llvm.getelementptr"(%arg0, %3) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%95, %97) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (i64, !llvm.ptr) -> ()
    %98 = "llvm.getelementptr"(%arg0, %5) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%96, %98) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (i64, !llvm.ptr) -> ()
    %99 = "llvm.getelementptr"(%arg0, %4) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%82, %99) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (i64, !llvm.ptr) -> ()
    %100 = "llvm.getelementptr"(%arg0, %0) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%88, %100) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (i64, !llvm.ptr) -> ()
    "llvm.return"() : () -> ()
}
]

def fiat_25519_carry_square : Cfg (Ctxt.ofList [SLLVM.Ty.ptr, SLLVM.Ty.ptr]) [] :=
  [sllvm_cfg_of| fiat_25519_carry_square_region]

end Firedancer.Ref
