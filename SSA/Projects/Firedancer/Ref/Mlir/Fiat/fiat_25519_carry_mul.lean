/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
-- build/native/gcc/mlir_canonicalized/ref/region/fiat_25519_carry_mul.mlir
import SSA.Projects.SLLVM.Cfg

namespace Firedancer.Ref
open LeanMLIR SLLVM

def fiat_25519_carry_mul_region : MLIR.AST.Region 0 := [mlir_region|
{
  ^bb0(%arg0: !llvm.ptr, %arg1: !llvm.ptr, %arg2: !llvm.ptr):
    %0 = "llvm.mlir.constant"() <{value = 19 : i64}> : () -> i64
    %1 = "llvm.mlir.constant"() <{value = 51 : i128}> : () -> i128
    %2 = "llvm.mlir.constant"() <{value = 2251799813685247 : i64}> : () -> i64
    %3 = "llvm.mlir.constant"() <{value = 18446744073709551615 : i128}> : () -> i128
    %4 = "llvm.mlir.constant"() <{value = 51 : i64}> : () -> i64
    %5 = "llvm.getelementptr"(%arg1) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: 4>}> : (!llvm.ptr) -> !llvm.ptr
    %6 = "llvm.load"(%5) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    %7 = "llvm.zext"(%6) : (i64) -> i128
    %8 = "llvm.getelementptr"(%arg2) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: 4>}> : (!llvm.ptr) -> !llvm.ptr
    %9 = "llvm.load"(%8) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    %10 = "llvm.mul"(%9, %0) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %11 = "llvm.zext"(%10) : (i64) -> i128
    %12 = "llvm.mul"(%11, %7) <{overflowFlags = #llvm.overflow<nuw>}> : (i128, i128) -> i128
    %13 = "llvm.getelementptr"(%arg2) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: 3>}> : (!llvm.ptr) -> !llvm.ptr
    %14 = "llvm.load"(%13) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    %15 = "llvm.mul"(%14, %0) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %16 = "llvm.zext"(%15) : (i64) -> i128
    %17 = "llvm.mul"(%16, %7) <{overflowFlags = #llvm.overflow<nuw>}> : (i128, i128) -> i128
    %18 = "llvm.getelementptr"(%arg2) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: 2>}> : (!llvm.ptr) -> !llvm.ptr
    %19 = "llvm.load"(%18) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    %20 = "llvm.mul"(%19, %0) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %21 = "llvm.zext"(%20) : (i64) -> i128
    %22 = "llvm.mul"(%21, %7) <{overflowFlags = #llvm.overflow<nuw>}> : (i128, i128) -> i128
    %23 = "llvm.getelementptr"(%arg2) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: 1>}> : (!llvm.ptr) -> !llvm.ptr
    %24 = "llvm.load"(%23) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    %25 = "llvm.mul"(%24, %0) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %26 = "llvm.zext"(%25) : (i64) -> i128
    %27 = "llvm.mul"(%26, %7) <{overflowFlags = #llvm.overflow<nuw>}> : (i128, i128) -> i128
    %28 = "llvm.getelementptr"(%arg1) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: 3>}> : (!llvm.ptr) -> !llvm.ptr
    %29 = "llvm.load"(%28) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    %30 = "llvm.zext"(%29) : (i64) -> i128
    %31 = "llvm.mul"(%30, %11) <{overflowFlags = #llvm.overflow<nuw>}> : (i128, i128) -> i128
    %32 = "llvm.mul"(%30, %16) <{overflowFlags = #llvm.overflow<nuw>}> : (i128, i128) -> i128
    %33 = "llvm.mul"(%30, %21) <{overflowFlags = #llvm.overflow<nuw>}> : (i128, i128) -> i128
    %34 = "llvm.getelementptr"(%arg1) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: 2>}> : (!llvm.ptr) -> !llvm.ptr
    %35 = "llvm.load"(%34) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    %36 = "llvm.zext"(%35) : (i64) -> i128
    %37 = "llvm.mul"(%36, %11) <{overflowFlags = #llvm.overflow<nuw>}> : (i128, i128) -> i128
    %38 = "llvm.mul"(%36, %16) <{overflowFlags = #llvm.overflow<nuw>}> : (i128, i128) -> i128
    %39 = "llvm.getelementptr"(%arg1) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: 1>}> : (!llvm.ptr) -> !llvm.ptr
    %40 = "llvm.load"(%39) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    %41 = "llvm.zext"(%40) : (i64) -> i128
    %42 = "llvm.mul"(%41, %11) <{overflowFlags = #llvm.overflow<nuw>}> : (i128, i128) -> i128
    %43 = "llvm.load"(%arg2) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    %44 = "llvm.zext"(%43) : (i64) -> i128
    %45 = "llvm.mul"(%44, %7) <{overflowFlags = #llvm.overflow<nuw>}> : (i128, i128) -> i128
    %46 = "llvm.zext"(%24) : (i64) -> i128
    %47 = "llvm.mul"(%30, %46) <{overflowFlags = #llvm.overflow<nuw>}> : (i128, i128) -> i128
    %48 = "llvm.mul"(%44, %30) <{overflowFlags = #llvm.overflow<nuw>}> : (i128, i128) -> i128
    %49 = "llvm.zext"(%19) : (i64) -> i128
    %50 = "llvm.mul"(%36, %49) <{overflowFlags = #llvm.overflow<nuw>}> : (i128, i128) -> i128
    %51 = "llvm.mul"(%36, %46) <{overflowFlags = #llvm.overflow<nuw>}> : (i128, i128) -> i128
    %52 = "llvm.mul"(%44, %36) <{overflowFlags = #llvm.overflow<nuw>}> : (i128, i128) -> i128
    %53 = "llvm.zext"(%14) : (i64) -> i128
    %54 = "llvm.mul"(%41, %53) <{overflowFlags = #llvm.overflow<nuw>}> : (i128, i128) -> i128
    %55 = "llvm.mul"(%41, %49) <{overflowFlags = #llvm.overflow<nuw>}> : (i128, i128) -> i128
    %56 = "llvm.mul"(%41, %46) <{overflowFlags = #llvm.overflow<nuw>}> : (i128, i128) -> i128
    %57 = "llvm.mul"(%44, %41) <{overflowFlags = #llvm.overflow<nuw>}> : (i128, i128) -> i128
    %58 = "llvm.load"(%arg1) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    %59 = "llvm.zext"(%58) : (i64) -> i128
    %60 = "llvm.zext"(%9) : (i64) -> i128
    %61 = "llvm.mul"(%59, %60) <{overflowFlags = #llvm.overflow<nuw>}> : (i128, i128) -> i128
    %62 = "llvm.mul"(%59, %53) <{overflowFlags = #llvm.overflow<nuw>}> : (i128, i128) -> i128
    %63 = "llvm.mul"(%59, %49) <{overflowFlags = #llvm.overflow<nuw>}> : (i128, i128) -> i128
    %64 = "llvm.mul"(%59, %46) <{overflowFlags = #llvm.overflow<nuw>}> : (i128, i128) -> i128
    %65 = "llvm.mul"(%59, %44) <{overflowFlags = #llvm.overflow<nuw>}> : (i128, i128) -> i128
    %66 = "llvm.add"(%33, %27) <{overflowFlags = #llvm.overflow<none>}> : (i128, i128) -> i128
    %67 = "llvm.add"(%66, %38) <{overflowFlags = #llvm.overflow<none>}> : (i128, i128) -> i128
    %68 = "llvm.add"(%67, %42) <{overflowFlags = #llvm.overflow<none>}> : (i128, i128) -> i128
    %69 = "llvm.add"(%68, %65) <{overflowFlags = #llvm.overflow<none>}> : (i128, i128) -> i128
    %70 = "llvm.lshr"(%69, %1) : (i128, i128) -> i128
    %71 = "llvm.trunc"(%69) : (i128) -> i64
    %72 = "llvm.and"(%71, %2) : (i64, i64) -> i64
    %73 = "llvm.add"(%31, %17) <{overflowFlags = #llvm.overflow<none>}> : (i128, i128) -> i128
    %74 = "llvm.add"(%32, %22) <{overflowFlags = #llvm.overflow<none>}> : (i128, i128) -> i128
    %75 = "llvm.add"(%74, %37) <{overflowFlags = #llvm.overflow<none>}> : (i128, i128) -> i128
    %76 = "llvm.add"(%75, %57) <{overflowFlags = #llvm.overflow<none>}> : (i128, i128) -> i128
    %77 = "llvm.add"(%76, %64) <{overflowFlags = #llvm.overflow<none>}> : (i128, i128) -> i128
    %78 = "llvm.and"(%70, %3) : (i128, i128) -> i128
    %79 = "llvm.add"(%77, %78) <{overflowFlags = #llvm.overflow<none>}> : (i128, i128) -> i128
    %80 = "llvm.lshr"(%79, %1) : (i128, i128) -> i128
    %81 = "llvm.trunc"(%79) : (i128) -> i64
    %82 = "llvm.and"(%81, %2) : (i64, i64) -> i64
    %83 = "llvm.and"(%80, %3) : (i128, i128) -> i128
    %84 = "llvm.add"(%73, %56) <{overflowFlags = #llvm.overflow<none>}> : (i128, i128) -> i128
    %85 = "llvm.add"(%84, %52) <{overflowFlags = #llvm.overflow<none>}> : (i128, i128) -> i128
    %86 = "llvm.add"(%85, %63) <{overflowFlags = #llvm.overflow<none>}> : (i128, i128) -> i128
    %87 = "llvm.add"(%86, %83) <{overflowFlags = #llvm.overflow<none>}> : (i128, i128) -> i128
    %88 = "llvm.lshr"(%87, %1) : (i128, i128) -> i128
    %89 = "llvm.trunc"(%87) : (i128) -> i64
    %90 = "llvm.and"(%89, %2) : (i64, i64) -> i64
    %91 = "llvm.and"(%88, %3) : (i128, i128) -> i128
    %92 = "llvm.add"(%51, %12) <{overflowFlags = #llvm.overflow<none>}> : (i128, i128) -> i128
    %93 = "llvm.add"(%92, %55) <{overflowFlags = #llvm.overflow<none>}> : (i128, i128) -> i128
    %94 = "llvm.add"(%93, %48) <{overflowFlags = #llvm.overflow<none>}> : (i128, i128) -> i128
    %95 = "llvm.add"(%94, %62) <{overflowFlags = #llvm.overflow<none>}> : (i128, i128) -> i128
    %96 = "llvm.add"(%95, %91) <{overflowFlags = #llvm.overflow<none>}> : (i128, i128) -> i128
    %97 = "llvm.lshr"(%96, %1) : (i128, i128) -> i128
    %98 = "llvm.trunc"(%96) : (i128) -> i64
    %99 = "llvm.and"(%98, %2) : (i64, i64) -> i64
    %100 = "llvm.and"(%97, %3) : (i128, i128) -> i128
    %101 = "llvm.add"(%50, %47) <{overflowFlags = #llvm.overflow<none>}> : (i128, i128) -> i128
    %102 = "llvm.add"(%101, %54) <{overflowFlags = #llvm.overflow<none>}> : (i128, i128) -> i128
    %103 = "llvm.add"(%102, %45) <{overflowFlags = #llvm.overflow<none>}> : (i128, i128) -> i128
    %104 = "llvm.add"(%103, %61) <{overflowFlags = #llvm.overflow<none>}> : (i128, i128) -> i128
    %105 = "llvm.add"(%104, %100) <{overflowFlags = #llvm.overflow<none>}> : (i128, i128) -> i128
    %106 = "llvm.lshr"(%105, %1) : (i128, i128) -> i128
    %107 = "llvm.trunc"(%106) : (i128) -> i64
    %108 = "llvm.trunc"(%105) : (i128) -> i64
    %109 = "llvm.and"(%108, %2) : (i64, i64) -> i64
    %110 = "llvm.mul"(%107, %0) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %111 = "llvm.add"(%110, %72) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %112 = "llvm.lshr"(%111, %4) : (i64, i64) -> i64
    %113 = "llvm.and"(%111, %2) : (i64, i64) -> i64
    %114 = "llvm.add"(%112, %82) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %115 = "llvm.lshr"(%114, %4) : (i64, i64) -> i64
    %116 = "llvm.and"(%114, %2) : (i64, i64) -> i64
    %117 = "llvm.add"(%115, %90) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    "llvm.store"(%113, %arg0) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (i64, !llvm.ptr) -> ()
    %118 = "llvm.getelementptr"(%arg0) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: 1>}> : (!llvm.ptr) -> !llvm.ptr
    "llvm.store"(%116, %118) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (i64, !llvm.ptr) -> ()
    %119 = "llvm.getelementptr"(%arg0) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: 2>}> : (!llvm.ptr) -> !llvm.ptr
    "llvm.store"(%117, %119) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (i64, !llvm.ptr) -> ()
    %120 = "llvm.getelementptr"(%arg0) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: 3>}> : (!llvm.ptr) -> !llvm.ptr
    "llvm.store"(%99, %120) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (i64, !llvm.ptr) -> ()
    %121 = "llvm.getelementptr"(%arg0) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: 4>}> : (!llvm.ptr) -> !llvm.ptr
    "llvm.store"(%109, %121) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (i64, !llvm.ptr) -> ()
    "llvm.return"() : () -> ()
}
]

def fiat_25519_carry_mul : Cfg (Ctxt.ofList [SLLVM.Ty.ptr, SLLVM.Ty.ptr, SLLVM.Ty.ptr]) [] :=
  [sllvm_cfg_of| fiat_25519_carry_mul_region]

end Firedancer.Ref
