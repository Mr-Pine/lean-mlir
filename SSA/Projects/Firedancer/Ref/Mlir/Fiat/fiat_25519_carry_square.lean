/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
-- build/native/gcc/mlir_canonicalized/ref/region/fiat_25519_carry_square.mlir
import SSA.Projects.SLLVM.Cfg

namespace Firedancer.Ref
open LeanMLIR SLLVM

def fiat_25519_carry_square_region : MLIR.AST.Region 0 := [mlir_region|
{
  ^bb0(%arg0: !llvm.ptr, %arg1: !llvm.ptr):
    %0 = "llvm.mlir.constant"() <{value = 19 : i64}> : () -> i64
    %1 = "llvm.mlir.constant"() <{value = 38 : i64}> : () -> i64
    %2 = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %3 = "llvm.mlir.constant"() <{value = 51 : i128}> : () -> i128
    %4 = "llvm.mlir.constant"() <{value = 2251799813685247 : i64}> : () -> i64
    %5 = "llvm.mlir.constant"() <{value = 18446744073709551615 : i128}> : () -> i128
    %6 = "llvm.mlir.constant"() <{value = 51 : i64}> : () -> i64
    %7 = "llvm.getelementptr"(%arg1) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: 4>}> : (!llvm.ptr) -> !llvm.ptr
    %8 = "llvm.load"(%7) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    %9 = "llvm.mul"(%8, %0) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %10 = "llvm.mul"(%8, %1) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %11 = "llvm.shl"(%8, %2) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %12 = "llvm.getelementptr"(%arg1) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: 3>}> : (!llvm.ptr) -> !llvm.ptr
    %13 = "llvm.load"(%12) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    %14 = "llvm.mul"(%13, %0) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %15 = "llvm.mul"(%13, %1) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %16 = "llvm.shl"(%13, %2) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %17 = "llvm.getelementptr"(%arg1) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: 2>}> : (!llvm.ptr) -> !llvm.ptr
    %18 = "llvm.load"(%17) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    %19 = "llvm.shl"(%18, %2) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %20 = "llvm.getelementptr"(%arg1) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: 1>}> : (!llvm.ptr) -> !llvm.ptr
    %21 = "llvm.load"(%20) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    %22 = "llvm.shl"(%21, %2) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %23 = "llvm.zext"(%8) : (i64) -> i128
    %24 = "llvm.zext"(%9) : (i64) -> i128
    %25 = "llvm.mul"(%24, %23) <{overflowFlags = #llvm.overflow<nuw>}> : (i128, i128) -> i128
    %26 = "llvm.zext"(%13) : (i64) -> i128
    %27 = "llvm.zext"(%10) : (i64) -> i128
    %28 = "llvm.mul"(%26, %27) <{overflowFlags = #llvm.overflow<nuw>}> : (i128, i128) -> i128
    %29 = "llvm.zext"(%14) : (i64) -> i128
    %30 = "llvm.mul"(%29, %26) <{overflowFlags = #llvm.overflow<nuw>}> : (i128, i128) -> i128
    %31 = "llvm.zext"(%18) : (i64) -> i128
    %32 = "llvm.mul"(%31, %27) <{overflowFlags = #llvm.overflow<nuw>}> : (i128, i128) -> i128
    %33 = "llvm.zext"(%15) : (i64) -> i128
    %34 = "llvm.mul"(%31, %33) <{overflowFlags = #llvm.overflow<nuw>}> : (i128, i128) -> i128
    %35 = "llvm.mul"(%31, %31) <{overflowFlags = #llvm.overflow<nuw>}> : (i128, i128) -> i128
    %36 = "llvm.zext"(%21) : (i64) -> i128
    %37 = "llvm.mul"(%36, %27) <{overflowFlags = #llvm.overflow<nuw>}> : (i128, i128) -> i128
    %38 = "llvm.zext"(%16) : (i64) -> i128
    %39 = "llvm.mul"(%36, %38) <{overflowFlags = #llvm.overflow<nuw>}> : (i128, i128) -> i128
    %40 = "llvm.zext"(%19) : (i64) -> i128
    %41 = "llvm.mul"(%36, %40) <{overflowFlags = #llvm.overflow<nuw>}> : (i128, i128) -> i128
    %42 = "llvm.mul"(%36, %36) <{overflowFlags = #llvm.overflow<nuw>}> : (i128, i128) -> i128
    %43 = "llvm.load"(%arg1) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    %44 = "llvm.zext"(%43) : (i64) -> i128
    %45 = "llvm.zext"(%11) : (i64) -> i128
    %46 = "llvm.mul"(%44, %45) <{overflowFlags = #llvm.overflow<nuw>}> : (i128, i128) -> i128
    %47 = "llvm.mul"(%44, %38) <{overflowFlags = #llvm.overflow<nuw>}> : (i128, i128) -> i128
    %48 = "llvm.mul"(%44, %40) <{overflowFlags = #llvm.overflow<nuw>}> : (i128, i128) -> i128
    %49 = "llvm.zext"(%22) : (i64) -> i128
    %50 = "llvm.mul"(%44, %49) <{overflowFlags = #llvm.overflow<nuw>}> : (i128, i128) -> i128
    %51 = "llvm.mul"(%44, %44) <{overflowFlags = #llvm.overflow<nuw>}> : (i128, i128) -> i128
    %52 = "llvm.add"(%37, %34) <{overflowFlags = #llvm.overflow<none>}> : (i128, i128) -> i128
    %53 = "llvm.add"(%52, %51) <{overflowFlags = #llvm.overflow<none>}> : (i128, i128) -> i128
    %54 = "llvm.lshr"(%53, %3) : (i128, i128) -> i128
    %55 = "llvm.trunc"(%53) : (i128) -> i64
    %56 = "llvm.and"(%55, %4) : (i64, i64) -> i64
    %57 = "llvm.add"(%39, %35) <{overflowFlags = #llvm.overflow<none>}> : (i128, i128) -> i128
    %58 = "llvm.add"(%57, %46) <{overflowFlags = #llvm.overflow<none>}> : (i128, i128) -> i128
    %59 = "llvm.add"(%41, %25) <{overflowFlags = #llvm.overflow<none>}> : (i128, i128) -> i128
    %60 = "llvm.add"(%59, %47) <{overflowFlags = #llvm.overflow<none>}> : (i128, i128) -> i128
    %61 = "llvm.add"(%42, %28) <{overflowFlags = #llvm.overflow<none>}> : (i128, i128) -> i128
    %62 = "llvm.add"(%61, %48) <{overflowFlags = #llvm.overflow<none>}> : (i128, i128) -> i128
    %63 = "llvm.add"(%32, %30) <{overflowFlags = #llvm.overflow<none>}> : (i128, i128) -> i128
    %64 = "llvm.add"(%63, %50) <{overflowFlags = #llvm.overflow<none>}> : (i128, i128) -> i128
    %65 = "llvm.and"(%54, %5) : (i128, i128) -> i128
    %66 = "llvm.add"(%64, %65) <{overflowFlags = #llvm.overflow<none>}> : (i128, i128) -> i128
    %67 = "llvm.lshr"(%66, %3) : (i128, i128) -> i128
    %68 = "llvm.trunc"(%66) : (i128) -> i64
    %69 = "llvm.and"(%68, %4) : (i64, i64) -> i64
    %70 = "llvm.and"(%67, %5) : (i128, i128) -> i128
    %71 = "llvm.add"(%62, %70) <{overflowFlags = #llvm.overflow<none>}> : (i128, i128) -> i128
    %72 = "llvm.lshr"(%71, %3) : (i128, i128) -> i128
    %73 = "llvm.trunc"(%71) : (i128) -> i64
    %74 = "llvm.and"(%73, %4) : (i64, i64) -> i64
    %75 = "llvm.and"(%72, %5) : (i128, i128) -> i128
    %76 = "llvm.add"(%60, %75) <{overflowFlags = #llvm.overflow<none>}> : (i128, i128) -> i128
    %77 = "llvm.lshr"(%76, %3) : (i128, i128) -> i128
    %78 = "llvm.trunc"(%76) : (i128) -> i64
    %79 = "llvm.and"(%78, %4) : (i64, i64) -> i64
    %80 = "llvm.and"(%77, %5) : (i128, i128) -> i128
    %81 = "llvm.add"(%58, %80) <{overflowFlags = #llvm.overflow<none>}> : (i128, i128) -> i128
    %82 = "llvm.lshr"(%81, %3) : (i128, i128) -> i128
    %83 = "llvm.trunc"(%82) : (i128) -> i64
    %84 = "llvm.trunc"(%81) : (i128) -> i64
    %85 = "llvm.and"(%84, %4) : (i64, i64) -> i64
    %86 = "llvm.mul"(%83, %0) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %87 = "llvm.add"(%86, %56) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %88 = "llvm.lshr"(%87, %6) : (i64, i64) -> i64
    %89 = "llvm.and"(%87, %4) : (i64, i64) -> i64
    %90 = "llvm.add"(%88, %69) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %91 = "llvm.lshr"(%90, %6) : (i64, i64) -> i64
    %92 = "llvm.and"(%90, %4) : (i64, i64) -> i64
    %93 = "llvm.add"(%91, %74) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    "llvm.store"(%89, %arg0) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (i64, !llvm.ptr) -> ()
    %94 = "llvm.getelementptr"(%arg0) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: 1>}> : (!llvm.ptr) -> !llvm.ptr
    "llvm.store"(%92, %94) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (i64, !llvm.ptr) -> ()
    %95 = "llvm.getelementptr"(%arg0) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: 2>}> : (!llvm.ptr) -> !llvm.ptr
    "llvm.store"(%93, %95) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (i64, !llvm.ptr) -> ()
    %96 = "llvm.getelementptr"(%arg0) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: 3>}> : (!llvm.ptr) -> !llvm.ptr
    "llvm.store"(%79, %96) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (i64, !llvm.ptr) -> ()
    %97 = "llvm.getelementptr"(%arg0) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: 4>}> : (!llvm.ptr) -> !llvm.ptr
    "llvm.store"(%85, %97) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (i64, !llvm.ptr) -> ()
    "llvm.return"() : () -> ()
}
]

sllvm_cfg_def fiat_25519_carry_square : Cfg (Ctxt.ofList [SLLVM.Ty.ptr, SLLVM.Ty.ptr]) [] :=
  [sllvm_cfg_of| fiat_25519_carry_square_region]

end Firedancer.Ref
