/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.SLLVM.Cfg

/-!
# `fiat_25519_carry_mul` (ref)

Byte-identical (modulo indentation) to
`build/native/gcc/mlir/ref/region/fiat_25519_carry_mul.mlir`. The fiat-crypto
carry-mul: three `!llvm.ptr` parameters (out, a, b), straight-line.
-/

namespace Firedancer.Ref
open LeanMLIR SLLVM

def fiat_25519_carry_mul_region : MLIR.AST.Region 0 := [mlir_region|
{
  ^bb0(%arg0: !llvm.ptr, %arg1: !llvm.ptr, %arg2: !llvm.ptr):
    %0 = "llvm.mlir.constant"() <{value = 4 : i64}> : () -> i64
    %1 = "llvm.mlir.constant"() <{value = 19 : i64}> : () -> i64
    %2 = "llvm.mlir.constant"() <{value = 3 : i64}> : () -> i64
    %3 = "llvm.mlir.constant"() <{value = 2 : i64}> : () -> i64
    %4 = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %5 = "llvm.mlir.constant"() <{value = 51 : i128}> : () -> i128
    %6 = "llvm.mlir.constant"() <{value = 2251799813685247 : i64}> : () -> i64
    %7 = "llvm.mlir.constant"() <{value = 18446744073709551615 : i128}> : () -> i128
    %8 = "llvm.mlir.constant"() <{value = 51 : i64}> : () -> i64
    %9 = "llvm.getelementptr"(%arg1, %0) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %10 = "llvm.load"(%9) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> i64
    %11 = "llvm.zext"(%10) : (i64) -> i128
    %12 = "llvm.getelementptr"(%arg2, %0) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %13 = "llvm.load"(%12) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> i64
    %14 = "llvm.mul"(%13, %1) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %15 = "llvm.zext"(%14) : (i64) -> i128
    %16 = "llvm.mul"(%15, %11) <{overflowFlags = #llvm.overflow<nuw>}> : (i128, i128) -> i128
    %17 = "llvm.getelementptr"(%arg2, %2) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %18 = "llvm.load"(%17) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> i64
    %19 = "llvm.mul"(%18, %1) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %20 = "llvm.zext"(%19) : (i64) -> i128
    %21 = "llvm.mul"(%20, %11) <{overflowFlags = #llvm.overflow<nuw>}> : (i128, i128) -> i128
    %22 = "llvm.getelementptr"(%arg2, %3) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %23 = "llvm.load"(%22) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> i64
    %24 = "llvm.mul"(%23, %1) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %25 = "llvm.zext"(%24) : (i64) -> i128
    %26 = "llvm.mul"(%25, %11) <{overflowFlags = #llvm.overflow<nuw>}> : (i128, i128) -> i128
    %27 = "llvm.getelementptr"(%arg2, %4) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %28 = "llvm.load"(%27) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> i64
    %29 = "llvm.mul"(%28, %1) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %30 = "llvm.zext"(%29) : (i64) -> i128
    %31 = "llvm.mul"(%30, %11) <{overflowFlags = #llvm.overflow<nuw>}> : (i128, i128) -> i128
    %32 = "llvm.getelementptr"(%arg1, %2) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %33 = "llvm.load"(%32) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> i64
    %34 = "llvm.zext"(%33) : (i64) -> i128
    %35 = "llvm.mul"(%34, %15) <{overflowFlags = #llvm.overflow<nuw>}> : (i128, i128) -> i128
    %36 = "llvm.mul"(%34, %20) <{overflowFlags = #llvm.overflow<nuw>}> : (i128, i128) -> i128
    %37 = "llvm.mul"(%34, %25) <{overflowFlags = #llvm.overflow<nuw>}> : (i128, i128) -> i128
    %38 = "llvm.getelementptr"(%arg1, %3) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %39 = "llvm.load"(%38) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> i64
    %40 = "llvm.zext"(%39) : (i64) -> i128
    %41 = "llvm.mul"(%40, %15) <{overflowFlags = #llvm.overflow<nuw>}> : (i128, i128) -> i128
    %42 = "llvm.mul"(%40, %20) <{overflowFlags = #llvm.overflow<nuw>}> : (i128, i128) -> i128
    %43 = "llvm.getelementptr"(%arg1, %4) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %44 = "llvm.load"(%43) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> i64
    %45 = "llvm.zext"(%44) : (i64) -> i128
    %46 = "llvm.mul"(%45, %15) <{overflowFlags = #llvm.overflow<nuw>}> : (i128, i128) -> i128
    %47 = "llvm.load"(%arg2) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> i64
    %48 = "llvm.zext"(%47) : (i64) -> i128
    %49 = "llvm.mul"(%48, %11) <{overflowFlags = #llvm.overflow<nuw>}> : (i128, i128) -> i128
    %50 = "llvm.zext"(%28) : (i64) -> i128
    %51 = "llvm.mul"(%34, %50) <{overflowFlags = #llvm.overflow<nuw>}> : (i128, i128) -> i128
    %52 = "llvm.mul"(%48, %34) <{overflowFlags = #llvm.overflow<nuw>}> : (i128, i128) -> i128
    %53 = "llvm.zext"(%23) : (i64) -> i128
    %54 = "llvm.mul"(%40, %53) <{overflowFlags = #llvm.overflow<nuw>}> : (i128, i128) -> i128
    %55 = "llvm.mul"(%40, %50) <{overflowFlags = #llvm.overflow<nuw>}> : (i128, i128) -> i128
    %56 = "llvm.mul"(%48, %40) <{overflowFlags = #llvm.overflow<nuw>}> : (i128, i128) -> i128
    %57 = "llvm.zext"(%18) : (i64) -> i128
    %58 = "llvm.mul"(%45, %57) <{overflowFlags = #llvm.overflow<nuw>}> : (i128, i128) -> i128
    %59 = "llvm.mul"(%45, %53) <{overflowFlags = #llvm.overflow<nuw>}> : (i128, i128) -> i128
    %60 = "llvm.mul"(%45, %50) <{overflowFlags = #llvm.overflow<nuw>}> : (i128, i128) -> i128
    %61 = "llvm.mul"(%48, %45) <{overflowFlags = #llvm.overflow<nuw>}> : (i128, i128) -> i128
    %62 = "llvm.load"(%arg1) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> i64
    %63 = "llvm.zext"(%62) : (i64) -> i128
    %64 = "llvm.zext"(%13) : (i64) -> i128
    %65 = "llvm.mul"(%63, %64) <{overflowFlags = #llvm.overflow<nuw>}> : (i128, i128) -> i128
    %66 = "llvm.mul"(%63, %57) <{overflowFlags = #llvm.overflow<nuw>}> : (i128, i128) -> i128
    %67 = "llvm.mul"(%63, %53) <{overflowFlags = #llvm.overflow<nuw>}> : (i128, i128) -> i128
    %68 = "llvm.mul"(%63, %50) <{overflowFlags = #llvm.overflow<nuw>}> : (i128, i128) -> i128
    %69 = "llvm.mul"(%63, %48) <{overflowFlags = #llvm.overflow<nuw>}> : (i128, i128) -> i128
    %70 = "llvm.add"(%37, %31) <{overflowFlags = #llvm.overflow<none>}> : (i128, i128) -> i128
    %71 = "llvm.add"(%70, %42) <{overflowFlags = #llvm.overflow<none>}> : (i128, i128) -> i128
    %72 = "llvm.add"(%71, %46) <{overflowFlags = #llvm.overflow<none>}> : (i128, i128) -> i128
    %73 = "llvm.add"(%72, %69) <{overflowFlags = #llvm.overflow<none>}> : (i128, i128) -> i128
    %74 = "llvm.lshr"(%73, %5) : (i128, i128) -> i128
    %75 = "llvm.trunc"(%73) : (i128) -> i64
    %76 = "llvm.and"(%75, %6) : (i64, i64) -> i64
    %77 = "llvm.add"(%35, %21) <{overflowFlags = #llvm.overflow<none>}> : (i128, i128) -> i128
    %78 = "llvm.add"(%36, %26) <{overflowFlags = #llvm.overflow<none>}> : (i128, i128) -> i128
    %79 = "llvm.add"(%78, %41) <{overflowFlags = #llvm.overflow<none>}> : (i128, i128) -> i128
    %80 = "llvm.add"(%79, %61) <{overflowFlags = #llvm.overflow<none>}> : (i128, i128) -> i128
    %81 = "llvm.add"(%80, %68) <{overflowFlags = #llvm.overflow<none>}> : (i128, i128) -> i128
    %82 = "llvm.and"(%74, %7) : (i128, i128) -> i128
    %83 = "llvm.add"(%81, %82) <{overflowFlags = #llvm.overflow<none>}> : (i128, i128) -> i128
    %84 = "llvm.lshr"(%83, %5) : (i128, i128) -> i128
    %85 = "llvm.trunc"(%83) : (i128) -> i64
    %86 = "llvm.and"(%85, %6) : (i64, i64) -> i64
    %87 = "llvm.and"(%84, %7) : (i128, i128) -> i128
    %88 = "llvm.add"(%77, %60) <{overflowFlags = #llvm.overflow<none>}> : (i128, i128) -> i128
    %89 = "llvm.add"(%88, %56) <{overflowFlags = #llvm.overflow<none>}> : (i128, i128) -> i128
    %90 = "llvm.add"(%89, %67) <{overflowFlags = #llvm.overflow<none>}> : (i128, i128) -> i128
    %91 = "llvm.add"(%90, %87) <{overflowFlags = #llvm.overflow<none>}> : (i128, i128) -> i128
    %92 = "llvm.lshr"(%91, %5) : (i128, i128) -> i128
    %93 = "llvm.trunc"(%91) : (i128) -> i64
    %94 = "llvm.and"(%93, %6) : (i64, i64) -> i64
    %95 = "llvm.and"(%92, %7) : (i128, i128) -> i128
    %96 = "llvm.add"(%55, %16) <{overflowFlags = #llvm.overflow<none>}> : (i128, i128) -> i128
    %97 = "llvm.add"(%96, %59) <{overflowFlags = #llvm.overflow<none>}> : (i128, i128) -> i128
    %98 = "llvm.add"(%97, %52) <{overflowFlags = #llvm.overflow<none>}> : (i128, i128) -> i128
    %99 = "llvm.add"(%98, %66) <{overflowFlags = #llvm.overflow<none>}> : (i128, i128) -> i128
    %100 = "llvm.add"(%99, %95) <{overflowFlags = #llvm.overflow<none>}> : (i128, i128) -> i128
    %101 = "llvm.lshr"(%100, %5) : (i128, i128) -> i128
    %102 = "llvm.trunc"(%100) : (i128) -> i64
    %103 = "llvm.and"(%102, %6) : (i64, i64) -> i64
    %104 = "llvm.and"(%101, %7) : (i128, i128) -> i128
    %105 = "llvm.add"(%54, %51) <{overflowFlags = #llvm.overflow<none>}> : (i128, i128) -> i128
    %106 = "llvm.add"(%105, %58) <{overflowFlags = #llvm.overflow<none>}> : (i128, i128) -> i128
    %107 = "llvm.add"(%106, %49) <{overflowFlags = #llvm.overflow<none>}> : (i128, i128) -> i128
    %108 = "llvm.add"(%107, %65) <{overflowFlags = #llvm.overflow<none>}> : (i128, i128) -> i128
    %109 = "llvm.add"(%108, %104) <{overflowFlags = #llvm.overflow<none>}> : (i128, i128) -> i128
    %110 = "llvm.lshr"(%109, %5) : (i128, i128) -> i128
    %111 = "llvm.trunc"(%110) : (i128) -> i64
    %112 = "llvm.trunc"(%109) : (i128) -> i64
    %113 = "llvm.and"(%112, %6) : (i64, i64) -> i64
    %114 = "llvm.mul"(%111, %1) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %115 = "llvm.add"(%114, %76) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %116 = "llvm.lshr"(%115, %8) : (i64, i64) -> i64
    %117 = "llvm.and"(%115, %6) : (i64, i64) -> i64
    %118 = "llvm.add"(%116, %86) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %119 = "llvm.lshr"(%118, %8) : (i64, i64) -> i64
    %120 = "llvm.and"(%118, %6) : (i64, i64) -> i64
    %121 = "llvm.add"(%119, %94) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    "llvm.store"(%117, %arg0) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (i64, !llvm.ptr) -> ()
    %122 = "llvm.getelementptr"(%arg0, %4) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%120, %122) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (i64, !llvm.ptr) -> ()
    %123 = "llvm.getelementptr"(%arg0, %3) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%121, %123) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (i64, !llvm.ptr) -> ()
    %124 = "llvm.getelementptr"(%arg0, %2) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%103, %124) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (i64, !llvm.ptr) -> ()
    %125 = "llvm.getelementptr"(%arg0, %0) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%113, %125) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (i64, !llvm.ptr) -> ()
    "llvm.return"() : () -> ()
}
]

def fiat_25519_carry_mul : Cfg (Ctxt.ofList [SLLVM.Ty.ptr, SLLVM.Ty.ptr, SLLVM.Ty.ptr]) [] :=
  [sllvm_cfg_of| fiat_25519_carry_mul_region]

end Firedancer.Ref
