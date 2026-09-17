/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
-- build/native/gcc/mlir_canonicalized/ref/region/fiat_25519_sub.mlir
import SSA.Projects.SLLVM.Cfg

namespace Firedancer.Ref
open LeanMLIR SLLVM

def fiat_25519_sub_region : MLIR.AST.Region 0 := [mlir_region|
{
  ^bb0(%arg0: !llvm.ptr, %arg1: !llvm.ptr, %arg2: !llvm.ptr):
    %0 = "llvm.mlir.constant"() <{value = 4503599627370458 : i64}> : () -> i64
    %1 = "llvm.mlir.constant"() <{value = 4503599627370494 : i64}> : () -> i64
    %2 = "llvm.load"(%arg1) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    %3 = "llvm.add"(%2, %0) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %4 = "llvm.load"(%arg2) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    %5 = "llvm.sub"(%3, %4) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %6 = "llvm.getelementptr"(%arg1) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: 1>}> : (!llvm.ptr) -> !llvm.ptr
    %7 = "llvm.load"(%6) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    %8 = "llvm.add"(%7, %1) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %9 = "llvm.getelementptr"(%arg2) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: 1>}> : (!llvm.ptr) -> !llvm.ptr
    %10 = "llvm.load"(%9) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    %11 = "llvm.sub"(%8, %10) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %12 = "llvm.getelementptr"(%arg1) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: 2>}> : (!llvm.ptr) -> !llvm.ptr
    %13 = "llvm.load"(%12) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    %14 = "llvm.add"(%13, %1) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %15 = "llvm.getelementptr"(%arg2) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: 2>}> : (!llvm.ptr) -> !llvm.ptr
    %16 = "llvm.load"(%15) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    %17 = "llvm.sub"(%14, %16) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %18 = "llvm.getelementptr"(%arg1) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: 3>}> : (!llvm.ptr) -> !llvm.ptr
    %19 = "llvm.load"(%18) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    %20 = "llvm.add"(%19, %1) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %21 = "llvm.getelementptr"(%arg2) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: 3>}> : (!llvm.ptr) -> !llvm.ptr
    %22 = "llvm.load"(%21) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    %23 = "llvm.sub"(%20, %22) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %24 = "llvm.getelementptr"(%arg1) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: 4>}> : (!llvm.ptr) -> !llvm.ptr
    %25 = "llvm.load"(%24) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    %26 = "llvm.add"(%25, %1) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %27 = "llvm.getelementptr"(%arg2) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: 4>}> : (!llvm.ptr) -> !llvm.ptr
    %28 = "llvm.load"(%27) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    %29 = "llvm.sub"(%26, %28) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    "llvm.store"(%5, %arg0) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (i64, !llvm.ptr) -> ()
    %30 = "llvm.getelementptr"(%arg0) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: 1>}> : (!llvm.ptr) -> !llvm.ptr
    "llvm.store"(%11, %30) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (i64, !llvm.ptr) -> ()
    %31 = "llvm.getelementptr"(%arg0) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: 2>}> : (!llvm.ptr) -> !llvm.ptr
    "llvm.store"(%17, %31) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (i64, !llvm.ptr) -> ()
    %32 = "llvm.getelementptr"(%arg0) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: 3>}> : (!llvm.ptr) -> !llvm.ptr
    "llvm.store"(%23, %32) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (i64, !llvm.ptr) -> ()
    %33 = "llvm.getelementptr"(%arg0) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: 4>}> : (!llvm.ptr) -> !llvm.ptr
    "llvm.store"(%29, %33) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (i64, !llvm.ptr) -> ()
    "llvm.return"() : () -> ()
}
]

sllvm_cfg_def fiat_25519_sub : Cfg (Ctxt.ofList [SLLVM.Ty.ptr, SLLVM.Ty.ptr, SLLVM.Ty.ptr]) [] :=
  [sllvm_cfg_of| fiat_25519_sub_region]

end Firedancer.Ref
