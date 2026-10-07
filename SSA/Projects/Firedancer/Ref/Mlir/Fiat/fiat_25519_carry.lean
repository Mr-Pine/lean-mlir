/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
-- build/native/gcc/mlir_canonicalized/ref/region/fiat_25519_carry.mlir
module

public import SSA.Projects.SLLVM.Cfg

@[expose] public section

namespace Firedancer.Ref
open LeanMLIR SLLVM

def fiat_25519_carry_region : MLIR.AST.Region 0 := [mlir_region|
{
  ^bb0(%arg0: !llvm.ptr, %arg1: !llvm.ptr):
    %0 = "llvm.mlir.constant"() <{value = 51 : i64}> : () -> i64
    %1 = "llvm.mlir.constant"() <{value = 2251799813685247 : i64}> : () -> i64
    %2 = "llvm.mlir.constant"() <{value = 19 : i64}> : () -> i64
    %3 = "llvm.load"(%arg1) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    %4 = "llvm.lshr"(%3, %0) : (i64, i64) -> i64
    %5 = "llvm.getelementptr"(%arg1) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: 1>}> : (!llvm.ptr) -> !llvm.ptr
    %6 = "llvm.load"(%5) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    %7 = "llvm.add"(%4, %6) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %8 = "llvm.lshr"(%7, %0) : (i64, i64) -> i64
    %9 = "llvm.getelementptr"(%arg1) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: 2>}> : (!llvm.ptr) -> !llvm.ptr
    %10 = "llvm.load"(%9) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    %11 = "llvm.add"(%8, %10) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %12 = "llvm.lshr"(%11, %0) : (i64, i64) -> i64
    %13 = "llvm.getelementptr"(%arg1) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: 3>}> : (!llvm.ptr) -> !llvm.ptr
    %14 = "llvm.load"(%13) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    %15 = "llvm.add"(%12, %14) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %16 = "llvm.lshr"(%15, %0) : (i64, i64) -> i64
    %17 = "llvm.getelementptr"(%arg1) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: 4>}> : (!llvm.ptr) -> !llvm.ptr
    %18 = "llvm.load"(%17) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    %19 = "llvm.add"(%16, %18) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %20 = "llvm.and"(%3, %1) : (i64, i64) -> i64
    %21 = "llvm.lshr"(%19, %0) : (i64, i64) -> i64
    %22 = "llvm.mul"(%21, %2) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %23 = "llvm.add"(%22, %20) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %24 = "llvm.lshr"(%23, %0) : (i64, i64) -> i64
    %25 = "llvm.and"(%7, %1) : (i64, i64) -> i64
    %26 = "llvm.add"(%24, %25) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %27 = "llvm.and"(%23, %1) : (i64, i64) -> i64
    %28 = "llvm.and"(%26, %1) : (i64, i64) -> i64
    %29 = "llvm.lshr"(%26, %0) : (i64, i64) -> i64
    %30 = "llvm.and"(%11, %1) : (i64, i64) -> i64
    %31 = "llvm.add"(%29, %30) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %32 = "llvm.and"(%15, %1) : (i64, i64) -> i64
    %33 = "llvm.and"(%19, %1) : (i64, i64) -> i64
    "llvm.store"(%27, %arg0) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (i64, !llvm.ptr) -> ()
    %34 = "llvm.getelementptr"(%arg0) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: 1>}> : (!llvm.ptr) -> !llvm.ptr
    "llvm.store"(%28, %34) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (i64, !llvm.ptr) -> ()
    %35 = "llvm.getelementptr"(%arg0) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: 2>}> : (!llvm.ptr) -> !llvm.ptr
    "llvm.store"(%31, %35) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (i64, !llvm.ptr) -> ()
    %36 = "llvm.getelementptr"(%arg0) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: 3>}> : (!llvm.ptr) -> !llvm.ptr
    "llvm.store"(%32, %36) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (i64, !llvm.ptr) -> ()
    %37 = "llvm.getelementptr"(%arg0) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: 4>}> : (!llvm.ptr) -> !llvm.ptr
    "llvm.store"(%33, %37) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (i64, !llvm.ptr) -> ()
    "llvm.return"() : () -> ()
}
]

sllvm_cfg_def fiat_25519_carry : Cfg (Ctxt.ofList [SLLVM.Ty.ptr, SLLVM.Ty.ptr]) [] :=
  [sllvm_cfg_of| fiat_25519_carry_region]

end Firedancer.Ref
