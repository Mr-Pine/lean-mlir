/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.SLLVM.Cfg

/-!
# `fiat_25519_sub` (ref)

Byte-identical (modulo indentation) to
`build/native/gcc/mlir/ref/region/fiat_25519_sub.mlir`. A fiat-crypto field subtraction: three
`!llvm.ptr` parameters (out, a, b), straight-line.
-/

namespace Firedancer.Ref
open LeanMLIR SLLVM

def fiat_25519_sub_region : MLIR.AST.Region 0 := [mlir_region|
{
  ^bb0(%arg0: !llvm.ptr, %arg1: !llvm.ptr, %arg2: !llvm.ptr):
    %0 = "llvm.mlir.constant"() <{value = 4503599627370458 : i64}> : () -> i64
    %1 = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %2 = "llvm.mlir.constant"() <{value = 4503599627370494 : i64}> : () -> i64
    %3 = "llvm.mlir.constant"() <{value = 2 : i64}> : () -> i64
    %4 = "llvm.mlir.constant"() <{value = 3 : i64}> : () -> i64
    %5 = "llvm.mlir.constant"() <{value = 4 : i64}> : () -> i64
    %6 = "llvm.load"(%arg1) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> i64
    %7 = "llvm.add"(%6, %0) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %8 = "llvm.load"(%arg2) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> i64
    %9 = "llvm.sub"(%7, %8) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %10 = "llvm.getelementptr"(%arg1, %1) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %11 = "llvm.load"(%10) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> i64
    %12 = "llvm.add"(%11, %2) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %13 = "llvm.getelementptr"(%arg2, %1) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %14 = "llvm.load"(%13) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> i64
    %15 = "llvm.sub"(%12, %14) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %16 = "llvm.getelementptr"(%arg1, %3) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %17 = "llvm.load"(%16) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> i64
    %18 = "llvm.add"(%17, %2) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %19 = "llvm.getelementptr"(%arg2, %3) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %20 = "llvm.load"(%19) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> i64
    %21 = "llvm.sub"(%18, %20) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %22 = "llvm.getelementptr"(%arg1, %4) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %23 = "llvm.load"(%22) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> i64
    %24 = "llvm.add"(%23, %2) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %25 = "llvm.getelementptr"(%arg2, %4) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %26 = "llvm.load"(%25) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> i64
    %27 = "llvm.sub"(%24, %26) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %28 = "llvm.getelementptr"(%arg1, %5) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %29 = "llvm.load"(%28) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> i64
    %30 = "llvm.add"(%29, %2) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %31 = "llvm.getelementptr"(%arg2, %5) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %32 = "llvm.load"(%31) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> i64
    %33 = "llvm.sub"(%30, %32) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    "llvm.store"(%9, %arg0) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (i64, !llvm.ptr) -> ()
    %34 = "llvm.getelementptr"(%arg0, %1) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%15, %34) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (i64, !llvm.ptr) -> ()
    %35 = "llvm.getelementptr"(%arg0, %3) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%21, %35) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (i64, !llvm.ptr) -> ()
    %36 = "llvm.getelementptr"(%arg0, %4) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%27, %36) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (i64, !llvm.ptr) -> ()
    %37 = "llvm.getelementptr"(%arg0, %5) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%33, %37) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (i64, !llvm.ptr) -> ()
    "llvm.return"() : () -> ()
}
]

def fiat_25519_sub : Cfg (Ctxt.ofList [SLLVM.Ty.ptr, SLLVM.Ty.ptr, SLLVM.Ty.ptr]) [] :=
  [sllvm_cfg_of| fiat_25519_sub_region]

end Firedancer.Ref
