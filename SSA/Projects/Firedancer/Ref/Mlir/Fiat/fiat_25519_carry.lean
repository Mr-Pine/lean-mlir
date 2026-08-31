/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.SLLVM.Cfg

/-!
# `fiat_25519_carry` (ref)

Byte-identical (modulo indentation) to
`build/native/gcc/mlir/ref/region/fiat_25519_carry.mlir`. The fiat-crypto carry reduction: two
`!llvm.ptr` parameters (out, a), straight-line.
-/

namespace Firedancer.Ref
open LeanMLIR SLLVM

def fiat_25519_carry_region : MLIR.AST.Region 0 := [mlir_region|
{
  ^bb0(%arg0: !llvm.ptr, %arg1: !llvm.ptr):
    %0 = "llvm.mlir.constant"() <{value = 51 : i64}> : () -> i64
    %1 = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %2 = "llvm.mlir.constant"() <{value = 2 : i64}> : () -> i64
    %3 = "llvm.mlir.constant"() <{value = 3 : i64}> : () -> i64
    %4 = "llvm.mlir.constant"() <{value = 4 : i64}> : () -> i64
    %5 = "llvm.mlir.constant"() <{value = 2251799813685247 : i64}> : () -> i64
    %6 = "llvm.mlir.constant"() <{value = 19 : i64}> : () -> i64
    %7 = "llvm.load"(%arg1) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> i64
    %8 = "llvm.lshr"(%7, %0) : (i64, i64) -> i64
    %9 = "llvm.getelementptr"(%arg1, %1) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %10 = "llvm.load"(%9) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> i64
    %11 = "llvm.add"(%8, %10) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %12 = "llvm.lshr"(%11, %0) : (i64, i64) -> i64
    %13 = "llvm.getelementptr"(%arg1, %2) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %14 = "llvm.load"(%13) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> i64
    %15 = "llvm.add"(%12, %14) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %16 = "llvm.lshr"(%15, %0) : (i64, i64) -> i64
    %17 = "llvm.getelementptr"(%arg1, %3) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %18 = "llvm.load"(%17) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> i64
    %19 = "llvm.add"(%16, %18) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %20 = "llvm.lshr"(%19, %0) : (i64, i64) -> i64
    %21 = "llvm.getelementptr"(%arg1, %4) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %22 = "llvm.load"(%21) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> i64
    %23 = "llvm.add"(%20, %22) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %24 = "llvm.and"(%7, %5) : (i64, i64) -> i64
    %25 = "llvm.lshr"(%23, %0) : (i64, i64) -> i64
    %26 = "llvm.mul"(%25, %6) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %27 = "llvm.add"(%26, %24) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %28 = "llvm.lshr"(%27, %0) : (i64, i64) -> i64
    %29 = "llvm.and"(%11, %5) : (i64, i64) -> i64
    %30 = "llvm.add"(%28, %29) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %31 = "llvm.and"(%27, %5) : (i64, i64) -> i64
    %32 = "llvm.and"(%30, %5) : (i64, i64) -> i64
    %33 = "llvm.lshr"(%30, %0) : (i64, i64) -> i64
    %34 = "llvm.and"(%15, %5) : (i64, i64) -> i64
    %35 = "llvm.add"(%33, %34) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %36 = "llvm.and"(%19, %5) : (i64, i64) -> i64
    %37 = "llvm.and"(%23, %5) : (i64, i64) -> i64
    "llvm.store"(%31, %arg0) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (i64, !llvm.ptr) -> ()
    %38 = "llvm.getelementptr"(%arg0, %1) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%32, %38) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (i64, !llvm.ptr) -> ()
    %39 = "llvm.getelementptr"(%arg0, %2) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%35, %39) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (i64, !llvm.ptr) -> ()
    %40 = "llvm.getelementptr"(%arg0, %3) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%36, %40) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (i64, !llvm.ptr) -> ()
    %41 = "llvm.getelementptr"(%arg0, %4) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%37, %41) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (i64, !llvm.ptr) -> ()
    "llvm.return"() : () -> ()
}
]

def fiat_25519_carry : Cfg (Ctxt.ofList [SLLVM.Ty.ptr, SLLVM.Ty.ptr]) [] :=
  [sllvm_cfg_of| fiat_25519_carry_region]

end Firedancer.Ref
