/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
-- build/native/gcc/mlir_canonicalized/{ref,avx512}/region/fd_curve25519_scalar_wnaf.mlir
import SSA.Projects.SLLVM.Cfg
import SSA.Projects.Firedancer.Common.Mlir.Scalar.fd_int_min

namespace Firedancer.Common
open LeanMLIR SLLVM

def fd_curve25519_scalar_wnaf_region : MLIR.AST.Region 0 := [mlir_region|
{
  ^bb0(%arg0: !llvm.ptr, %arg1: !llvm.ptr, %arg2: i32):
    %0 = "llvm.mlir.constant"() <{value = -1 : i32}> : () -> i32
    %1 = "llvm.mlir.constant"() <{value = 0 : i64}> : () -> i64
    %2 = "llvm.mlir.constant"() <{value = 3 : i64}> : () -> i64
    %3 = "llvm.mlir.constant"() <{value = 536870911 : i64}> : () -> i64
    %4 = "llvm.mlir.constant"() <{value = 7 : i16}> : () -> i16
    %5 = "llvm.mlir.constant"() <{value = 1 : i16}> : () -> i16
    %6 = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %7 = "llvm.mlir.constant"() <{value = 255 : i64}> : () -> i64
    %8 = "llvm.mlir.constant"() <{value = 0 : i16}> : () -> i16
    %9 = "llvm.mlir.constant"() <{value = 256 : i32}> : () -> i32
    %10 = "llvm.mlir.constant"() <{value = 16 : i32}> : () -> i32
    %11 = "llvm.mlir.constant"() <{value = 15 : i32}> : () -> i32
    %12 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %13 = "llvm.mlir.constant"() <{value = 255 : i32}> : () -> i32
    %14 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %15 = "llvm.mlir.constant"() <{value = 65536 : i32}> : () -> i32
    %16 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %17 = "llvm.mlir.constant"() <{value = 256 : i64}> : () -> i64
    %18 = "llvm.shl"(%0, %arg2) <{overflowFlags = #llvm.overflow<nsw>}> : (i32, i32) -> i32
    "llvm.br"(%1)[^bb2] : (i64) -> ()
  ^bb1:  // pred: ^bb2
    %19 = "llvm.xor"(%18, %0) : (i32, i32) -> i32
    %20 = "llvm.getelementptr"(%arg0) <{elem_type = i16, inbounds, rawConstantIndices = array<i32: 255>}> : (!llvm.ptr) -> !llvm.ptr
    "llvm.store"(%8, %20) <{alignment = 2 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag2]}> : (i16, !llvm.ptr) -> ()
    "llvm.br"(%1)[^bb3] : (i64) -> ()
  ^bb2(%21: i64):  // 2 preds: ^bb0, ^bb2
    %22 = "llvm.trunc"(%21) : (i64) -> i16
    %23 = "llvm.lshr"(%21, %2) : (i64, i64) -> i64
    %24 = "llvm.and"(%23, %3) : (i64, i64) -> i64
    %25 = "llvm.getelementptr"(%arg1, %24) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %26 = "llvm.load"(%25) <{alignment = 1 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> i8
    %27 = "llvm.zext"(%26) : (i8) -> i16
    %28 = "llvm.and"(%22, %4) : (i16, i16) -> i16
    %29 = "llvm.lshr"(%27, %28) : (i16, i16) -> i16
    %30 = "llvm.and"(%29, %5) : (i16, i16) -> i16
    %31 = "llvm.getelementptr"(%arg0, %21) <{elem_type = i16, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%30, %31) <{alignment = 2 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag2]}> : (i16, !llvm.ptr) -> ()
    %32 = "llvm.add"(%21, %6) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %33 = "llvm.icmp"(%32, %7) <{predicate = 0 : i64}> : (i64, i64) -> i1
    "llvm.cond_br"(%33, %32)[^bb1, ^bb2] <{loop_annotation = #loop_annotation, operandSegmentSizes = array<i32: 1, 0, 1>}> : (i1, i64) -> ()
  ^bb3(%34: i64):  // 2 preds: ^bb1, ^bb4
    %35 = "llvm.getelementptr"(%arg0, %34) <{elem_type = i16, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %36 = "llvm.load"(%35) <{alignment = 2 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag2]}> : (!llvm.ptr) -> i16
    %37 = "llvm.icmp"(%36, %8) <{predicate = 0 : i64}> : (i16, i16) -> i1
    "llvm.cond_br"(%37)[^bb4, ^bb5] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
  ^bb4:  // pred: ^bb3
    %38 = "llvm.add"(%34, %6) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %39 = "llvm.icmp"(%38, %17) <{predicate = 0 : i64}> : (i64, i64) -> i1
    "llvm.cond_br"(%39, %38)[^bb23, ^bb3] <{loop_annotation = #loop_annotation, operandSegmentSizes = array<i32: 1, 0, 1>}> : (i1, i64) -> ()
  ^bb5:  // pred: ^bb3
    %40 = "llvm.trunc"(%34) : (i64) -> i32
    %41 = "llvm.icmp"(%40, %9) <{predicate = 2 : i64}> : (i32, i32) -> i1
    "llvm.cond_br"(%41)[^bb6, ^bb23] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
  ^bb6:  // pred: ^bb5
    %42 = "llvm.shl"(%19, %10) <{overflowFlags = #llvm.overflow<none>}> : (i32, i32) -> i32
    %43 = "llvm.ashr"(%42, %10) : (i32, i32) -> i32
    %44 = "llvm.ashr"(%42, %11) : (i32, i32) -> i32
    %45 = "llvm.sub"(%12, %43) <{overflowFlags = #llvm.overflow<nsw>}> : (i32, i32) -> i32
    "llvm.br"(%40)[^bb7] : (i32) -> ()
  ^bb7(%46: i32):  // 2 preds: ^bb6, ^bb22
    %47 = "llvm.icmp"(%46, %13) <{predicate = 2 : i64}> : (i32, i32) -> i1
    "llvm.cond_br"(%47, %7, %5)[^bb8, ^bb20] <{operandSegmentSizes = array<i32: 1, 0, 2>}> : (i1, i64, i16) -> ()
  ^bb8:  // pred: ^bb7
    %48 = "llvm.sext"(%46) : (i32) -> i64
    %49 = "llvm.add"(%46, %14) <{overflowFlags = #llvm.overflow<nsw>}> : (i32, i32) -> i32
    "llvm.br"(%49, %48, %5)[^bb9] : (i32, i64, i16) -> ()
  ^bb9(%50: i32, %51: i64, %52: i16):  // 2 preds: ^bb8, ^bb19
    %53 = "llvm.add"(%51, %6) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %54 = "llvm.getelementptr"(%arg0, %53) <{elem_type = i16, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %55 = "llvm.load"(%54) <{alignment = 2 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag2]}> : (!llvm.ptr) -> i16
    %56 = "llvm.icmp"(%55, %8) <{predicate = 0 : i64}> : (i16, i16) -> i1
    "llvm.cond_br"(%56, %52)[^bb19, ^bb10] <{operandSegmentSizes = array<i32: 1, 1, 0>}> : (i1, i16) -> ()
  ^bb10:  // pred: ^bb9
    %57 = "llvm.trunc"(%53) : (i64) -> i32
    %58 = "llvm.sub"(%57, %46) <{overflowFlags = #llvm.overflow<none>}> : (i32, i32) -> i32
    %59 = "llvm.call"(%58) <{CConv = #llvm.cconv<fastcc>, callee = @fd_int_min, fastmathFlags = #llvm.fastmath<none>}> : (i32) -> i32
    %60 = "llvm.shl"(%15, %59) <{overflowFlags = #llvm.overflow<none>}> : (i32, i32) -> i32
    %61 = "llvm.ashr"(%60, %10) : (i32, i32) -> i32
    %62 = "llvm.icmp"(%61, %44) <{predicate = 4 : i64}> : (i32, i32) -> i1
    "llvm.cond_br"(%62)[^bb21, ^bb11] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
  ^bb11:  // pred: ^bb10
    %63 = "llvm.trunc"(%61) : (i32) -> i16
    %64 = "llvm.add"(%52, %63) <{overflowFlags = #llvm.overflow<none>}> : (i16, i16) -> i16
    %65 = "llvm.sext"(%64) : (i16) -> i32
    %66 = "llvm.icmp"(%43, %65) <{predicate = 2 : i64}> : (i32, i32) -> i1
    "llvm.cond_br"(%66)[^bb13, ^bb12] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
  ^bb12:  // pred: ^bb11
    "llvm.store"(%8, %54) <{alignment = 2 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag2]}> : (i16, !llvm.ptr) -> ()
    "llvm.br"(%64)[^bb19] : (i16) -> ()
  ^bb13:  // pred: ^bb11
    %67 = "llvm.trunc"(%53) : (i64) -> i32
    %68 = "llvm.sub"(%52, %63) <{overflowFlags = #llvm.overflow<none>}> : (i16, i16) -> i16
    %69 = "llvm.sext"(%68) : (i16) -> i32
    %70 = "llvm.icmp"(%69, %45) <{predicate = 2 : i64}> : (i32, i32) -> i1
    "llvm.cond_br"(%70, %67, %52)[^bb22, ^bb14] <{operandSegmentSizes = array<i32: 1, 2, 0>}> : (i1, i32, i16) -> ()
  ^bb14:  // pred: ^bb13
    %71 = "llvm.trunc"(%51) : (i64) -> i32
    "llvm.store"(%8, %54) <{alignment = 2 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag2]}> : (i16, !llvm.ptr) -> ()
    %72 = "llvm.add"(%71, %14) <{overflowFlags = #llvm.overflow<nsw>}> : (i32, i32) -> i32
    %73 = "llvm.sext"(%72) : (i32) -> i64
    %74 = "llvm.getelementptr"(%arg0, %73) <{elem_type = i16, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %75 = "llvm.load"(%74) <{alignment = 2 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag2]}> : (!llvm.ptr) -> i16
    %76 = "llvm.icmp"(%75, %8) <{predicate = 0 : i64}> : (i16, i16) -> i1
    "llvm.cond_br"(%76, %72, %74)[^bb17, ^bb15] <{operandSegmentSizes = array<i32: 1, 2, 0>}> : (i1, i32, !llvm.ptr) -> ()
  ^bb15:  // pred: ^bb14
    %77 = "llvm.sext"(%50) : (i32) -> i64
    "llvm.br"(%77, %74)[^bb18] : (i64, !llvm.ptr) -> ()
  ^bb16:  // pred: ^bb18
    %78 = "llvm.trunc"(%83) : (i64) -> i32
    "llvm.br"(%78, %84)[^bb17] : (i32, !llvm.ptr) -> ()
  ^bb17(%79: i32, %80: !llvm.ptr):  // 2 preds: ^bb14, ^bb16
    "llvm.store"(%5, %80) <{alignment = 2 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag2]}> : (i16, !llvm.ptr) -> ()
    "llvm.br"(%79, %68)[^bb22] : (i32, i16) -> ()
  ^bb18(%81: i64, %82: !llvm.ptr):  // 2 preds: ^bb15, ^bb18
    "llvm.store"(%8, %82) <{alignment = 2 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag2]}> : (i16, !llvm.ptr) -> ()
    %83 = "llvm.add"(%81, %6) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %84 = "llvm.getelementptr"(%arg0, %83) <{elem_type = i16, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %85 = "llvm.load"(%84) <{alignment = 2 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag2]}> : (!llvm.ptr) -> i16
    %86 = "llvm.icmp"(%85, %8) <{predicate = 0 : i64}> : (i16, i16) -> i1
    "llvm.cond_br"(%86, %83, %84)[^bb16, ^bb18] <{loop_annotation = #loop_annotation1, operandSegmentSizes = array<i32: 1, 0, 2>}> : (i1, i64, !llvm.ptr) -> ()
  ^bb19(%87: i16):  // 2 preds: ^bb9, ^bb12
    %88 = "llvm.icmp"(%53, %7) <{predicate = 0 : i64}> : (i64, i64) -> i1
    %89 = "llvm.add"(%50, %16) <{overflowFlags = #llvm.overflow<none>}> : (i32, i32) -> i32
    "llvm.cond_br"(%88, %48, %87, %89, %53, %87)[^bb20, ^bb9] <{operandSegmentSizes = array<i32: 1, 2, 3>}> : (i1, i64, i16, i32, i64, i16) -> ()
  ^bb20(%90: i64, %91: i16):  // 2 preds: ^bb7, ^bb19
    %92 = "llvm.getelementptr"(%arg0, %90) <{elem_type = i16, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%91, %92) <{alignment = 2 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag2]}> : (i16, !llvm.ptr) -> ()
    "llvm.br"()[^bb23] : () -> ()
  ^bb21:  // pred: ^bb10
    %93 = "llvm.trunc"(%53) : (i64) -> i32
    "llvm.br"(%93, %52)[^bb22] : (i32, i16) -> ()
  ^bb22(%94: i32, %95: i16):  // 3 preds: ^bb13, ^bb17, ^bb21
    %96 = "llvm.getelementptr"(%arg0, %48) <{elem_type = i16, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%95, %96) <{alignment = 2 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag2]}> : (i16, !llvm.ptr) -> ()
    %97 = "llvm.icmp"(%94, %9) <{predicate = 2 : i64}> : (i32, i32) -> i1
    "llvm.cond_br"(%97, %94)[^bb7, ^bb23] <{loop_annotation = #loop_annotation, operandSegmentSizes = array<i32: 1, 1, 0>}> : (i1, i32) -> ()
  ^bb23:  // 4 preds: ^bb4, ^bb5, ^bb20, ^bb22
    "llvm.return"() : () -> ()
}
]

def fd_curve25519_scalar_wnaf :
    Cfg (Ctxt.ofList [SLLVM.Ty.bitvec 32, SLLVM.Ty.ptr, SLLVM.Ty.ptr]) [] :=
  [sllvm_cfg_of| fd_curve25519_scalar_wnaf_region with
    @fd_int_min := fd_int_min]

end Firedancer.Common
