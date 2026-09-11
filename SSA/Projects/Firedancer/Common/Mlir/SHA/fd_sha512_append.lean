/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
-- build/native/gcc/mlir_canonicalized/{ref,avx512}/region/fd_sha512_append.mlir
import SSA.Projects.SLLVM.Cfg
import SSA.Projects.Firedancer.Common.Mlir.SHA.fd_memcpy
import SSA.Projects.Firedancer.Common.Mlir.SHA.fd_sha512_core_ref

namespace Firedancer.Common
open LeanMLIR SLLVM

set_option maxRecDepth 100000 in
def fd_sha512_append_region : MLIR.AST.Region 0 := [mlir_region|
{
  ^bb0(%arg0: !llvm.ptr, %arg1: !llvm.ptr, %arg2: i64):
    %0 = "llvm.mlir.constant"() <{value = 0 : i64}> : () -> i64
    %1 = "llvm.mlir.constant"() <{value = 3 : i64}> : () -> i64
    %2 = "llvm.mlir.constant"() <{value = 61 : i64}> : () -> i64
    %3 = "llvm.mlir.constant"() <{value = 128 : i64}> : () -> i64
    %4 = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %5 = "llvm.mlir.constant"() <{value = 7 : i64}> : () -> i64
    %6 = "llvm.mlir.constant"() <{value = 127 : i64}> : () -> i64
    %7 = "llvm.mlir.constant"() <{value = -128 : i64}> : () -> i64
    %8 = "llvm.icmp"(%arg2, %0) <{predicate = 0 : i64}> : (i64, i64) -> i1
    "llvm.cond_br"(%8)[^bb10, ^bb1] <{branch_weights = array<i32: 1, 2000>, operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
  ^bb1:  // pred: ^bb0
    %9 = "llvm.getelementptr"(%arg0) <{elem_type = !llvm.struct<"struct.fd_sha512_private", (array<128 x i8>, array<8 x i64>, i64, i64, i64, i64, array<32 x i8>)>, inbounds, rawConstantIndices = array<i32: 0, 1>}> : (!llvm.ptr) -> !llvm.ptr
    %10 = "llvm.getelementptr"(%arg0) <{elem_type = !llvm.struct<"struct.fd_sha512_private", (array<128 x i8>, array<8 x i64>, i64, i64, i64, i64, array<32 x i8>)>, inbounds, rawConstantIndices = array<i32: 0, 3>}> : (!llvm.ptr) -> !llvm.ptr
    %11 = "llvm.load"(%10) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag3]}> : (!llvm.ptr) -> i64
    %12 = "llvm.getelementptr"(%arg0) <{elem_type = !llvm.struct<"struct.fd_sha512_private", (array<128 x i8>, array<8 x i64>, i64, i64, i64, i64, array<32 x i8>)>, inbounds, rawConstantIndices = array<i32: 0, 4>}> : (!llvm.ptr) -> !llvm.ptr
    %13 = "llvm.load"(%12) <{alignment = 16 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag4]}> : (!llvm.ptr) -> i64
    %14 = "llvm.getelementptr"(%arg0) <{elem_type = !llvm.struct<"struct.fd_sha512_private", (array<128 x i8>, array<8 x i64>, i64, i64, i64, i64, array<32 x i8>)>, inbounds, rawConstantIndices = array<i32: 0, 5>}> : (!llvm.ptr) -> !llvm.ptr
    %15 = "llvm.load"(%14) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag5]}> : (!llvm.ptr) -> i64
    %16 = "llvm.shl"(%arg2, %1) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %17 = "llvm.add"(%13, %16) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %18 = "llvm.lshr"(%arg2, %2) : (i64, i64) -> i64
    %19 = "llvm.add"(%15, %18) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %20 = "llvm.icmp"(%17, %13) <{predicate = 6 : i64}> : (i64, i64) -> i1
    %21 = "llvm.zext"(%20) : (i1) -> i64
    %22 = "llvm.add"(%19, %21) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    "llvm.store"(%17, %12) <{alignment = 16 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag4]}> : (i64, !llvm.ptr) -> ()
    "llvm.store"(%22, %14) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag5]}> : (i64, !llvm.ptr) -> ()
    %23 = "llvm.icmp"(%11, %0) <{predicate = 0 : i64}> : (i64, i64) -> i1
    "llvm.cond_br"(%23, %arg1, %arg2)[^bb5, ^bb2] <{branch_weights = array<i32: 2000, 1>, operandSegmentSizes = array<i32: 1, 2, 0>}> : (i1, !llvm.ptr, i64) -> ()
  ^bb2:  // pred: ^bb1
    %24 = "llvm.sub"(%3, %11) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %25 = "llvm.icmp"(%24, %arg2) <{predicate = 8 : i64}> : (i64, i64) -> i1
    %26 = "llvm.getelementptr"(%arg0, %11) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.cond_br"(%25)[^bb3, ^bb4] <{branch_weights = array<i32: 1, 2000>, operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
  ^bb3:  // pred: ^bb2
    %27 = "llvm.call"(%26, %arg1, %arg2) <{CConv = #llvm.cconv<fastcc>, callee = @fd_memcpy, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr, i64) -> !llvm.ptr
    %28 = "llvm.add"(%11, %arg2) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    "llvm.br"(%28)[^bb9] : (i64) -> ()
  ^bb4:  // pred: ^bb2
    %29 = "llvm.call"(%26, %arg1, %24) <{CConv = #llvm.cconv<fastcc>, callee = @fd_memcpy, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr, i64) -> !llvm.ptr
    %30 = "llvm.getelementptr"(%arg1, %24) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %31 = "llvm.sub"(%arg2, %24) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    "llvm.call"(%9, %arg0, %4) <{CConv = #llvm.cconv<fastcc>, callee = @fd_sha512_core_ref, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr, i64) -> ()
    "llvm.store"(%0, %10) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag3]}> : (i64, !llvm.ptr) -> ()
    "llvm.br"(%30, %31)[^bb5] : (!llvm.ptr, i64) -> ()
  ^bb5(%32: !llvm.ptr, %33: i64):  // 2 preds: ^bb1, ^bb4
    %34 = "llvm.icmp"(%33, %3) <{predicate = 6 : i64}> : (i64, i64) -> i1
    "llvm.cond_br"(%34)[^bb7, ^bb6] <{branch_weights = array<i32: 1, 2000>, operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
  ^bb6:  // pred: ^bb5
    %35 = "llvm.lshr"(%33, %5) : (i64, i64) -> i64
    "llvm.call"(%9, %32, %35) <{CConv = #llvm.cconv<fastcc>, callee = @fd_sha512_core_ref, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr, i64) -> ()
    "llvm.br"()[^bb7] : () -> ()
  ^bb7:  // 2 preds: ^bb5, ^bb6
    %36 = "llvm.and"(%33, %6) : (i64, i64) -> i64
    %37 = "llvm.icmp"(%36, %0) <{predicate = 0 : i64}> : (i64, i64) -> i1
    "llvm.cond_br"(%37)[^bb10, ^bb8] <{branch_weights = array<i32: 2000, 1>, operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
  ^bb8:  // pred: ^bb7
    %38 = "llvm.and"(%33, %7) : (i64, i64) -> i64
    %39 = "llvm.getelementptr"(%32, %38) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %40 = "llvm.call"(%arg0, %39, %36) <{CConv = #llvm.cconv<fastcc>, callee = @fd_memcpy, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr, i64) -> !llvm.ptr
    "llvm.br"(%36)[^bb9] : (i64) -> ()
  ^bb9(%41: i64):  // 2 preds: ^bb3, ^bb8
    "llvm.store"(%41, %10) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag3]}> : (i64, !llvm.ptr) -> ()
    "llvm.br"()[^bb10] : () -> ()
  ^bb10:  // 3 preds: ^bb0, ^bb7, ^bb9
    "llvm.return"(%arg0) : (!llvm.ptr) -> ()
}
]

set_option maxRecDepth 100000 in
def fd_sha512_append : Cfg (Ctxt.ofList [SLLVM.Ty.bitvec 64, SLLVM.Ty.ptr, SLLVM.Ty.ptr]) [SLLVM.Ty.ptr] :=
  [sllvm_cfg_of| fd_sha512_append_region with
    @fd_memcpy := fd_memcpy,
    @fd_sha512_core_ref := fd_sha512_core_ref]

end Firedancer.Common
