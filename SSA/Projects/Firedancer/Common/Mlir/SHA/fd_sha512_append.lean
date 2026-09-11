/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.SLLVM.Cfg
import SSA.Projects.Firedancer.Common.Mlir.SHA.fd_memcpy
import SSA.Projects.Firedancer.Common.Mlir.SHA.fd_sha512_core_ref

/-!
# `fd_sha512_append` (common)

Byte-identical (modulo indentation) to
`build/native/gcc/mlir/{ref,avx512}/region/fd_sha512_append.mlir`. The two
backends emit the same file, so the function is lifted once, here.

`fd_sha512.c`: buffer `sz` bytes, compressing whole blocks as they fill.
Eleven blocks, all forward -- the loop over whole blocks lives in
`fd_sha512_core_ref`, not here.
-/

namespace Firedancer.Common
open LeanMLIR SLLVM

set_option maxRecDepth 100000 in
def fd_sha512_append_region : MLIR.AST.Region 0 := [mlir_region|
{
  ^bb0(%arg0: !llvm.ptr, %arg1: !llvm.ptr, %arg2: i64):
    %0 = "llvm.mlir.constant"() <{value = 0 : i64}> : () -> i64
    %1 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %2 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %3 = "llvm.mlir.constant"() <{value = 4 : i32}> : () -> i32
    %4 = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
    %5 = "llvm.mlir.constant"() <{value = 3 : i64}> : () -> i64
    %6 = "llvm.mlir.constant"() <{value = 61 : i64}> : () -> i64
    %7 = "llvm.mlir.constant"() <{value = 128 : i64}> : () -> i64
    %8 = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %9 = "llvm.mlir.constant"() <{value = 7 : i64}> : () -> i64
    %10 = "llvm.mlir.constant"() <{value = 127 : i64}> : () -> i64
    %11 = "llvm.mlir.constant"() <{value = -128 : i64}> : () -> i64
    %12 = "llvm.icmp"(%arg2, %0) <{predicate = 0 : i64}> : (i64, i64) -> i1
    "llvm.cond_br"(%12)[^bb10, ^bb1] <{branch_weights = array<i32: 1, 2000>, operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
  ^bb1:  // pred: ^bb0
    %13 = "llvm.getelementptr"(%arg0, %0) <{elem_type = !llvm.struct<"struct.fd_sha512_private", (array<128 x i8>, array<8 x i64>, i64, i64, i64, i64, array<32 x i8>)>, inbounds, rawConstantIndices = array<i32: -2147483648, 1>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %14 = "llvm.getelementptr"(%arg0, %0) <{elem_type = !llvm.struct<"struct.fd_sha512_private", (array<128 x i8>, array<8 x i64>, i64, i64, i64, i64, array<32 x i8>)>, inbounds, rawConstantIndices = array<i32: -2147483648, 3>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %15 = "llvm.load"(%14) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag2]}> : (!llvm.ptr) -> i64
    %16 = "llvm.getelementptr"(%arg0, %0) <{elem_type = !llvm.struct<"struct.fd_sha512_private", (array<128 x i8>, array<8 x i64>, i64, i64, i64, i64, array<32 x i8>)>, inbounds, rawConstantIndices = array<i32: -2147483648, 4>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %17 = "llvm.load"(%16) <{alignment = 16 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag3]}> : (!llvm.ptr) -> i64
    %18 = "llvm.getelementptr"(%arg0, %0) <{elem_type = !llvm.struct<"struct.fd_sha512_private", (array<128 x i8>, array<8 x i64>, i64, i64, i64, i64, array<32 x i8>)>, inbounds, rawConstantIndices = array<i32: -2147483648, 5>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %19 = "llvm.load"(%18) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag4]}> : (!llvm.ptr) -> i64
    %20 = "llvm.shl"(%arg2, %5) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %21 = "llvm.add"(%17, %20) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %22 = "llvm.lshr"(%arg2, %6) : (i64, i64) -> i64
    %23 = "llvm.add"(%19, %22) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %24 = "llvm.icmp"(%21, %17) <{predicate = 6 : i64}> : (i64, i64) -> i1
    %25 = "llvm.zext"(%24) : (i1) -> i64
    %26 = "llvm.add"(%23, %25) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    "llvm.store"(%21, %16) <{alignment = 16 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag3]}> : (i64, !llvm.ptr) -> ()
    "llvm.store"(%26, %18) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag4]}> : (i64, !llvm.ptr) -> ()
    %27 = "llvm.icmp"(%15, %0) <{predicate = 0 : i64}> : (i64, i64) -> i1
    "llvm.cond_br"(%27, %arg1, %arg2)[^bb5, ^bb2] <{branch_weights = array<i32: 2000, 1>, operandSegmentSizes = array<i32: 1, 2, 0>}> : (i1, !llvm.ptr, i64) -> ()
  ^bb2:  // pred: ^bb1
    %28 = "llvm.sub"(%7, %15) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %29 = "llvm.icmp"(%28, %arg2) <{predicate = 8 : i64}> : (i64, i64) -> i1
    %30 = "llvm.getelementptr"(%arg0, %15) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.cond_br"(%29)[^bb3, ^bb4] <{branch_weights = array<i32: 1, 2000>, operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
  ^bb3:  // pred: ^bb2
    %31 = "llvm.call"(%30, %arg1, %arg2) <{CConv = #llvm.cconv<fastcc>, callee = @fd_memcpy, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr, i64) -> !llvm.ptr
    %32 = "llvm.add"(%15, %arg2) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    "llvm.br"(%32)[^bb9] : (i64) -> ()
  ^bb4:  // pred: ^bb2
    %33 = "llvm.call"(%30, %arg1, %28) <{CConv = #llvm.cconv<fastcc>, callee = @fd_memcpy, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr, i64) -> !llvm.ptr
    %34 = "llvm.getelementptr"(%arg1, %28) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %35 = "llvm.sub"(%arg2, %28) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    "llvm.call"(%13, %arg0, %8) <{CConv = #llvm.cconv<fastcc>, callee = @fd_sha512_core_ref, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr, i64) -> ()
    "llvm.store"(%0, %14) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag2]}> : (i64, !llvm.ptr) -> ()
    "llvm.br"(%34, %35)[^bb5] : (!llvm.ptr, i64) -> ()
  ^bb5(%36: !llvm.ptr, %37: i64):  // 2 preds: ^bb1, ^bb4
    %38 = "llvm.icmp"(%37, %7) <{predicate = 6 : i64}> : (i64, i64) -> i1
    "llvm.cond_br"(%38)[^bb7, ^bb6] <{branch_weights = array<i32: 1, 2000>, operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
  ^bb6:  // pred: ^bb5
    %39 = "llvm.lshr"(%37, %9) : (i64, i64) -> i64
    "llvm.call"(%13, %36, %39) <{CConv = #llvm.cconv<fastcc>, callee = @fd_sha512_core_ref, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr, i64) -> ()
    "llvm.br"()[^bb7] : () -> ()
  ^bb7:  // 2 preds: ^bb5, ^bb6
    %40 = "llvm.and"(%37, %10) : (i64, i64) -> i64
    %41 = "llvm.icmp"(%40, %0) <{predicate = 0 : i64}> : (i64, i64) -> i1
    "llvm.cond_br"(%41)[^bb10, ^bb8] <{branch_weights = array<i32: 2000, 1>, operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
  ^bb8:  // pred: ^bb7
    %42 = "llvm.and"(%37, %11) : (i64, i64) -> i64
    %43 = "llvm.getelementptr"(%36, %42) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %44 = "llvm.call"(%arg0, %43, %40) <{CConv = #llvm.cconv<fastcc>, callee = @fd_memcpy, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr, i64) -> !llvm.ptr
    "llvm.br"(%40)[^bb9] : (i64) -> ()
  ^bb9(%45: i64):  // 2 preds: ^bb3, ^bb8
    "llvm.store"(%45, %14) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag2]}> : (i64, !llvm.ptr) -> ()
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
