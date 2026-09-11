/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
-- build/native/gcc/mlir_canonicalized/{ref,avx512}/region/fd_curve25519_scalar_validate.mlir
import SSA.Projects.SLLVM.Cfg
import SSA.Projects.Firedancer.Common.Mlir.fd_ulong_load_8

namespace Firedancer.Common
open LeanMLIR SLLVM

def fd_curve25519_scalar_validate_region : MLIR.AST.Region 0 := [mlir_region|
{
  ^bb0(%arg0: !llvm.ptr):
    %0 = "llvm.mlir.constant"() <{value = 1152921504606846976 : i64}> : () -> i64
    %1 = "llvm.mlir.constant"() <{value = 1152921504606846977 : i64}> : () -> i64
    %2 = "llvm.mlir.constant"() <{value = 0 : i64}> : () -> i64
    %3 = "llvm.mlir.constant"() <{value = 1503914060200516822 : i64}> : () -> i64
    %4 = "llvm.mlir.constant"() <{value = 1503914060200516823 : i64}> : () -> i64
    %5 = "llvm.mlir.constant"() <{value = 6346243789798364141 : i64}> : () -> i64
    %6 = "llvm.mlir.constant"() <{value = 16 : i8}> : () -> i8
    %7 = "llvm.mlir.constant"() <{value = 32 : i8}> : () -> i8
    %8 = "llvm.mlir.zero"() : () -> !llvm.ptr
    %9 = "llvm.getelementptr"(%arg0) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: 31>}> : (!llvm.ptr) -> !llvm.ptr
    %10 = "llvm.load"(%9) <{alignment = 1 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> i8
    %11 = "llvm.icmp"(%10, %6) <{predicate = 6 : i64}> : (i8, i8) -> i1
    "llvm.cond_br"(%11, %arg0)[^bb3, ^bb1] <{branch_weights = array<i32: 2000, 1>, operandSegmentSizes = array<i32: 1, 1, 0>}> : (i1, !llvm.ptr) -> ()
  ^bb1:  // pred: ^bb0
    %12 = "llvm.icmp"(%10, %7) <{predicate = 6 : i64}> : (i8, i8) -> i1
    "llvm.cond_br"(%12, %8)[^bb2, ^bb3] <{branch_weights = array<i32: 1, 2000>, operandSegmentSizes = array<i32: 1, 0, 1>}> : (i1, !llvm.ptr) -> ()
  ^bb2:  // pred: ^bb1
    %13 = "llvm.call"(%arg0) <{CConv = #llvm.cconv<fastcc>, callee = @fd_ulong_load_8, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr) -> i64
    %14 = "llvm.getelementptr"(%arg0) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: 8>}> : (!llvm.ptr) -> !llvm.ptr
    %15 = "llvm.call"(%14) <{CConv = #llvm.cconv<fastcc>, callee = @fd_ulong_load_8, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr) -> i64
    %16 = "llvm.getelementptr"(%arg0) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: 16>}> : (!llvm.ptr) -> !llvm.ptr
    %17 = "llvm.call"(%16) <{CConv = #llvm.cconv<fastcc>, callee = @fd_ulong_load_8, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr) -> i64
    %18 = "llvm.getelementptr"(%arg0) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: 24>}> : (!llvm.ptr) -> !llvm.ptr
    %19 = "llvm.call"(%18) <{CConv = #llvm.cconv<fastcc>, callee = @fd_ulong_load_8, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr) -> i64
    %20 = "llvm.icmp"(%13, %5) <{predicate = 6 : i64}> : (i64, i64) -> i1
    %21 = "llvm.select"(%20, %4, %3) <{fastmathFlags = #llvm.fastmath<none>}> : (i1, i64, i64) -> i64
    %22 = "llvm.icmp"(%21, %15) <{predicate = 8 : i64}> : (i64, i64) -> i1
    %23 = "llvm.icmp"(%17, %2) <{predicate = 0 : i64}> : (i64, i64) -> i1
    %24 = "llvm.and"(%23, %22) : (i1, i1) -> i1
    %25 = "llvm.select"(%24, %1, %0) <{fastmathFlags = #llvm.fastmath<none>}> : (i1, i64, i64) -> i64
    %26 = "llvm.icmp"(%25, %19) <{predicate = 8 : i64}> : (i64, i64) -> i1
    %27 = "llvm.select"(%26, %arg0, %8) <{fastmathFlags = #llvm.fastmath<none>}> : (i1, !llvm.ptr, !llvm.ptr) -> !llvm.ptr
    "llvm.br"(%27)[^bb3] : (!llvm.ptr) -> ()
  ^bb3(%28: !llvm.ptr):  // 3 preds: ^bb0, ^bb1, ^bb2
    "llvm.return"(%28) : (!llvm.ptr) -> ()
}
]

def fd_curve25519_scalar_validate : Cfg (Ctxt.ofList [SLLVM.Ty.ptr]) [SLLVM.Ty.ptr] :=
  [sllvm_cfg_of| fd_curve25519_scalar_validate_region with
    @fd_ulong_load_8 := fd_ulong_load_8]

end Firedancer.Common
