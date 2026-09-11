/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.SLLVM.Cfg
import SSA.Projects.Firedancer.Common.Mlir.fd_ulong_load_8

/-!
# `fd_curve25519_scalar_validate` (common)

Byte-identical (modulo indentation) to
`build/native/gcc/mlir/{ref,avx512}/region/fd_curve25519_scalar_validate.mlir`.
The two backends' regions are the same file, as is the one callee
`fd_ulong_load_8`, so the function is lifted once, here.

`fd_curve25519_scalar.h`: return `s` if the 32-byte scalar is below the group
order `l = 2^252 + 27742317777372353535851937790883648493`, else `NULL`. The
top byte decides most cases (`< 0x10` accept, `≥ 0x20` reject); in between the
four little-endian `ulong`s are compared against `l`'s.
-/

namespace Firedancer.Common
open LeanMLIR SLLVM

def fd_curve25519_scalar_validate_region : MLIR.AST.Region 0 := [mlir_region|
{
  ^bb0(%arg0: !llvm.ptr):
    %0 = "llvm.mlir.constant"() <{value = 31 : i64}> : () -> i64
    %1 = "llvm.mlir.constant"() <{value = 16 : i8}> : () -> i8
    %2 = "llvm.mlir.constant"() <{value = 32 : i8}> : () -> i8
    %3 = "llvm.mlir.zero"() : () -> !llvm.ptr
    %4 = "llvm.mlir.constant"() <{value = 8 : i64}> : () -> i64
    %5 = "llvm.mlir.constant"() <{value = 16 : i64}> : () -> i64
    %6 = "llvm.mlir.constant"() <{value = 24 : i64}> : () -> i64
    %7 = "llvm.mlir.constant"() <{value = 6346243789798364141 : i64}> : () -> i64
    %8 = "llvm.mlir.constant"() <{value = 1503914060200516823 : i64}> : () -> i64
    %9 = "llvm.mlir.constant"() <{value = 1503914060200516822 : i64}> : () -> i64
    %10 = "llvm.mlir.constant"() <{value = 0 : i64}> : () -> i64
    %11 = "llvm.mlir.constant"() <{value = 1152921504606846977 : i64}> : () -> i64
    %12 = "llvm.mlir.constant"() <{value = 1152921504606846976 : i64}> : () -> i64
    %13 = "llvm.getelementptr"(%arg0, %0) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %14 = "llvm.load"(%13) <{alignment = 1 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> i8
    %15 = "llvm.icmp"(%14, %1) <{predicate = 6 : i64}> : (i8, i8) -> i1
    "llvm.cond_br"(%15, %arg0)[^bb3, ^bb1] <{branch_weights = array<i32: 2000, 1>, operandSegmentSizes = array<i32: 1, 1, 0>}> : (i1, !llvm.ptr) -> ()
  ^bb1:  // pred: ^bb0
    %16 = "llvm.icmp"(%14, %2) <{predicate = 6 : i64}> : (i8, i8) -> i1
    "llvm.cond_br"(%16, %3)[^bb2, ^bb3] <{branch_weights = array<i32: 1, 2000>, operandSegmentSizes = array<i32: 1, 0, 1>}> : (i1, !llvm.ptr) -> ()
  ^bb2:  // pred: ^bb1
    %17 = "llvm.call"(%arg0) <{CConv = #llvm.cconv<fastcc>, callee = @fd_ulong_load_8, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr) -> i64
    %18 = "llvm.getelementptr"(%arg0, %4) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %19 = "llvm.call"(%18) <{CConv = #llvm.cconv<fastcc>, callee = @fd_ulong_load_8, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr) -> i64
    %20 = "llvm.getelementptr"(%arg0, %5) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %21 = "llvm.call"(%20) <{CConv = #llvm.cconv<fastcc>, callee = @fd_ulong_load_8, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr) -> i64
    %22 = "llvm.getelementptr"(%arg0, %6) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %23 = "llvm.call"(%22) <{CConv = #llvm.cconv<fastcc>, callee = @fd_ulong_load_8, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr) -> i64
    %24 = "llvm.icmp"(%17, %7) <{predicate = 6 : i64}> : (i64, i64) -> i1
    %25 = "llvm.select"(%24, %8, %9) <{fastmathFlags = #llvm.fastmath<none>}> : (i1, i64, i64) -> i64
    %26 = "llvm.icmp"(%25, %19) <{predicate = 8 : i64}> : (i64, i64) -> i1
    %27 = "llvm.icmp"(%21, %10) <{predicate = 0 : i64}> : (i64, i64) -> i1
    %28 = "llvm.and"(%27, %26) : (i1, i1) -> i1
    %29 = "llvm.select"(%28, %11, %12) <{fastmathFlags = #llvm.fastmath<none>}> : (i1, i64, i64) -> i64
    %30 = "llvm.icmp"(%29, %23) <{predicate = 8 : i64}> : (i64, i64) -> i1
    %31 = "llvm.select"(%30, %arg0, %3) <{fastmathFlags = #llvm.fastmath<none>}> : (i1, !llvm.ptr, !llvm.ptr) -> !llvm.ptr
    "llvm.br"(%31)[^bb3] : (!llvm.ptr) -> ()
  ^bb3(%32: !llvm.ptr):  // 3 preds: ^bb0, ^bb1, ^bb2
    "llvm.return"(%32) : (!llvm.ptr) -> ()
}
]

def fd_curve25519_scalar_validate : Cfg (Ctxt.ofList [SLLVM.Ty.ptr]) [SLLVM.Ty.ptr] :=
  [sllvm_cfg_of| fd_curve25519_scalar_validate_region with
    @fd_ulong_load_8 := fd_ulong_load_8]

end Firedancer.Common
