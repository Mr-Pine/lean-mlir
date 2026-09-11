/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
-- build/native/gcc/mlir_canonicalized/avx512/region/fd_ed25519_point_sub_with_opts.mlir
import SSA.Projects.SLLVM.Cfg
import SSA.Projects.Firedancer.Avx512.Mlir.Point.fd_ed25519_point_neg
import SSA.Projects.Firedancer.Avx512.Mlir.Point.fd_ed25519_point_neg_precomputed
import SSA.Projects.Firedancer.Avx512.Mlir.Point.fd_ed25519_point_add_with_opts

namespace Firedancer.Avx512
open LeanMLIR SLLVM

def fd_ed25519_point_sub_with_opts_region : MLIR.AST.Region 0 := [mlir_region|
{
  ^bb0(%arg0: !llvm.ptr, %arg1: !llvm.ptr, %arg2: !llvm.ptr, %arg3: i32):
    %0 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %1 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %2 = "llvm.alloca"(%0) <{alignment = 64 : i64, elem_type = !llvm.array<1 x struct<"struct.fd_curve25519_edwards", (vector<8xi64>, vector<8xi64>, vector<8xi64>)>>}> : (i32) -> !llvm.ptr
    "llvm.intr.lifetime.start"(%2) <{size = 192 : i64}> : (!llvm.ptr) -> ()
    %3 = "llvm.icmp"(%arg3, %1) <{predicate = 0 : i64}> : (i32, i32) -> i1
    "llvm.cond_br"(%3)[^bb2, ^bb1] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
  ^bb1:  // pred: ^bb0
    %4 = "llvm.call"(%2, %arg2) <{CConv = #llvm.cconv<fastcc>, callee = @fd_ed25519_point_neg_precomputed, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr) -> !llvm.ptr
    "llvm.br"()[^bb3] : () -> ()
  ^bb2:  // pred: ^bb0
    %5 = "llvm.call"(%2, %arg2) <{CConv = #llvm.cconv<fastcc>, callee = @fd_ed25519_point_neg, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr) -> !llvm.ptr
    "llvm.br"()[^bb3] : () -> ()
  ^bb3:  // 2 preds: ^bb1, ^bb2
    %6 = "llvm.call"(%arg0, %arg1, %2, %arg3) <{CConv = #llvm.cconv<fastcc>, callee = @fd_ed25519_point_add_with_opts, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr, !llvm.ptr, i32) -> !llvm.ptr
    "llvm.intr.lifetime.end"(%2) <{size = 192 : i64}> : (!llvm.ptr) -> ()
    "llvm.return"(%arg0) : (!llvm.ptr) -> ()
}
]

def fd_ed25519_point_sub_with_opts :
    Cfg (Ctxt.ofList [SLLVM.Ty.bitvec 32, SLLVM.Ty.ptr, SLLVM.Ty.ptr, SLLVM.Ty.ptr]) [SLLVM.Ty.ptr] :=
  [sllvm_cfg_of| fd_ed25519_point_sub_with_opts_region with
    @fd_ed25519_point_neg_precomputed := fd_ed25519_point_neg_precomputed,
    @fd_ed25519_point_neg := fd_ed25519_point_neg,
    @fd_ed25519_point_add_with_opts := fd_ed25519_point_add_with_opts]

end Firedancer.Avx512
