/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.SLLVM.Cfg
import SSA.Projects.Firedancer.Ref.Mlir.Point.fd_ed25519_point_frombytes

/-!
# `fd_ed25519_point_frombytes_2x` (ref)

Byte-identical (modulo indentation) to
`build/native/gcc/mlir/ref/region/fd_ed25519_point_frombytes_2x.mlir`: two
decompressions, short-circuiting on the first failure.
-/

namespace Firedancer.Ref
open LeanMLIR SLLVM

def fd_ed25519_point_frombytes_2x_region : MLIR.AST.Region 0 := [mlir_region|
{
  ^bb0(%arg0: !llvm.ptr, %arg1: !llvm.ptr, %arg2: !llvm.ptr, %arg3: !llvm.ptr):
    %0 = "llvm.mlir.zero"() : () -> !llvm.ptr
    %1 = "llvm.mlir.constant"() <{value = -1 : i32}> : () -> i32
    %2 = "llvm.mlir.constant"() <{value = -2 : i32}> : () -> i32
    %3 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %4 = "llvm.call"(%arg0, %arg1) <{CConv = #llvm.cconv<ccc>, callee = @fd_ed25519_point_frombytes, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr) -> !llvm.ptr
    %5 = "llvm.icmp"(%4, %0) <{predicate = 0 : i64}> : (!llvm.ptr, !llvm.ptr) -> i1
    "llvm.cond_br"(%5, %1)[^bb2, ^bb1] <{operandSegmentSizes = array<i32: 1, 1, 0>}> : (i1, i32) -> ()
  ^bb1:  // pred: ^bb0
    %6 = "llvm.call"(%arg2, %arg3) <{CConv = #llvm.cconv<ccc>, callee = @fd_ed25519_point_frombytes, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr) -> !llvm.ptr
    %7 = "llvm.icmp"(%6, %0) <{predicate = 0 : i64}> : (!llvm.ptr, !llvm.ptr) -> i1
    %8 = "llvm.select"(%7, %2, %3) <{fastmathFlags = #llvm.fastmath<none>}> : (i1, i32, i32) -> i32
    "llvm.br"(%8)[^bb2] : (i32) -> ()
  ^bb2(%9: i32):  // 2 preds: ^bb0, ^bb1
    "llvm.return"(%9) : (i32) -> ()
}
]

def fd_ed25519_point_frombytes_2x :
    Cfg (Ctxt.ofList [SLLVM.Ty.ptr, SLLVM.Ty.ptr, SLLVM.Ty.ptr, SLLVM.Ty.ptr]) [SLLVM.Ty.bitvec 32] :=
  [sllvm_cfg_of| fd_ed25519_point_frombytes_2x_region with
    @fd_ed25519_point_frombytes := fd_ed25519_point_frombytes]

end Firedancer.Ref
