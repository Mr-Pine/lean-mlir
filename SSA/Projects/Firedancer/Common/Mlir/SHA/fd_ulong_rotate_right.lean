/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.SLLVM.Cfg

/-!
# `fd_ulong_rotate_right` (common)

Byte-identical (modulo indentation) to
`build/native/gcc/mlir/{ref,avx512}/region/fd_ulong_rotate_right.mlir`. The two
backends emit the same file, so the function is lifted once, here.

`fd_bits.h`: rotate a `ulong` right by `n`, compiled to `fshr x x n`.
The shift amount arrives as an `i32` and is zero-extended.
-/

namespace Firedancer.Common
open LeanMLIR SLLVM

set_option maxRecDepth 100000 in
def fd_ulong_rotate_right_region : MLIR.AST.Region 0 := [mlir_region|
{
  ^bb0(%arg0: i64, %arg1: i32):
    %0 = "llvm.zext"(%arg1) : (i32) -> i64
    %1 = "llvm.intr.fshr"(%arg0, %arg0, %0) : (i64, i64, i64) -> i64
    "llvm.return"(%1) : (i64) -> ()
}
]

set_option maxRecDepth 100000 in
def fd_ulong_rotate_right : Cfg (Ctxt.ofList [SLLVM.Ty.bitvec 32, SLLVM.Ty.bitvec 64]) [SLLVM.Ty.bitvec 64] :=
  [sllvm_cfg_of| fd_ulong_rotate_right_region]

end Firedancer.Common
