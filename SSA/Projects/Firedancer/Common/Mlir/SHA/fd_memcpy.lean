/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.SLLVM.Cfg

/-!
# `fd_memcpy` (common)

Byte-identical (modulo indentation) to
`build/native/gcc/mlir/{ref,avx512}/region/fd_memcpy.mlir`. The two
backends emit the same file, so the function is lifted once, here.

`fd_memcpy(d, s, sz)`: the intrinsic, returning `d`.
-/

namespace Firedancer.Common
open LeanMLIR SLLVM

set_option maxRecDepth 100000 in
def fd_memcpy_region : MLIR.AST.Region 0 := [mlir_region|
{
  ^bb0(%arg0: !llvm.ptr, %arg1: !llvm.ptr, %arg2: i64):
    "llvm.intr.memcpy"(%arg0, %arg1, %arg2) <{isVolatile = false}> : (!llvm.ptr, !llvm.ptr, i64) -> ()
    "llvm.return"(%arg0) : (!llvm.ptr) -> ()
}
]

set_option maxRecDepth 100000 in
def fd_memcpy : Cfg (Ctxt.ofList [SLLVM.Ty.bitvec 64, SLLVM.Ty.ptr, SLLVM.Ty.ptr]) [SLLVM.Ty.ptr] :=
  [sllvm_cfg_of| fd_memcpy_region]

end Firedancer.Common
