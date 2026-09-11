/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.SLLVM.Cfg

/-!
# `fd_memset` (common)

Byte-identical (modulo indentation) to
`build/native/gcc/mlir/{ref,avx512}/region/fd_memset.mlir`. The two
backends emit the same file, so the function is lifted once, here.

`fd_memset(d, 0, sz)` as SHA-512 uses it: the fill byte is a constant `0`,
so the wrapper takes only the destination and the size.
-/

namespace Firedancer.Common
open LeanMLIR SLLVM

set_option maxRecDepth 100000 in
def fd_memset_region : MLIR.AST.Region 0 := [mlir_region|
{
  ^bb0(%arg0: !llvm.ptr, %arg1: i64):
    %0 = "llvm.mlir.constant"() <{value = 0 : i8}> : () -> i8
    "llvm.intr.memset"(%arg0, %0, %arg1) <{isVolatile = false}> : (!llvm.ptr, i8, i64) -> ()
    "llvm.return"(%arg0) : (!llvm.ptr) -> ()
}
]

set_option maxRecDepth 100000 in
def fd_memset : Cfg (Ctxt.ofList [SLLVM.Ty.bitvec 64, SLLVM.Ty.ptr]) [SLLVM.Ty.ptr] :=
  [sllvm_cfg_of| fd_memset_region]

end Firedancer.Common
