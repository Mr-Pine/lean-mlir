/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.SLLVM.Cfg

/-!
# `fd_ulong_bswap` (common)

Byte-identical (modulo indentation) to
`build/native/gcc/mlir/{ref,avx512}/region/fd_ulong_bswap.mlir`. The two
backends emit the same file, so the function is lifted once, here.

`fd_bits.h`: reverse the byte order of a `ulong`.
-/

namespace Firedancer.Common
open LeanMLIR SLLVM

set_option maxRecDepth 100000 in
def fd_ulong_bswap_region : MLIR.AST.Region 0 := [mlir_region|
{
  ^bb0(%arg0: i64):
    %0 = "llvm.intr.bswap"(%arg0) : (i64) -> i64
    "llvm.return"(%0) : (i64) -> ()
}
]

set_option maxRecDepth 100000 in
def fd_ulong_bswap : Cfg (Ctxt.ofList [SLLVM.Ty.bitvec 64]) [SLLVM.Ty.bitvec 64] :=
  [sllvm_cfg_of| fd_ulong_bswap_region]

end Firedancer.Common
