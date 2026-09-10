/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.SLLVM.Cfg

/-!
# `fd_ulong_load_8` (common)

Byte-identical (modulo indentation) to
`build/native/gcc/mlir/{ref,avx512}/region/fd_ulong_load_8.mlir`, which are the
same file: an unaligned little-endian `ulong` load, `fd_bits.h`. Neither backend
specialises it, so it lives in `Common`.
-/

namespace Firedancer.Common
open LeanMLIR SLLVM

def fd_ulong_load_8_region : MLIR.AST.Region 0 := [mlir_region|
{
  ^bb0(%arg0: !llvm.ptr):
    %0 = "llvm.load"(%arg0) <{alignment = 1 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i64
    "llvm.return"(%0) : (i64) -> ()
}
]

def fd_ulong_load_8 : Cfg (Ctxt.ofList [SLLVM.Ty.ptr]) [SLLVM.Ty.bitvec 64] :=
  [sllvm_cfg_of| fd_ulong_load_8_region]

end Firedancer.Common
