/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
-- build/native/gcc/mlir_canonicalized/{ref,avx512}/region/fd_int_min.mlir
import SSA.Projects.SLLVM.Cfg

namespace Firedancer.Common
open LeanMLIR SLLVM

def fd_int_min_region : MLIR.AST.Region 0 := [mlir_region|
{
  ^bb0(%arg0: i32):
    %0 = "llvm.mlir.constant"() <{value = 14 : i32}> : () -> i32
    %1 = "llvm.intr.smin"(%arg0, %0) : (i32, i32) -> i32
    "llvm.return"(%1) : (i32) -> ()
}
]

sllvm_cfg_def fd_int_min : Cfg (Ctxt.ofList [SLLVM.Ty.bitvec 32]) [SLLVM.Ty.bitvec 32] :=
  [sllvm_cfg_of| fd_int_min_region]

end Firedancer.Common
