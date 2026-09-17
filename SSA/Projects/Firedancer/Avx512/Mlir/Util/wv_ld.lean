/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
-- build/native/gcc/mlir_canonicalized/avx512/region/wv_ld.mlir
import SSA.Projects.SLLVM.Cfg

namespace Firedancer.Avx512
open LeanMLIR SLLVM

def wv_ld_region : MLIR.AST.Region 0 := [mlir_region|
{
  ^bb0(%arg0: !llvm.ptr):
    %0 = "llvm.load"(%arg0) <{alignment = 32 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<4xi64>
    "llvm.return"(%0) : (vector<4xi64>) -> ()
}
]

sllvm_cfg_def wv_ld : Cfg (Ctxt.ofList [SLLVM.Ty.ptr])
    [SLLVM.Ty.arith (.vector 4 (.bitvec (.concrete 64)))] :=
  [sllvm_cfg_of| wv_ld_region]

end Firedancer.Avx512
