/- Released under Apache 2.0 license as described in the file LICENSE. -/
import SSA.Projects.Agave.LatticeHash.MLIR.BatchCFG8
import SSA.Projects.Agave.LatticeHash.MLIR.agave_batch_16
namespace AgaveLatticeHash.MLIR
open LeanMLIR SLLVM

sllvm_cfg_def agave_batch_16 : Cfg
    (Ctxt.ofList [SLLVM.Ty.ptr, .ptr, .ptr]) [] :=
  [sllvm_cfg_of| agave_batch_16_region with
    @_RNvNtNtCsgxBkk5gSRhY_4core5slice5index16slice_index_fail := sliceIndexFail]

end AgaveLatticeHash.MLIR
