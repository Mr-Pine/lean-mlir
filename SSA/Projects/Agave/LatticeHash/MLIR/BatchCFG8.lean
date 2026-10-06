/- Released under Apache 2.0 license as described in the file LICENSE. -/
import SSA.Projects.Agave.LatticeHash.MLIR.agave_batch_8


namespace AgaveLatticeHash.MLIR
open LeanMLIR SLLVM

/-- The sole external call is Rust's nonreturning bounds-check failure.
This is an explicit UB contract for an aborting path, not a returning stub.
The batch refinement must show that this call is unreachable for valid input. -/
def sliceIndexFail : Cfg
    (Ctxt.ofList [SLLVM.Ty.ptr, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 64]) [] :=
  ⟨.term .unreachable, .nil⟩

/-- Calling the explicit failure contract cannot produce a successful result. -/
theorem sliceIndexFail_denote (V :
    (Ctxt.ofList [SLLVM.Ty.ptr, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 64]).Valuation)
    (s : GlobalState) : StateT.run (sliceIndexFail.denote V) s = .poison := by
  rfl

sllvm_cfg_def agave_batch_8 : Cfg
    (Ctxt.ofList [SLLVM.Ty.ptr, .ptr, .ptr]) [] :=
  [sllvm_cfg_of| agave_batch_8_region with
    @_RNvNtNtCsgxBkk5gSRhY_4core5slice5index16slice_index_fail := sliceIndexFail]

end AgaveLatticeHash.MLIR
