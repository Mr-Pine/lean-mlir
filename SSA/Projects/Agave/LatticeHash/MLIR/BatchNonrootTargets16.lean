/- Released under Apache 2.0 license as described in the file LICENSE. -/
import SSA.Projects.Agave.LatticeHash.MLIR.BatchPrefixTargets16
import SSA.Projects.Agave.LatticeHash.MLIR.BatchNonrootData16

namespace AgaveLatticeHash.MLIR.BatchRefinement16
open LeanMLIR SLLVM
open InstCombine (LLVM)
attribute [local irreducible] BatchHeader16.values16

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
/-- The actual nonroot successor is exactly the composition-ready compression
entry, carrying the scalar-prefix CV, offsets, packed metadata and active mask. -/
theorem nonrootNextAt16 (s : GlobalState) (src len out sched panic : Pointer)
    (ms : Fin 16 → AgaveConcrete.Message) (t : Nat)
    (hms : ∀ lane, (ms lane).length ≤ 1024) :
    BatchTranspose16.nonrootTarget16
      (transposeAt16 (ambient16 s src len out sched panic ms) ms t) =
    BatchNonrootRounds16.initTarget (BatchUpdate16.stateCV16 ms t)
      (BatchHeader16.values16 (headerAt16Val (ambient16 s src len out sched panic ms) ms t) ⟨37, rfl⟩)
      (BatchHeader16.values16 (headerAt16Val (ambient16 s src len out sched panic ms) ms t) ⟨43, rfl⟩)
      (BatchUpdate16.offsetsAt16 ms t) (BatchUpdate16.activeAt16 ms t) := by
  let A := ambient16 s src len out sched panic ms
  let V := headerAt16Val A ms t
  have hm : (show Vector (LLVM.IntW 8) 16 from BatchHeader16.values16 V ⟨33, rfl⟩) =
      BatchUpdate16.activeBytes16 (BatchUpdate16.activeAt16 ms t) :=
    (header_active_bytes16 s src len out sched panic ms t hms).trans
      (activeBytes16_update ms t)
  have hf := nonroot_forward A (BatchUpdate16.stateCV16 ms t) (BatchUpdate16.offsetsAt16 ms t)
  have hg := congrArg (fun bytes : Vector (LLVM.IntW 8) 16 =>
    (⟨6, rfl, (headerAt16 ms t).args.append
      [BatchHeader16.values16 V ⟨43, rfl⟩, BatchHeader16.values16 V ⟨37, rfl⟩, bytes]ₕ⟩ :
      SuccArgs agave_batch_16.cfgSigs)) hm
  exact hf.trans hg

end AgaveLatticeHash.MLIR.BatchRefinement16
