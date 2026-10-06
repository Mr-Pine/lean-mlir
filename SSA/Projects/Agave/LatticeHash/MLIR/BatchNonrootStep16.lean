/- Released under Apache 2.0 license as described in the file LICENSE. -/
import SSA.Projects.Agave.LatticeHash.MLIR.BatchNonrootTargets16
import SSA.Projects.Agave.LatticeHash.MLIR.BatchNonrootSemantic16
import SSA.Projects.Agave.LatticeHash.MLIR.BatchHeaderSemantics16
import SSA.Projects.Agave.LatticeHash.MLIR.BatchRoundMemory16

namespace AgaveLatticeHash.MLIR.BatchNonrootStep16
open LeanMLIR SLLVM Firedancer
open BatchRefinement16

attribute [local irreducible] BatchHeader16.values16 Blocks.run

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
/-- Actual nonroot compression and masked update advance the represented
scalar-prefix state. Its schedule and message loads are derived from caller
memory preservation and the scratch-message contract. -/
theorem run (entry current : GlobalState) (src len out sched panic : Pointer)
    (p : AgavePhysicalStaging.Store) (a : AgaveStaging.Value)
    (hc : CallerMemory.Represents entry 16 src len out sched panic p a)
    (hm : BatchMemory16 entry current)
    (ms : Fin 16 → AgaveConcrete.Message) (t : Nat)
    (hms : ∀ lane, (ms lane).length ≤ 1024)
    (hstage : ∀ lane, AgaveBatchControl.ValidStaging (ms lane).length 1024
      (AgaveConcrete.bytes (ms lane)) (AgavePhysicalStaging.memoryAt p lane.val))
    (hmsg : CompressionMessage current.mem (BatchEntry16.scratch entry 0)
      (BatchTranspose16.columns16 (CallerMemory.rows16 p ms t))) :
    StateT.run (agave_batch_16.blocks.run (ambient16 entry src len out sched panic ms)
      (BatchTranspose16.nonrootTarget16
        (transposeAt16 (ambient16 entry src len out sched panic ms) ms t))) current =
    StateT.run (agave_batch_16.blocks.run (ambient16 entry src len out sched panic ms)
      (headerAt16 ms (t+1))) current := by
  have hround := frameRoundMemory16 hc hm 0
    (BatchTranspose16.columns16 (CallerMemory.rows16 p ms t)) hmsg
  rw [nonrootNextAt16 entry src len out sched panic ms t hms]
  exact BatchNonrootSemantic16.run entry current src len out sched panic
    (Vector.ofFn fun i : Fin 8 => BitVec.ofNat 64 (ms ⟨i.val, by omega⟩).length)
    (Vector.ofFn fun i : Fin 8 => BitVec.ofNat 64 (ms ⟨i.val+8, by omega⟩).length)
    p ms t
    (BatchHeader16.values16 (headerAt16Val (ambient16 entry src len out sched panic ms) ms t) ⟨37, rfl⟩)
    (BatchHeader16.values16 (headerAt16Val (ambient16 entry src len out sched panic ms) ms t) ⟨43, rfl⟩)
    hms hstage
    (BatchHeader16.size_words16 entry src len out sched panic ms t hms)
    (BatchHeader16.flags_words16 entry src len out sched panic ms t hms)
    hround.scheduleFits hround.scheduleRead hround.messageFits hround.messageRead

end AgaveLatticeHash.MLIR.BatchNonrootStep16
