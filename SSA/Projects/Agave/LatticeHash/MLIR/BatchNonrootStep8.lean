/- Released under Apache 2.0 license as described in the file LICENSE. -/
import SSA.Projects.Agave.LatticeHash.MLIR.BatchNonrootSemantic8
import SSA.Projects.Agave.LatticeHash.MLIR.BatchNonrootRounds8

namespace AgaveLatticeHash.MLIR.BatchNonrootStep8
open LeanMLIR SLLVM Firedancer Blake3Compression
open InstCombine (LLVM)
open BatchNonrootRounds8 BatchNonrootSemantic8

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
theorem update_run (entry current : GlobalState) (src len out sched panic : Pointer)
    (p : AgavePhysicalStaging.Store) (ms : Fin 8 → AgaveConcrete.Message) (t : Nat)
    (hstage : ∀ lane, AgaveBatchControl.ValidStaging (ms lane).length 1024
      (AgaveConcrete.bytes (ms lane)) (AgavePhysicalStaging.memoryAt p lane.val)) :
    let B := BatchReadInput8.ambient entry src len out sched panic ms
    let e := extras (BatchUpdate.stateCV8 ms t) (BatchUpdate.offsetsAt8 ms t)
      (BatchUpdate.advancedAt8 ms t) (BatchUpdate.activeAt8 ms t)
    StateT.run (agave_batch_8.blocks.run B (updateTarget e (finalState p ms t))) current =
      StateT.run (agave_batch_8.blocks.run B (headerAt8 ms (t+1))) current := by
  dsimp only
  let B := BatchReadInput8.ambient entry src len out sched panic ms
  let e := extras (BatchUpdate.stateCV8 ms t) (BatchUpdate.offsetsAt8 ms t)
    (BatchUpdate.advancedAt8 ms t) (BatchUpdate.activeAt8 ms t)
  have hz : B ⟨28, rfl⟩ = Vector.replicate 32 (PoisonOr.value 0#8) := rfl
  have he := update_env B hz (BatchUpdate.stateCV8 ms t) (BatchUpdate.offsetsAt8 ms t)
    (BatchUpdate.advancedAt8 ms t) (BatchUpdate.activeAt8 ms t) (finalState p ms t)
  have hrun := BatchUpdate.update8_stateAt (updateVal B e (finalState p ms t)) current ms t
    (upperCV (finalState p ms t)) (lowerCV (finalState p ms t)) he
    (compression_active p ms t hstage)
  denote_enter_block
  apply EffectM.run_bind_of_value hrun

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
/-- The actual seven inlined rounds and masked update advance the existing
scalar-prefix invariant. All schedule reads come from the caller global and
all message reads from the completed compiler transpose. -/
theorem run {entry current : GlobalState} {src len out sched panic : Pointer}
    {p : AgavePhysicalStaging.Store} {a : AgaveStaging.Value}
    (hrep : CallerMemory.Represents entry 8 src len out sched panic p a)
    (hm : BatchMemory8 entry current) (ms : Fin 8 → AgaveConcrete.Message) (t : Nat)
    (hstage : ∀ lane, AgaveBatchControl.ValidStaging (ms lane).length 1024
      (AgaveConcrete.bytes (ms lane)) (AgavePhysicalStaging.memoryAt p lane.val))
    (hmessage : CompressionMessage current.mem (BatchEntry.scratch entry 0)
      (BatchReadInput8.columns p ms t)) :
    StateT.run (agave_batch_8.blocks.run (BatchReadInput8.ambient entry src len out sched panic ms)
      (BatchInputSuccessor.nonrootAt ms t)) current =
    StateT.run (agave_batch_8.blocks.run (BatchReadInput8.ambient entry src len out sched panic ms)
      (headerAt8 ms (t+1))) current := by
  rw [nonroot_target]
  have hptr (i : Fin 16) : CompressionRound.messagePtr8 (BatchEntry.scratch entry 0) i =
      (BatchEntry.scratch entry 0).withOffset (BitVec.ofNat 64 (32*i.val)) := by
    unfold CompressionRound.messagePtr8
    rw [show (32 : BitVec 64) = BitVec.ofNat 64 32 from rfl, ← BitVec.ofNat_mul]
    rw [Nat.mul_comm i.val 32]
  have hmi (i : Fin 16) : Fits current.mem
      (CompressionRound.messagePtr8 (BatchEntry.scratch entry 0) i) 256 := by
    rw [hptr]
    exact compressionSlotFits8 hmessage.fits i.val i.isLt
  have hmv (i : Fin 16) : readWord? (CompressionRound.messagePtr8 (BatchEntry.scratch entry 0) i)
      256 current.mem = some (packBits (BatchReadInput8.columns p ms t i)) := by
    rw [hptr]
    exact hmessage.read i
  have hsi (r : Fin 7) (i : Fin 16) : Fits current.mem (CompressionRound.schedulePtr sched r i) 64 := by
    apply hm.fits hrep.wf
    simpa only [CompressionRound.schedulePtr, CompressionRound.rowPtr, schedulePtr_two_geps] using
      scheduleGlobal_fits hrep.schedule r i
  have hsv (r : Fin 7) (i : Fin 16) : readWord? (CompressionRound.schedulePtr sched r i) 64 current.mem =
      some (BitVec.ofNat 64 (schedule r i).val) := by
    have hf : Fits entry.mem (CompressionRound.schedulePtr sched r i) 64 := by
      simpa only [CompressionRound.schedulePtr, CompressionRound.rowPtr, schedulePtr_two_geps] using
        scheduleGlobal_fits hrep.schedule r i
    rw [hm.read hrep.wf hf]
    simpa only [CompressionRound.schedulePtr, CompressionRound.rowPtr, schedulePtr_two_geps] using
      scheduleGlobal_read hrep.schedule r i
  rw [init_seven_rounds_run _ (init_env entry src len out sched panic ms) _ _ _ _ _ _
    (BatchEntry.scratch entry 0) sched (BatchReadInput8.columns p ms t)
    (round_env entry src len out sched panic ms _ _ _ _ _ _) current hsi hsv hmi hmv]
  exact update_run entry current src len out sched panic p ms t hstage

end AgaveLatticeHash.MLIR.BatchNonrootStep8
