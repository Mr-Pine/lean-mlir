/- Released under Apache 2.0 license as described in the file LICENSE. -/
import SSA.Projects.Agave.LatticeHash.MLIR.BatchNonrootStep8

namespace AgaveLatticeHash.MLIR.BatchOuter8
open LeanMLIR SLLVM Firedancer

/-- The compiled input loop reaches its root-copy block after at most `fuel`
nonroot updates. The bound is on independent scalar root indices, and the
result includes the byte-backed root-message representation. -/
theorem reachesRoot {entry current : GlobalState} {src len out sched panic : Pointer}
    {p : AgavePhysicalStaging.Store} {a : AgaveStaging.Value}
    (hrep : CallerMemory.Represents entry 8 src len out sched panic p a)
    (hm : BatchMemory8 entry current) (ms : Fin 8 → AgaveConcrete.Message)
    (hms : ∀ lane, (ms lane).length ≤ 1024)
    (hstage : ∀ lane, AgaveBatchControl.ValidStaging (ms lane).length 1024
      (AgaveConcrete.bytes (ms lane)) (AgavePhysicalStaging.memoryAt p lane.val))
    (t fuel : Nat) (hbound : ∀ lane, AgaveBatchControl.rootIndex (ms lane).length ≤ t+fuel) :
    ∃ finish final, t ≤ finish ∧ finish ≤ t+fuel ∧
      (∀ lane, AgaveBatchControl.rootIndex (ms lane).length ≤ finish) ∧
      BatchMemory8 entry final ∧
      CompressionMessage final.mem (BatchEntry.scratch entry 0) (BatchReadInput8.columns p ms finish) ∧
      StateT.run (agave_batch_8.blocks.run (BatchReadInput8.ambient entry src len out sched panic ms)
        (headerAt8 ms t)) current =
      StateT.run (agave_batch_8.blocks.run (BatchReadInput8.ambient entry src len out sched panic ms)
        (BatchInputSuccessor.rootAt ms finish)) final := by
  induction fuel generalizing t current with
  | zero =>
    have hd : ∀ lane, AgaveBatchControl.rootIndex (ms lane).length ≤ t := by simpa using hbound
    refine ⟨t, BatchReadInput8.afterInput entry current p ms t, le_rfl, by omega, hd,
      BatchReadInput8.memory hm p ms t, BatchReadInput8.message hm p ms t, ?_⟩
    simpa only [ite_eq_left hd] using BatchReadInput8.run hrep hm ms t hms
  | succ fuel ih =>
    by_cases hd : ∀ lane, AgaveBatchControl.rootIndex (ms lane).length ≤ t
    · refine ⟨t, BatchReadInput8.afterInput entry current p ms t, le_rfl, by omega, hd,
        BatchReadInput8.memory hm p ms t, BatchReadInput8.message hm p ms t, ?_⟩
      simpa only [ite_eq_left hd] using BatchReadInput8.run hrep hm ms t hms
    · let next := BatchReadInput8.afterInput entry current p ms t
      have hn : BatchMemory8 entry next := BatchReadInput8.memory hm p ms t
      have hb : ∀ lane, AgaveBatchControl.rootIndex (ms lane).length ≤ (t+1)+fuel := by
        intro lane
        have := hbound lane
        omega
      obtain ⟨finish, final, hlo, hhi, hdone, hmem, hmsg, hexec⟩ := ih hn (t+1) hb
      refine ⟨finish, final, by omega, by omega, hdone, hmem, hmsg, ?_⟩
      calc
        _ = StateT.run (agave_batch_8.blocks.run (BatchReadInput8.ambient entry src len out sched panic ms)
            (BatchInputSuccessor.nonrootAt ms t)) next := by
          simpa only [ite_eq_right hd] using BatchReadInput8.run hrep hm ms t hms
        _ = StateT.run (agave_batch_8.blocks.run (BatchReadInput8.ambient entry src len out sched panic ms)
            (headerAt8 ms (t+1))) next :=
          BatchNonrootStep8.run hrep hn ms t hstage (BatchReadInput8.message hm p ms t)
        _ = _ := hexec

/-- Legal one-chunk lanes require at most fifteen updates before their root. -/
theorem reachesRoot_fromEntry {entry : GlobalState} {src len out sched panic : Pointer}
    {p : AgavePhysicalStaging.Store} {a : AgaveStaging.Value}
    (hrep : CallerMemory.Represents entry 8 src len out sched panic p a)
    (ms : Fin 8 → AgaveConcrete.Message) (hms : ∀ lane, (ms lane).length ≤ 1024)
    (hstage : ∀ lane, AgaveBatchControl.ValidStaging (ms lane).length 1024
      (AgaveConcrete.bytes (ms lane)) (AgavePhysicalStaging.memoryAt p lane.val)) :
    ∃ finish final, finish ≤ 15 ∧
      (∀ lane, AgaveBatchControl.rootIndex (ms lane).length ≤ finish) ∧
      BatchMemory8 entry final ∧
      CompressionMessage final.mem (BatchEntry.scratch entry 0) (BatchReadInput8.columns p ms finish) ∧
      StateT.run (agave_batch_8.blocks.run (BatchReadInput8.ambient entry src len out sched panic ms)
        BatchEntry.header8) (BatchEntry.entryState entry) =
      StateT.run (agave_batch_8.blocks.run (BatchReadInput8.ambient entry src len out sched panic ms)
        (BatchInputSuccessor.rootAt ms finish)) final := by
  obtain ⟨finish, final, _, hhi, hdone, hmem, hmsg, hexec⟩ :=
    reachesRoot hrep (batchMemory8_entry entry) ms hms hstage 0 15
      (fun lane => by have := AgaveBatchControl.rootIndex_lt16 _ (hms lane); omega)
  exact ⟨finish, final, hhi, hdone, hmem, hmsg, by simpa only [headerAt8_zero] using hexec⟩

end AgaveLatticeHash.MLIR.BatchOuter8
