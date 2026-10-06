/- Released under Apache 2.0 license as described in the file LICENSE. -/
import SSA.Projects.Agave.LatticeHash.MLIR.BatchNonrootStep16

namespace AgaveLatticeHash.MLIR.BatchOuter16
open LeanMLIR SLLVM Firedancer Blake3Compression CompressionExit BatchRefinement16
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Blocks.run

noncomputable def afterInput (entry current : GlobalState) (p : AgavePhysicalStaging.Store)
    (ms : Fin 16 → AgaveConcrete.Message) (t : Nat) : GlobalState :=
  {current with mem := outputMem (BatchEntry16.scratch entry 0) (BatchTranspose16.columns16 (CallerMemory.rows16 p ms t)) 16 current.mem}

theorem memory {entry current : GlobalState} (hm : BatchMemory16 entry current)
    (p : AgavePhysicalStaging.Store) (ms : Fin 16 → AgaveConcrete.Message) (t : Nat) :
    BatchMemory16 entry (afterInput entry current p ms t) :=
  hm.transpose 0 (CallerMemory.rows16 p ms t)

theorem message {entry current : GlobalState} (hm : BatchMemory16 entry current)
    (p : AgavePhysicalStaging.Store) (ms : Fin 16 → AgaveConcrete.Message) (t : Nat) :
    CompressionMessage (afterInput entry current p ms t).mem (BatchEntry16.scratch entry 0)
      (BatchTranspose16.columns16 (CallerMemory.rows16 p ms t)) :=
  by
  dsimp only [afterInput]
  exact hm.message (CallerMemory.rows16 p ms t)

/-- The actual input loop reaches root-copy in finitely many scalar-prefix updates. -/
theorem reachesRoot {entry current : GlobalState} {src len out sched panic : Pointer}
    {p : AgavePhysicalStaging.Store} {a : AgaveStaging.Value}
    (hrep : CallerMemory.Represents entry 16 src len out sched panic p a)
    (hm : BatchMemory16 entry current) (ms : Fin 16 → AgaveConcrete.Message)
    (hms : ∀ lane, (ms lane).length ≤ 1024)
    (hstage : ∀ lane, AgaveBatchControl.ValidStaging (ms lane).length 1024
      (AgaveConcrete.bytes (ms lane)) (AgavePhysicalStaging.memoryAt p lane.val))
    (t fuel : Nat) (hbound : ∀ lane, AgaveBatchControl.rootIndex (ms lane).length ≤ t+fuel) :
    ∃ finish final, t ≤ finish ∧ finish ≤ t+fuel ∧
      (∀ lane, AgaveBatchControl.rootIndex (ms lane).length ≤ finish) ∧
      BatchMemory16 entry final ∧
      CompressionMessage final.mem (BatchEntry16.scratch entry 0)
        (BatchTranspose16.columns16 (CallerMemory.rows16 p ms finish)) ∧
      StateT.run (agave_batch_16.blocks.run (ambient16 entry src len out sched panic ms)
        (headerAt16 ms t)) current =
      StateT.run (agave_batch_16.blocks.run (ambient16 entry src len out sched panic ms)
        (BatchTranspose16.rootTarget16
          (transposeAt16 (ambient16 entry src len out sched panic ms) ms finish))) final := by
  induction fuel generalizing t current with
  | zero =>
    have hd : activeMask16 ms t = 0 := (activeMask16_zero_iff ms t).mpr (by simpa using hbound)
    refine ⟨t, afterInput entry current p ms t, le_rfl, by omega,
      (activeMask16_zero_iff ms t).mp hd, memory hm p ms t, message hm p ms t, ?_⟩
    simpa only [hd, ite_true, afterInput, sourceRows16, CallerMemory.rows16] using
      header_to_transpose_physical entry current src len out sched panic p a hrep hm ms t hms
  | succ fuel ih =>
    by_cases hd : activeMask16 ms t = 0
    · refine ⟨t, afterInput entry current p ms t, le_rfl, by omega,
        (activeMask16_zero_iff ms t).mp hd, memory hm p ms t, message hm p ms t, ?_⟩
      simpa only [hd, ite_true, afterInput, sourceRows16, CallerMemory.rows16] using
        header_to_transpose_physical entry current src len out sched panic p a hrep hm ms t hms
    · let next := afterInput entry current p ms t
      have hn : BatchMemory16 entry next := memory hm p ms t
      have hb : ∀ lane, AgaveBatchControl.rootIndex (ms lane).length ≤ (t+1)+fuel := by
        intro lane
        have := hbound lane
        omega
      obtain ⟨finish, final, hlo, hhi, hdone, hmem, hmsg, hexec⟩ := ih hn (t+1) hb
      refine ⟨finish, final, by omega, by omega, hdone, hmem, hmsg, ?_⟩
      calc
        _ = StateT.run (agave_batch_16.blocks.run (ambient16 entry src len out sched panic ms)
            (BatchTranspose16.nonrootTarget16
              (transposeAt16 (ambient16 entry src len out sched panic ms) ms t))) next := by
          simpa only [hd, ite_false, next, afterInput, sourceRows16, CallerMemory.rows16] using
            header_to_transpose_physical entry current src len out sched panic p a hrep hm ms t hms
        _ = StateT.run (agave_batch_16.blocks.run (ambient16 entry src len out sched panic ms)
            (headerAt16 ms (t+1))) next :=
          BatchNonrootStep16.run entry next src len out sched panic p a hrep hn ms t hms hstage (message hm p ms t)
        _ = _ := hexec

end AgaveLatticeHash.MLIR.BatchOuter16
