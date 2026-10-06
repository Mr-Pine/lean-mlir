/- Released under Apache 2.0 license as described in the file LICENSE. -/
import SSA.Projects.Agave.LatticeHash.MLIR.BatchRootMemory16
import SSA.Projects.Agave.LatticeHash.MLIR.BatchRootTargets16

namespace AgaveLatticeHash.MLIR
open LeanMLIR SLLVM Firedancer Blake3Compression CompressionExit
open BatchRefinement16 BatchXofLoop16
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

/-- Execute the actual copied-root branch through all 32 XOF counters and
normal return. Its only memory assumptions are the maintained caller frame,
valid scratch buffers, and the message produced by the preceding transpose. -/
theorem root_branch16 (entry current : GlobalState) (src len out sched panic : Pointer)
    (p : AgavePhysicalStaging.Store) (a : AgaveStaging.Value)
    (hc : CallerMemory.Represents entry 16 src len out sched panic p a)
    (hm : BatchMemory16 entry current)
    (ms : Fin 16 → AgaveConcrete.Message) (iteration : Nat)
    (hms : ∀ lane, (ms lane).length ≤ 1024)
    (hmsg : CompressionMessage current.mem (BatchEntry16.scratch entry 0)
      (BatchTranspose16.columns16 (CallerMemory.rows16 p ms iteration))) :
    ∃ final, StateT.run (agave_batch_16.blocks.run
      (ambient16 entry src len out sched panic ms)
      (BatchTranspose16.rootTarget16
        (transposeAt16 (ambient16 entry src len out sched panic ms) ms iteration))) current =
      .value (.nil, final) ∧ Fits final.mem out 16384 ∧
      ∀ c, c < 32 → readWord? (outputPtr out c) 512 final.mem =
        some (packBits (BatchOutput16.sums32
          (outputSlice (CallerMemory.accumulatorWords a) c)
          (delta (rootCVAt16 ms iteration) (rootSizes16 ms iteration) (rootFlags16 ms iteration)
            (BatchTranspose16.columns16 (CallerMemory.rows16 p ms iteration)) c))) := by
  let A := ambient16 entry src len out sched panic ms
  let V := transposeAt16 A ms iteration
  let bytes : BitVec 8192 := readWord (hm.scratch 0)
  have hr : readWord? (BatchEntry16.scratch entry 0) 8192 current.mem = some bytes :=
    readWord?_eq_some (hm.scratch 0) rfl
  let copied : GlobalState := {current with mem := current.mem.splice (BatchEntry16.scratch entry 1) bytes}
  have hcopy := BatchRootRun16.run5 A (BatchTranspose16.rootTarget16 V).args current
    (BatchEntry16.scratch entry 0) (BatchEntry16.scratch entry 1) bytes
    (rootCopyEnv16 entry src len out sched panic ms iteration).1
    (rootCopyEnv16 entry src len out sched panic ms iteration).2.1
    (rootCopyEnv16 entry src len out sched panic ms iteration).2.2
    (hm.scratch 0) (hm.scratch 1) hr
  have heta : (⟨5, rfl, (BatchTranspose16.rootTarget16 V).args⟩ : SuccArgs agave_batch_16.cfgSigs) =
      BatchTranspose16.rootTarget16 V := rfl
  rw [heta] at hcopy
  have hn := rootNextAt16 entry src len out sched panic ms iteration hms
  change BatchRootCopy16.next5 (BatchRootRun16.input5 A (BatchTranspose16.rootTarget16 V).args) = _ at hn
  rw [hn] at hcopy
  have hcopied : BatchMemory16 entry copied := hm.copy 1 bytes
  have hretained : CompressionMessage copied.mem (BatchEntry16.scratch entry 1)
      (BatchTranspose16.columns16 (CallerMemory.rows16 p ms iteration)) :=
    copyMessage16 hmsg (hm.scratch 1) (by rfl) (by rfl) bytes hr
  have hMem := rootMemory16 hc hcopied _ hretained
  have hrun := xof32_run A (rootCVAt16 ms iteration)
    (rootSizes16 ms iteration) (rootFlags16 ms iteration) out (BatchEntry16.scratch entry 1) sched
    (rootInitEnv16 entry src len out sched panic ms)
    (rootOutputEnv16 entry src len out sched panic ms) copied
    (BatchTranspose16.columns16 (CallerMemory.rows16 p ms iteration))
    (outputSlice (CallerMemory.accumulatorWords a))
    (fun c _ => rootRoundEnvAt16 entry src len out sched panic ms _ _ _ c)
    (fun c hc32 => hMem.iteration copied out (BatchEntry16.scratch entry 1) sched
      (rootCVAt16 ms iteration) (rootSizes16 ms iteration) (rootFlags16 ms iteration)
      (BatchTranspose16.columns16 (CallerMemory.rows16 p ms iteration))
      (outputSlice (CallerMemory.accumulatorWords a)) c hc32)
  refine ⟨_, hcopy.trans hrun, ?_, ?_⟩
  · exact fits_accumulatedState copied out _ _ _ _ _ 32 hMem.outputFits
  · intro c hc32
    exact hMem.completed_reads copied out (BatchEntry16.scratch entry 1) sched
      (rootCVAt16 ms iteration) (rootSizes16 ms iteration) (rootFlags16 ms iteration)
      (BatchTranspose16.columns16 (CallerMemory.rows16 p ms iteration))
      (outputSlice (CallerMemory.accumulatorWords a)) 32 c (by omega) hc32

end AgaveLatticeHash.MLIR
