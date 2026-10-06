/- Released under Apache 2.0 license as described in the file LICENSE. -/
import SSA.Projects.Agave.LatticeHash.MLIR.BatchState16
import SSA.Projects.Agave.LatticeHash.MLIR.BatchXofMemoryCore16
import SSA.Projects.Agave.LatticeHash.MLIR.BatchRefinement16

namespace AgaveLatticeHash.MLIR
open LeanMLIR SLLVM Firedancer Blake3Compression
open CompressionRound BatchXofLoop16
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

/-- The actual entry supplies all root-XOF initialization constants. -/
theorem rootInitEnv16 (entry : GlobalState) (src len out sched panic : Pointer)
    (ms : Fin 16 → AgaveConcrete.Message) :
    InitEnv (BatchRefinement16.ambient16 entry src len out sched panic ms) := by
  constructor <;> rfl

/-- The actual entry supplies the output pointer and bounded-counter constants. -/
theorem rootOutputEnv16 (entry : GlobalState) (src len out sched panic : Pointer)
    (ms : Fin 16 → AgaveConcrete.Message) :
    OutputEnv (BatchRefinement16.ambient16 entry src len out sched panic ms) out := by
  constructor <;> rfl

/-- The actual captured root-round environment points to the copied message
and immutable schedule, with all rotation and index constants from entry. -/
theorem rootRoundEnvAt16 (entry : GlobalState) (src len out sched panic : Pointer)
    (ms : Fin 16 → AgaveConcrete.Message) (cv : CV (Vector Word 16))
    (sizes flags : Vector Word 16) (counter : Nat) :
    RoundEnv16 (sourceVal (BatchRefinement16.ambient16 entry src len out sched panic ms)
      (extras cv sizes flags counter) 0 (rootInitial cv sizes flags counter))
      (BatchEntry16.scratch entry 1) sched := by
  constructor <;> rfl

/-- The actual captured root-round environment points to the copied message
and immutable schedule, with all rotation and index constants from entry. -/
theorem rootRoundEnv16 (entry : GlobalState) (src len out sched panic : Pointer)
    (ms : Fin 16 → AgaveConcrete.Message) (cv : CV (Vector Word 16))
    (sizes flags : Vector Word 16) :
    RoundEnv16 (sourceVal (BatchRefinement16.ambient16 entry src len out sched panic ms)
      (extras cv sizes flags 0) 0 (rootInitial cv sizes flags 0))
      (BatchEntry16.scratch entry 1) sched := by
  constructor <;> rfl

/-- The retained-root memory contract follows from the original caller image,
the preserved caller frame, and the checked complete-message copy. -/
theorem rootMemory16 {entry current : GlobalState}
    {src len out sched panic : Pointer} {p : AgavePhysicalStaging.Store} {a : AgaveStaging.Value}
    (hc : CallerMemory.Represents entry 16 src len out sched panic p a)
    (hf : BatchMemory16 entry current) (words : State (Vector Word 16))
    (hmsg : CompressionMessage current.mem (BatchEntry16.scratch entry 1) words) :
    InitialMemory current out (BatchEntry16.scratch entry 1) sched words
      (outputSlice (CallerMemory.accumulatorWords a)) := by
  apply InitialMemory.ofPacked current out (BatchEntry16.scratch entry 1) sched words
    (CallerMemory.accumulatorWords a)
  · intro r i
    have hfit : Fits entry.mem (schedulePtr16 sched r i) 64 := by
      simpa only [schedulePtr16, rowPtr16, schedulePtr_two_geps] using scheduleGlobal_fits hc.schedule r i
    exact fits_of_live?_eq (hf.caller _ (lt_nextFreeBlock_of_fits hc.wf hfit)) hfit
  · intro r i
    have hfit : Fits entry.mem (schedulePtr16 sched r i) 64 := by
      simpa only [schedulePtr16, rowPtr16, schedulePtr_two_geps] using scheduleGlobal_fits hc.schedule r i
    rw [hf.read hc.wf hfit]
    simpa only [schedulePtr16, rowPtr16, schedulePtr_two_geps] using scheduleGlobal_read hc.schedule r i
  · intro i
    have hptr : messagePtr16 (BatchEntry16.scratch entry 1) i =
        (BatchEntry16.scratch entry 1).withOffset (BitVec.ofNat 64 (64*i.val)) := by
      unfold messagePtr16
      rw [show (64 : BitVec 64) = BitVec.ofNat 64 64 from rfl, ← BitVec.ofNat_mul]
      rw [Nat.mul_comm i.val 64]
    rw [hptr]
    exact compressionSlotFits16 hmsg.fits i.val i.isLt
  · intro i
    have hptr : messagePtr16 (BatchEntry16.scratch entry 1) i =
        (BatchEntry16.scratch entry 1).withOffset (BitVec.ofNat 64 (64*i.val)) := by
      unfold messagePtr16
      rw [show (64 : BitVec 64) = BitVec.ofNat 64 64 from rfl, ← BitVec.ofNat_mul]
      rw [Nat.mul_comm i.val 64]
    rw [hptr]
    exact hmsg.read i
  · exact fits_of_live?_eq (hf.caller _ (lt_nextFreeBlock_of_fits hc.wf hc.accumulator.2.1)) hc.accumulator.2.1
  · simp [hc.out_zero]
  · rw [hf.read hc.wf hc.accumulator.2.1]
    exact readWord?_eq_some hc.accumulator.2.1 hc.accumulator.2.2
  · exact hc.output_schedule
  · exact Ne.symm (BatchEntry16.scratch_ne_input hc.wf hc.accumulator.2.1 1)

end AgaveLatticeHash.MLIR
