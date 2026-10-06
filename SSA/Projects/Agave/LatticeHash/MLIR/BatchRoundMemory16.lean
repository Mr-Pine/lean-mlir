/- Released under Apache 2.0 license as described in the file LICENSE. -/
import SSA.Projects.Agave.LatticeHash.MLIR.BatchState16
import SSA.Projects.Agave.LatticeHash.MLIR.CompressionProof

namespace AgaveLatticeHash.MLIR
open LeanMLIR SLLVM Firedancer Blake3Compression CompressionRound

/-- Exact memory premises of a sixteen-lane compiled compression loop. -/
structure RoundMemory16 (s : GlobalState) (msg sched : Pointer)
    (m : State (Vector Word 16)) : Prop where
  scheduleFits : ∀ r i, Fits s.mem (schedulePtr16 sched r i) 64
  scheduleRead : ∀ r i, readWord? (schedulePtr16 sched r i) 64 s.mem =
    some (BitVec.ofNat 64 (schedule r i).val)
  messageFits : ∀ i, Fits s.mem (messagePtr16 msg i) 512
  messageRead : ∀ i, readWord? (messagePtr16 msg i) 512 s.mem = some (packBits (m i))

/-- Derive the checked compression loop's memory contract from the preserved
caller schedule and actual scratch-message readback. -/
theorem frameRoundMemory16 {entry current : GlobalState}
    {src len out sched panic : Pointer} {p : AgavePhysicalStaging.Store} {a : AgaveStaging.Value}
    (hc : CallerMemory.Represents entry 16 src len out sched panic p a)
    (hf : BatchMemory16 entry current) (i : Fin 2) (words : State (Vector Word 16))
    (hmsg : CompressionMessage current.mem (BatchEntry16.scratch entry i) words) :
    RoundMemory16 current (BatchEntry16.scratch entry i) sched words := by
  constructor
  · intro r w
    have hfit : Fits entry.mem (schedulePtr16 sched r w) 64 := by
      simpa only [schedulePtr16, rowPtr16, schedulePtr_two_geps] using scheduleGlobal_fits hc.schedule r w
    exact fits_of_live?_eq (hf.caller _ (lt_nextFreeBlock_of_fits hc.wf hfit)) hfit
  · intro r w
    have hfit : Fits entry.mem (schedulePtr16 sched r w) 64 := by
      simpa only [schedulePtr16, rowPtr16, schedulePtr_two_geps] using scheduleGlobal_fits hc.schedule r w
    rw [hf.read hc.wf hfit]
    simpa only [schedulePtr16, rowPtr16, schedulePtr_two_geps] using scheduleGlobal_read hc.schedule r w
  · intro w
    have hptr : messagePtr16 (BatchEntry16.scratch entry i) w =
        (BatchEntry16.scratch entry i).withOffset (BitVec.ofNat 64 (64*w.val)) := by
      unfold messagePtr16
      rw [show (64 : BitVec 64) = BitVec.ofNat 64 64 from rfl, ← BitVec.ofNat_mul]
      rw [Nat.mul_comm w.val 64]
    rw [hptr]
    exact compressionSlotFits16 hmsg.fits w.val w.isLt
  · intro w
    have hptr : messagePtr16 (BatchEntry16.scratch entry i) w =
        (BatchEntry16.scratch entry i).withOffset (BitVec.ofNat 64 (64*w.val)) := by
      unfold messagePtr16
      rw [show (64 : BitVec 64) = BitVec.ofNat 64 64 from rfl, ← BitVec.ofNat_mul]
      rw [Nat.mul_comm w.val 64]
    rw [hptr]
    exact hmsg.read w

end AgaveLatticeHash.MLIR
