import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMFinishOutput
import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMFinishCall
import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSourceCoreBlockBytes

namespace Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource
open LeanMLIR SLLVM Firedancer
open Agave.Ed25519.SHA512 Agave.Ed25519.SHA512.Spec
open Agave.Ed25519.Bridge.Challenge
open FinishObservation FinishExecution
namespace FinishDigest
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

private theorem observe {m : MemoryState} {p : Pointer} {n : Nat}
    (h : Core.SmallRange m p n) : ∃ r q, Observed m p r q ∧
      Agave.Ed25519.Reduce64.Execution.SmallRange r q n := by
  obtain ⟨b, hb, hs, hn⟩ := h
  exact ⟨snapshot b, snapshotPtr p, snapshot_observed hb,
    ⟨⟨b.length,b.bytes⟩, snapshot_get b, hs, hn⟩⟩

theorem readBits_sourceRead (m : MemoryState) (p : Pointer) (w : Nat) :
    Core.readBits m p w = sourceRead m p w := by
  unfold Core.readBits sourceRead readWord?
  cases m.live? p.id <;> rfl

theorem readBytes_sourceReadBytes (m : MemoryState) (p : Pointer) (n : Nat)
    (h : Core.SmallRange m p n) : Core.readBytes m p n = sourceReadBytes m p n := by
  rw [Core.readBytes_eq_ofFn m p n h]
  simp only [sourceReadBytes, readBits_sourceRead]

theorem packed_state (m : MemoryState) (p : Pointer) (h : Core.SmallRange m p 224) :
    pack (sourceReadState m p) = Core.readBits m (p.withOffset 128#64) 512 := by
  have hs : sourceReadState m p = Core.chainState m (p.withOffset 128#64) := by
    simp [sourceReadState, Core.chainState, readBits_sourceRead, Pointer.withOffset, BitVec.add_assoc]
  rw [hs, Core.pack_chainState m _ (h.add (by decide))]

theorem marker_range {m : MemoryState} {p q : Pointer} {n : Nat}
    (h : Core.SmallRange m q n) (used : Nat) : Core.SmallRange (markerMemory m p used) q n :=
  h.splice _ _

theorem long_range {m : MemoryState} {p q : Pointer} {n : Nat}
    (h : Core.SmallRange m q n) (used : Nat) : Core.SmallRange (longMemory m p used) q n :=
  h.splice _ _

theorem last_range {m : MemoryState} {p q : Pointer} {n : Nat}
    (h : Core.SmallRange m q n) (k : Nat) (lo hi : Word) :
    Core.SmallRange (lastMemory m p k lo hi) q n :=
  ((h.splice _ _).splice _ _).splice _ _

theorem marker_state (m : MemoryState) (p : Pointer) (h : Core.SmallRange m p 224)
    (used : Nat) (hn : used < 128) : sourceReadState (markerMemory m p used) p = sourceReadState m p := by
  obtain ⟨r,q,ho,hr⟩ := observe h
  exact FinishObservation.marker_state ho hr used hn

theorem long_state (m : MemoryState) (p : Pointer) (h : Core.SmallRange m p 224)
    (used : Nat) (hn : used < 128) : sourceReadState (longMemory m p used) p = sourceReadState m p := by
  obtain ⟨r,q,ho,hr⟩ := observe h
  exact FinishObservation.long_state ho hr used hn

theorem last_state (m : MemoryState) (p : Pointer) (h : Core.SmallRange m p 224)
    (n : Nat) (lo hi : Word) (hn : n ≤ 112) : sourceReadState (lastMemory m p n lo hi) p = sourceReadState m p := by
  obtain ⟨r,q,ho,hr⟩ := observe h
  exact FinishObservation.last_state ho hr n lo hi hn

theorem short_bytes (m : MemoryState) (p : Pointer) (h : Core.SmallRange m p 224)
    (pending : Bytes) (total : Nat) (lo hi : Word) (hn : pending.length < 112)
    (hp : sourceReadBytes m p pending.length = pending)
    (hcount : hi ++ lo = BitVec.ofNat 128 (8*total)) :
    Core.readBytes (lastMemory (markerMemory m p pending.length) p (pending.length+1) lo hi) p 128 =
      onlyPaddingBlock pending total := by
  rw [readBytes_sourceReadBytes _ _ _ ((last_range (marker_range h pending.length) _ lo hi).mono (by decide))]
  obtain ⟨r,q,ho,hr⟩ := observe (h.mono (by decide : 128 ≤ 224))
  exact only_padding_bytes ho hr pending total lo hi hn hp hcount

theorem first_bytes (m : MemoryState) (p : Pointer) (h : Core.SmallRange m p 224)
    (pending : Bytes) (hn : pending.length < 128)
    (hp : sourceReadBytes m p pending.length = pending) :
    Core.readBytes (longMemory (markerMemory m p pending.length) p pending.length) p 128 =
      firstPaddingBlock pending := by
  rw [readBytes_sourceReadBytes _ _ _ ((long_range (marker_range h pending.length) _).mono (by decide))]
  obtain ⟨r,q,ho,hr⟩ := observe (h.mono (by decide : 128 ≤ 224))
  exact first_padding_bytes ho hr pending hn hp

theorem last_bytes (m : MemoryState) (p : Pointer) (h : Core.SmallRange m p 224)
    (total : Nat) (lo hi : Word) (hcount : hi ++ lo = BitVec.ofNat 128 (8*total)) :
    Core.readBytes (lastMemory m p 0 lo hi) p 128 = lastPaddingBlock total := by
  rw [readBytes_sourceReadBytes _ _ _ ((last_range h 0 lo hi).mono (by decide))]
  obtain ⟨r,q,ho,hr⟩ := observe (h.mono (by decide : 128 ≤ 224))
  exact last_padding_bytes ho hr total lo hi hcount

theorem core_result_state (before after : GlobalState) (p : Pointer)
    (hr : Core.SmallRange before.mem p 224)
    (he : ∀ b, after.mem.live? b = (before.mem.splice (p.withOffset 128#64)
      (Core.result before (p.withOffset 128#64) p 1#64)).live? b) :
    pack (sourceReadState after.mem p) =
      Spec.run (pack (sourceReadState before.mem p)) (Core.readBytes before.mem p 128) := by
  have hr' : Core.SmallRange after.mem p 224 := (hr.splice _ _).of_live_eq (he _)
  rw [packed_state _ _ hr', Core.readBits_of_live_eq (he _), Core.readBits_splice_self _
    (show Fits before.mem (p.withOffset 128#64) 512 from (hr.add (by decide : 128+64 ≤ 224)).fits)]
  simp only [Core.result, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.mul_one, ← packed_state _ _ hr]

theorem output_serialized (m : MemoryState) (p o : Pointer)
    (ho : Core.SmallRange m o 64) (hne : o.id ≠ p.id) :
    sourceRead (outputMemory m p o) o 512 = serialize (pack (sourceReadState m p)) := by
  obtain ⟨r,q,hobs,hr⟩ := observe ho
  exact output_word m p o r q hobs hr hne

end FinishDigest
end Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource
