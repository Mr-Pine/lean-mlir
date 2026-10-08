import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMAppendMessageResult
import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSourceCoreBlockBytes
import SSA.Projects.Agave.Ed25519.Proof.SHA512.ByteOrder

namespace Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource
open LeanMLIR SLLVM Firedancer
namespace MessageExecution
set_option maxRecDepth 10000
set_option maxHeartbeats 400000
attribute [local irreducible] core append Core.result sourceRead

private theorem readBits_sourceRead (m : MemoryState) (p : Pointer) (w : Nat) :
    Core.readBits m p w = sourceRead m p w := by
  unfold Core.readBits readWord? sourceRead
  cases m.live? p.id <;> rfl

/-- Equality of the bounded input byte window determines every contained wide read. -/
theorem sourceRead_window_congr {m t : MemoryState} {data other : Pointer} {n : Nat}
    (hm : Core.SmallRange m data n) (ht : Core.SmallRange t other n)
    (he : sourceReadBytes m data n = sourceReadBytes t other n)
    (off : BitVec 64) (len : Nat) (hb : off.toNat + len ≤ n) :
    sourceRead m (data.withOffset off) (8*len) =
      sourceRead t (other.withOffset off) (8*len) := by
  have hr (r : MemoryState) (p : Pointer) (h : Core.SmallRange r p n) :
      Core.readBytes r p n = sourceReadBytes r p n := by
    rw [Core.readBytes_eq_ofFn r p n h]
    simp only [sourceReadBytes, readBits_sourceRead]
  have hw : Core.readBits m data (n*8) = Core.readBits t other (n*8) := by
    apply Agave.Ed25519.SHA512.bytesOf_injective
    change Core.readBytes m data n = Core.readBytes t other n
    rw [hr m data hm, hr t other ht, he]
  have h1 := Core.readBits_add_extract m data n off.toNat (8*len) hm (by omega) (by omega)
  have h2 := Core.readBits_add_extract t other n off.toNat (8*len) ht (by omega) (by omega)
  simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq, readBits_sourceRead] using h1.trans ((congrArg
    (fun v : BitVec (n*8) => v.extractLsb' (8*off.toNat) (8*len)) hw).trans h2.symm)

/-- Equal context allocations, addressed at equal offsets. -/
structure ContextEq (m t : MemoryState) (p q : Pointer) : Prop where
  offset : p.offset = q.offset
  live : m.live? p.id = t.live? q.id

namespace ContextEq

theorem read {m t : MemoryState} {p q : Pointer} (h : ContextEq m t p q)
    (off : BitVec 64) (w : Nat) :
    sourceRead m (p.withOffset off) w = sourceRead t (q.withOffset off) w := by
  simp only [sourceRead, Pointer.withOffset, Pointer.offsetInBits, h.live, h.offset]

theorem store {m t : MemoryState} {p q : Pointer} (h : ContextEq m t p q)
    (off : BitVec 64) (x : BitVec w) :
    ContextEq (m.splice (p.withOffset off) x) (t.splice (q.withOffset off) x) p q := by
  refine ⟨h.offset, ?_⟩
  cases hb : t.live? q.id with
  | none =>
    exact (splicedDead (p := p.withOffset off) (x := x) (h.live.trans hb)).trans
      (splicedDead (p := q.withOffset off) (x := x) hb).symm
  | some b =>
    have h1 := splicedLive m (p.withOffset off) b (h.live.trans hb) x
    have h2 := splicedLive t (q.withOffset off) b hb x
    have ho : (p.withOffset off).offsetInBits = (q.withOffset off).offsetInBits := by
      simp only [Pointer.withOffset, Pointer.offsetInBits, h.offset]
    rw [ho] at h1
    exact h1.trans h2.symm

end ContextEq

/-- Every wide read contained in the input window agrees. -/
def WindowEq (m t : MemoryState) (data other : Pointer) (n : Nat) : Prop :=
  ∀ (off : BitVec 64) (len : Nat), off.toNat + len ≤ n →
    sourceRead m (data.withOffset off) (8*len) =
      sourceRead t (other.withOffset off) (8*len)

private structure Rel (m t : MemoryState) (p q data other : Pointer) (n : Nat) : Prop where
  context : ContextEq m t p q
  input : WindowEq m t data other n

private theorem Rel.store {m t : MemoryState} {p q data other : Pointer} {n : Nat}
    (h : Rel m t p q data other n) (hs : p.id ≠ data.id) (ht : q.id ≠ other.id)
    (off : BitVec 64) (x : BitVec w) :
    Rel (m.splice (p.withOffset off) x) (t.splice (q.withOffset off) x) p q data other n := by
  refine ⟨h.context.store off x, ?_⟩
  intro k len hk
  exact (sourceRead_of_live_eq (p := data.withOffset k)
    (live?_splice_ne (p := p.withOffset off) (x := x) hs)).trans
    ((h.input k len hk).trans (sourceRead_of_live_eq (p := other.withOffset k)
      (live?_splice_ne (p := q.withOffset off) (x := x) ht)).symm)

private theorem Rel.copy {m t : MemoryState} {p q data other : Pointer} {n : Nat}
    (h : Rel m t p q data other n) (hs : p.id ≠ data.id) (ht : q.id ≠ other.id)
    (dst src : BitVec 64) (len : Nat) (hb : src.toNat + len ≤ n) :
    Rel (m.splice (p.withOffset dst) (sourceRead m (data.withOffset src) (8*len)))
      (t.splice (q.withOffset dst) (sourceRead t (other.withOffset src) (8*len)))
      p q data other n := by
  rw [h.input src len hb]
  exact h.store hs ht dst _

private def counterMemory (m : MemoryState) (p : Pointer) (n : BitVec 64) : MemoryState :=
  let lo := sourceRead m (p.withOffset 208#64) 64
  let hi := sourceRead m (p.withOffset 216#64) 64
  let nextLo := lo + (n <<< 3)
  let nextHi := (hi + (n >>> 61)) + (if nextLo <ᵤ lo then 1#64 else 0#64)
  (m.splice (p.withOffset 208#64) nextLo).splice (p.withOffset 216#64) nextHi

private theorem Rel.counter {m t : MemoryState} {p q data other : Pointer} {N : Nat}
    (h : Rel m t p q data other N) (hs : p.id ≠ data.id) (ht : q.id ≠ other.id)
    (n : BitVec 64) :
    Rel (counterMemory m p n) (counterMemory t q n) p q data other N := by
  unfold counterMemory
  rw [h.context.read 208#64 64, h.context.read 216#64 64]
  exact (h.store hs ht _ _).store hs ht _ _

private theorem Rel.filled {m t : MemoryState} {p q data other : Pointer} {n : BitVec 64}
    (h : Rel m t p q data other n.toNat) (hs : p.id ≠ data.id) (ht : q.id ≠ other.id)
    (hn : 64 ≤ n.toNat) :
    Rel (appendMessageFilledMemory m p data n) (appendMessageFilledMemory t q other n)
      p q data other n.toNat := by
  have hc := (h.counter hs ht n).copy hs ht 64#64 0#64 64 (by simpa using hn)
  simpa only [appendMessageFilledMemory, counterMemory, Pointer.withOffset, BitVec.add_zero] using hc

private theorem Rel.short {m t : MemoryState} {p q data other : Pointer} {n : BitVec 64}
    (h : Rel m t p q data other n.toNat) (hs : p.id ≠ data.id) (ht : q.id ≠ other.id) :
    Rel (appendMessageShortMemory m p data n) (appendMessageShortMemory t q other n)
      p q data other n.toNat := by
  have hc := ((h.counter hs ht n).copy hs ht 64#64 0#64 n.toNat (by simp)).store
    hs ht 200#64 (64#64 + n)
  simpa only [appendMessageShortMemory, counterMemory, Pointer.withOffset, BitVec.add_zero,
    Nat.mul_comm] using hc

private theorem Rel.core {s t : GlobalState} {p q data other : Pointer} {n : Nat}
    (h : Rel s.mem t.mem p q data other n) (hs : p.id ≠ data.id) (ht : q.id ≠ other.id)
    (src otherSrc : Pointer) (count : BitVec 64)
    (hi : Core.readBytes s.mem src (128*count.toNat) =
      Core.readBytes t.mem otherSrc (128*count.toNat)) :
    Rel (coreState s p src count).mem (coreState t q otherSrc count).mem p q data other n := by
  have hc : Core.result s (p.withOffset 128#64) src count =
      Core.result t (q.withOffset 128#64) otherSrc count := by
    unfold Core.result
    rw [readBits_sourceRead, readBits_sourceRead, h.context.read, hi]
  unfold coreState
  rw [hc]
  exact h.store hs ht 128#64 _

private theorem ContextEq.coreBytes {m t : MemoryState} {p q : Pointer}
    (h : ContextEq m t p q) (len : Nat) : Core.readBytes m p len = Core.readBytes t q len := by
  unfold Core.readBytes
  rw [readBits_sourceRead, readBits_sourceRead]
  congr 1
  simpa only [Pointer.withOffset, BitVec.add_zero] using h.read 0#64 (len*8)

private theorem WindowEq.coreBytes {m t : MemoryState} {data other : Pointer} {n : Nat}
    (h : WindowEq m t data other n) (off : BitVec 64) (len : Nat) (hb : off.toNat+len ≤ n) :
    Core.readBytes m (data.withOffset off) len = Core.readBytes t (other.withOffset off) len := by
  unfold Core.readBytes
  rw [readBits_sourceRead, readBits_sourceRead]
  congr 1
  rw [Nat.mul_comm len 8]
  exact h off len hb

private theorem Rel.tail {m t : MemoryState} {p q data other : Pointer} {N : Nat}
    (h : Rel m t p q data other N) (hs : p.id ≠ data.id) (ht : q.id ≠ other.id)
    (off size : BitVec 64) (hb : off.toNat+size.toNat ≤ N) :
    Rel (appendMessageTailMemory m p (data.withOffset off) size)
      (appendMessageTailMemory t q (other.withOffset off) size) p q data other N := by
  have hc := ((h.store hs ht 200#64 0#64).copy hs ht 0#64 off size.toNat hb).store
    hs ht 200#64 size
  simpa only [appendMessageTailMemory, Pointer.withOffset, BitVec.add_zero, Nat.mul_comm] using hc

private theorem Rel.directTail {m t : MemoryState} {p q data other : Pointer} {n : BitVec 64}
    (h : Rel m t p q data other n.toNat) (hs : p.id ≠ data.id) (ht : q.id ≠ other.id)
    (hn : 64 ≤ n.toNat) :
    Rel (appendMessageDirectTailMemory m p (data.withOffset 64#64) (n-64#64))
      (appendMessageDirectTailMemory t q (other.withOffset 64#64) (n-64#64))
      p q data other n.toNat := by
  dsimp only [appendMessageDirectTailMemory]
  by_cases hz : ((n-64#64) &&& 127#64) = 0#64
  · simpa only [hz, ite_true] using h
  · simp only [hz, ite_false]
    have hr : (n-64#64).toNat = n.toNat-64 := BitVec.toNat_sub_of_le hn
    have ha := aligned_plus_remainder (n-64#64)
    have hb : (64#64 + ((n-64#64) &&& 18446744073709551488#64)).toNat +
        ((n-64#64) &&& 127#64).toNat ≤ n.toNat := by
      rw [BitVec.toNat_add]
      change (64 + ((n-64#64) &&& 18446744073709551488#64).toNat) % 2^64 +
        ((n-64#64) &&& 127#64).toNat ≤ n.toNat
      have hlt := n.isLt
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
    have hc := (h.copy hs ht 0#64
      (64#64 + ((n-64#64) &&& 18446744073709551488#64))
      ((n-64#64) &&& 127#64).toNat hb).store hs ht 200#64 ((n-64#64) &&& 127#64)
    simpa only [Pointer.withOffset, BitVec.add_zero, BitVec.add_assoc, Nat.mul_comm] using hc

attribute [local irreducible] appendMessageShortMemory appendMessageFilledMemory
  appendMessageTailMemory appendMessageDirectTailMemory coreState

/-- The third append's complete resulting context allocation depends only on
its incoming context block and the bounded input bytes, independently of either
allocation's identity and of all unrelated caller memory. -/
theorem resultState_context_congr {s t : GlobalState} {p q data other : Pointer} (n : BitVec 64)
    (hoff : p.offset = q.offset) (hc : s.mem.live? p.id = t.mem.live? q.id)
    (hs : p.id ≠ data.id) (ht : q.id ≠ other.id)
    (hi : Core.SmallRange s.mem data n.toNat) (hj : Core.SmallRange t.mem other n.toNat)
    (hb : sourceReadBytes s.mem data n.toNat = sourceReadBytes t.mem other n.toNat) :
    (resultState s p data n).mem.live? p.id = (resultState t q other n).mem.live? q.id := by
  have h : Rel s.mem t.mem p q data other n.toNat :=
    ⟨⟨hoff, hc⟩, sourceRead_window_congr hi hj hb⟩
  by_cases hz : n = 0#64
  · simpa only [resultState, hz, ite_true] using hc
  by_cases hshort : n.toNat < 64
  · simpa only [resultState, hz, hshort, ite_false, ite_true] using (h.short hs ht).context.live
  have hn : 64 ≤ n.toNat := by omega
  let sf : GlobalState := {s with mem := appendMessageFilledMemory s.mem p data n}
  let tf : GlobalState := {t with mem := appendMessageFilledMemory t.mem q other n}
  have hfilled : Rel sf.mem tf.mem p q data other n.toNat := h.filled hs ht hn
  have hfirst : Rel (coreState sf p p 1#64).mem (coreState tf q q 1#64).mem
      p q data other n.toNat :=
    hfilled.core hs ht p q 1#64 (hfilled.context.coreBytes _)
  by_cases he : n = 64#64
  · simpa only [resultState, ite_eq_right hz, ite_eq_right hshort, ite_eq_left he, sf, tf] using
      (hfirst.store hs ht 200#64 0#64).context.live
  have hr : (n-64#64).toNat = n.toNat-64 := BitVec.toNat_sub_of_le hn
  by_cases htail : n.toNat < 192
  · have hbnd : (64#64).toNat + (n-64#64).toNat ≤ n.toNat := by rw [hr]; simp; omega
    simpa only [resultState, hz, hshort, he, htail, ite_false, ite_true, sf, tf] using
      (hfirst.tail hs ht 64#64 (n-64#64) hbnd).context.live
  let fs := coreState sf p p 1#64
  let ft := coreState tf q q 1#64
  let sr : GlobalState := {fs with mem := fs.mem.splice (p.withOffset 200#64) (0#64)}
  let tr : GlobalState := {ft with mem := ft.mem.splice (q.withOffset 200#64) (0#64)}
  have hreset : Rel sr.mem tr.mem p q data other n.toNat := hfirst.store hs ht 200#64 0#64
  have hbulkBound : (64#64).toNat + 128*((n-64#64) >>> (7 : Nat)).toNat ≤ n.toNat := by
    simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, hr]
    change 64 + 128*((n.toNat-64)/128) ≤ n.toNat
    omega
  have hbulk := hreset.core hs ht (data.withOffset 64#64) (other.withOffset 64#64)
    ((n-64#64) >>> (7 : Nat)) (hreset.input.coreBytes 64#64 _ hbulkBound)
  simpa only [resultState, hz, hshort, he, htail, ite_false, sf, tf, sr, tr, fs, ft] using
    (hbulk.directTail hs ht hn).context.live

end MessageExecution
end Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource
