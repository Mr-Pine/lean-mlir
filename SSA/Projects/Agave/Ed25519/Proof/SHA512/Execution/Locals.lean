import SSA.Projects.Agave.Ed25519.Proof.SHA512.Execution.Allocation
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Execution.PaddingReadback

namespace Agave.Ed25519.Verifier.Execution.SHA512Finalization

open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Challenge
open Agave.Ed25519.Bridge.Challenge

variable {entry before after : GlobalState} {m : MemoryState}
  {dst : Pointer} {w n : Nat} {value : BitVec w}

set_option maxRecDepth 20000
set_option maxHeartbeats 1600000

/-- Liveness of precisely the local allocations in the imported body. -/
structure LocalsLive (entry : GlobalState) (m : MemoryState) : Prop where
  block0 : SmallRange m (slot entry 0) 128
  block1 : SmallRange m (slot entry 1) 128
  block2 : SmallRange m (slot entry 2) 128
  buffer : SmallRange m (slot entry 3) 128
  digest : SmallRange m (slot entry 4) 64
  context : SmallRange m (slot entry 5) 208
  scratch : ∀ i : Fin 64, SmallRange m (slot entry (i.val + 6)) 1

theorem LocalsLive.storeAt (h : LocalsLive entry m) (dst : Pointer) (value : BitVec w) :
    LocalsLive entry (m.storeAt dst value) :=
  ⟨h.block0.storeAt _ _, h.block1.storeAt _ _, h.block2.storeAt _ _,
    h.buffer.storeAt _ _, h.digest.storeAt _ _, h.context.storeAt _ _,
    fun i => (h.scratch i).storeAt _ _⟩

theorem LocalsLive.effect (h : LocalsLive entry before.mem)
    (he : StoreEffect before after dst value) : LocalsLive entry after.mem := by
  rw [he.memory]
  exact h.storeAt _ _

theorem locals_allocated (s : GlobalState) (hwf : s.WF) :
    LocalsLive s (allocateSlots s slotSizes).mem := by
  constructor
  · exact allocateSlots_slot_live slotSizes hwf (i := 0) (by decide) (by decide)
  · exact allocateSlots_slot_live slotSizes hwf (i := 1) (by decide) (by decide)
  · exact allocateSlots_slot_live slotSizes hwf (i := 2) (by decide) (by decide)
  · exact allocateSlots_slot_live slotSizes hwf (i := 3) (by decide) (by decide)
  · exact allocateSlots_slot_live slotSizes hwf (i := 4) (by decide) (by decide)
  · exact allocateSlots_slot_live slotSizes hwf (i := 5) (by decide) (by decide)
  · intro i
    have hi : i.val + 6 < slotSizes.length := by simp; omega
    have hsize : slotSizes[i.val + 6]'hi = 1 := by
      have hg := List.getElem_append_right (as := [128, 128, 128, 128, 64, 208])
        (bs := List.replicate 64 1) (i := i.val + 6)
        (by simp only [List.length_cons, List.length_nil]; omega)
        (h₂ := by simpa only [slotSizes] using hi)
      exact hg.trans (List.getElem_replicate _)
    simpa only [hsize, slot] using
      allocateSlots_slot_live slotSizes hwf hi (by rw [hsize]; decide)

theorem slot_id (s : GlobalState) (i : Nat) (hi : i ≤ 70) :
    (slot s i).id.id = s.alloc.nextFreeBlock + i := by
  simp [slot, GlobalState.allocaPtr, allocateSlots_counter, List.length_take,
    Nat.min_eq_left hi]

theorem slot_internal (s : GlobalState) (i : Nat) (hi : i ≤ 70) :
    s.alloc.nextFreeBlock ≤ (slot s i).id.id := by rw [slot_id s i hi]; omega

theorem slot_ne (s : GlobalState) (i j : Nat) (hi : i ≤ 70) (hj : j ≤ 70) (hne : i ≠ j) :
    (slot s i).id ≠ (slot s j).id := by
  intro h
  have heq := congrArg BlockId.id h
  rw [slot_id s i hi, slot_id s j hj] at heq
  omega

theorem slot_ne_caller (s : GlobalState) (i : Nat) (hi : i ≤ 70) (ptr : Pointer)
    (hwf : s.WF) (hptr : SmallRange s.mem ptr n) : (slot s i).id ≠ ptr.id := by
  intro h
  have hlo := hwf.lt hptr.fits.mem
  have heq := congrArg BlockId.id h
  rw [slot_id s i hi] at heq
  omega

theorem allocated_context (s : GlobalState) (src : Pointer) (sha : Sha512Model)
    (completed pending : Bytes) (hwf : s.WF)
    (hctx : ContextRepresents sha s.mem src completed pending) :
    ContextRepresents sha (allocateSlots s slotSizes).mem src completed pending := by
  refine ⟨allocateSlots_live _ hwf hctx.live, hctx.completedWhole, hctx.pendingBound,
    ?_, ?_, ?_, ?_⟩
  · calc
      readBytes (allocateSlots s slotSizes).mem src pending.length =
          readBytes s.mem src pending.length := by
        unfold readBytes
        congr 1
        funext i
        exact allocateSlots_read _ hwf
          (smallRange_add hctx.live (k := i.val) (count := 1)
            (by have := i.isLt; have := hctx.pendingBound; omega)) 8
      _ = pending := hctx.pendingBytes
  · exact (congrArg BitVec.toNat (allocateSlots_read slotSizes hwf
      (smallRange_add hctx.live (k := 127) (count := 1) (by decide)) 8)).trans hctx.pendingCount
  · exact (allocateSlots_read slotSizes hwf
      (smallRange_add hctx.live (k := 128) (count := 64) (by decide)) 512).trans hctx.chaining
  · exact (congrArg BitVec.toNat (allocateSlots_read slotSizes hwf
      (smallRange_add hctx.live (k := 192) (count := 16) (by decide)) 128)).trans hctx.blockCount

def entryState (s : GlobalState) (src : Pointer) (count : BitVec 8) : GlobalState :=
  paddingState (allocateSlots s slotSizes) src (slot s 5) (slot s 3) count

theorem entryState_wf (s : GlobalState) (src : Pointer) (count : BitVec 8) (hwf : s.WF) :
    (entryState s src count).WF := (allocateSlots_wf _ hwf).storeAt.storeAt.storeAt.storeAt

theorem entryState_locals (s : GlobalState) (src : Pointer) (count : BitVec 8) (hwf : s.WF) :
    LocalsLive s (entryState s src count).mem :=
  ((((locals_allocated s hwf).storeAt _ _).storeAt _ _).storeAt _ _).storeAt _ _

theorem entryState_live (s : GlobalState) (src ptr : Pointer) (count : BitVec 8)
    (hwf : s.WF) (hptr : SmallRange s.mem ptr n) :
    SmallRange (entryState s src count).mem ptr n :=
  ((((allocateSlots_live _ hwf hptr).storeAt _ _).storeAt _ _).storeAt _ _).storeAt _ _

theorem entryState_frame (s : GlobalState) (src : Pointer) (count : BitVec 8) (hwf : s.WF) :
    (entryState s src count).mem.eraseFrom s.alloc.nextFreeBlock = s.mem := by
  have hc := slot_internal s 5 (by decide)
  have hb := slot_internal s 3 (by decide)
  exact erase_internal_store _ _ _ _ _
    (erase_internal_store _ _ _ _ _
      (erase_internal_store _ _ _ _ _
        (erase_internal_store _ _ _ _ _ (allocateSlots_frame _ s hwf) hc) hb) hb) hb

theorem entryState_counter (s : GlobalState) (src : Pointer) (count : BitVec 8) :
    (entryState s src count).alloc.nextFreeBlock = s.alloc.nextFreeBlock + 70 := by
  change (allocateSlots s slotSizes).alloc.nextFreeBlock = _
  simp

theorem entryState_chaining (s : GlobalState) (src : Pointer) (count : BitVec 8)
    (hwf : s.WF) (hs : SmallRange s.mem src 208) :
    (entryState s src count).mem.readAt ((slot s 5).add 128#64) 512 =
      s.mem.readAt (src.add 128#64) 512 := by
  have hne := slot_ne s 3 5 (by decide) (by decide) (by decide)
  dsimp only [entryState, paddingState, paddingCopied, paddingCleared, cloned]
  rw [readAt_storeAt_of_id_ne _ ((slot s 3).add (count.setWidth 64))
      ((slot s 5).add 128#64) _ _ hne,
    readAt_storeAt_of_id_ne _ (slot s 3) ((slot s 5).add 128#64) _ _ hne,
    readAt_storeAt_of_id_ne _ (slot s 3) ((slot s 5).add 128#64) _ _ hne]
  rw [copy_readAt_offset _ src (slot s 5) 208 128 64
    (allocateSlots_live _ hwf hs) (locals_allocated s hwf).context (by decide)]
  exact allocateSlots_read _ hwf (smallRange_add hs (k := 128) (count := 64) (by decide)) 512

end Agave.Ed25519.Verifier.Execution.SHA512Finalization
