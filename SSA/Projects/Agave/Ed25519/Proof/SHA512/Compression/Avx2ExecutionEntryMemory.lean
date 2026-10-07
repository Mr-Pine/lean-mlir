import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionEntry
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionInitialMemory
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Execution.Frame

/-! Heap facts for the three actual bb0 allocations and the initial scratch stores. -/
namespace Agave.Ed25519.SHA512.Execution.Avx2

open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.Bridge.Challenge
open Agave.Ed25519.Verifier.Execution.SHA512Finalization

private theorem entryState_allocateSlots (mem : GlobalState) :
    entryState mem = allocateSlots mem [128, 640, 128] := rfl

theorem entryState_wf {mem : GlobalState} (hwf : mem.WF) : (entryState mem).WF :=
  allocateSlots_wf [128, 640, 128] hwf

theorem entryState_live {mem : GlobalState} {p : Pointer} {bytes : Nat}
    (hwf : mem.WF) (h : SmallRange mem.mem p bytes) :
    SmallRange (entryState mem).mem p bytes :=
  allocateSlots_live [128, 640, 128] hwf h

/-- All widths at an existing live allocation retain their exact original bits. -/
theorem entryState_read {mem : GlobalState} {p : Pointer} {bytes : Nat}
    (hwf : mem.WF) (h : SmallRange mem.mem p bytes) (width : Nat) :
    (entryState mem).mem.readAt p width = mem.mem.readAt p width :=
  allocateSlots_read [128, 640, 128] hwf h width

theorem entryState_frame (mem : GlobalState) (hwf : mem.WF) :
    (entryState mem).mem.eraseFrom mem.alloc.nextFreeBlock = mem.mem :=
  allocateSlots_frame [128, 640, 128] mem hwf

theorem entryState_frame_le (mem : GlobalState) (mark : Nat)
    (hmark : mark ≤ mem.alloc.nextFreeBlock) :
    (entryState mem).mem.eraseFrom mark = mem.mem.eraseFrom mark :=
  allocateSlots_frame_le [128, 640, 128] mem hmark

theorem entryState_counter (mem : GlobalState) :
    (entryState mem).alloc.nextFreeBlock = mem.alloc.nextFreeBlock + 3 :=
  allocateSlots_counter [128, 640, 128] mem

theorem entry_scratch_live (mem : GlobalState) (hwf : mem.WF) :
    SmallRange (entryState mem).mem mem.allocaPtr 128 := by
  exact allocateSlots_slot_live [128, 640, 128] hwf (i := 0) (by decide) (by decide)

theorem entry_cache_live (mem : GlobalState) (hwf : mem.WF) :
    SmallRange (entryState mem).mem (mem.alloca 128).allocaPtr 640 := by
  exact allocateSlots_slot_live [128, 640, 128] hwf (i := 1) (by decide) (by decide)

theorem entry_buffer_live (mem : GlobalState) (hwf : mem.WF) :
    SmallRange (entryState mem).mem ((mem.alloca 128).alloca 640).allocaPtr 128 := by
  exact allocateSlots_slot_live [128, 640, 128] hwf (i := 2) (by decide) (by decide)

/-- Every old live pointer predates all three fresh allocation identities. -/
theorem entry_slots_ne_old {mem : GlobalState} {p : Pointer} {bytes : Nat}
    (hwf : mem.WF) (h : SmallRange mem.mem p bytes) :
    mem.allocaPtr.id ≠ p.id ∧
      (mem.alloca 128).allocaPtr.id ≠ p.id ∧
      ((mem.alloca 128).alloca 640).allocaPtr.id ≠ p.id := by
  have hlt := hwf.lt h.fits.mem
  refine ⟨?_, ?_, ?_⟩ <;> intro heq <;>
    have hv := congrArg BlockId.id heq <;>
    simp only [GlobalState.allocaPtr, GlobalState.alloca] at hv <;> omega

/-- Whole fresh slots are disjoint from every read at an old live allocation. -/
theorem entry_slots_disjoint_old {mem : GlobalState} {p : Pointer} {bytes : Nat}
    (hwf : mem.WF) (h : SmallRange mem.mem p bytes) (width : Nat) :
    (Range.of mem.allocaPtr 1024).Disjoint (Range.of p width) ∧
      (Range.of (mem.alloca 128).allocaPtr 5120).Disjoint (Range.of p width) ∧
      (Range.of ((mem.alloca 128).alloca 640).allocaPtr 1024).Disjoint (Range.of p width) := by
  obtain ⟨h0, h1, h2⟩ := entry_slots_ne_old hwf h
  exact ⟨Range.disjoint_of_id_ne h0, Range.disjoint_of_id_ne h1,
    Range.disjoint_of_id_ne h2⟩

theorem entry_slots_distinct (mem : GlobalState) :
    mem.allocaPtr.id ≠ (mem.alloca 128).allocaPtr.id ∧
      mem.allocaPtr.id ≠ ((mem.alloca 128).alloca 640).allocaPtr.id ∧
      (mem.alloca 128).allocaPtr.id ≠ ((mem.alloca 128).alloca 640).allocaPtr.id := by
  simp only [GlobalState.allocaPtr, GlobalState.alloca, ne_eq, BlockId.mk.injEq]
  omega

theorem entry_slots_disjoint (mem : GlobalState) :
    (Range.of mem.allocaPtr 1024).Disjoint (Range.of (mem.alloca 128).allocaPtr 5120) ∧
      (Range.of mem.allocaPtr 1024).Disjoint
        (Range.of ((mem.alloca 128).alloca 640).allocaPtr 1024) ∧
      (Range.of (mem.alloca 128).allocaPtr 5120).Disjoint
        (Range.of ((mem.alloca 128).alloca 640).allocaPtr 1024) := by
  obtain ⟨h01, h02, h12⟩ := entry_slots_distinct mem
  exact ⟨Range.disjoint_of_id_ne h01, Range.disjoint_of_id_ne h02,
    Range.disjoint_of_id_ne h12⟩

/-- Every initial scratch store disappears at cleanup of its owning frame. -/
theorem initialScratchStores_erasure (mem : GlobalState) (scratch : Pointer)
    (block : Bytes) (n mark : Nat) (hmark : mark ≤ scratch.id.id) :
    (initialScratchStores mem scratch block n).mem.eraseFrom mark = mem.mem.eraseFrom mark := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [initialScratchStores, pairStoreState, pairScratchStore,
      MemoryState.eraseFrom_storeAt]
    rw [MemoryState.storeAt_eraseFrom_of_le (by exact hmark)]
    exact ih

end Agave.Ed25519.SHA512.Execution.Avx2
