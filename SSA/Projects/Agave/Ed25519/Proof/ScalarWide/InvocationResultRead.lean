import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.InvocationTailState

/-! Derive serializer loads from actual result stores through all cleanup writes. -/
namespace Agave.Ed25519.Verifier.Execution.ScalarWide
open LeanMLIR.RIR

theorem resultState_read (g : Globals) (state : GlobalState) (input : Pointer)
    (bytes : BitVec 512) (i : Fin 5) :
    (resultState g state input bytes).mem.readAt (resultSlots state i) 64 =
      finalWords g state bytes i := by
  have hf0 := (bothCallState_range g state input (slot state 19) bytes 8
    (startup_slot_range state ⟨19, by decide⟩)).fits
  have hf1 := (bothCallState_range g state input (slot state 20) bytes 8
    (startup_slot_range state ⟨20, by decide⟩)).fits
  have hf2 := (bothCallState_range g state input (slot state 21) bytes 8
    (startup_slot_range state ⟨21, by decide⟩)).fits
  have hf3 := (bothCallState_range g state input (slot state 22) bytes 8
    (startup_slot_range state ⟨22, by decide⟩)).fits
  have hf4 := (bothCallState_range g state input (slot state 23) bytes 8
    (startup_slot_range state ⟨23, by decide⟩)).fits
  have hd10 : (Range.of (slot state 20) 64).Disjoint (Range.of (slot state 19) 64) :=
    Range.disjoint_of_id_ne (slot_ne state 20 19 (by decide))
  have hd20 : (Range.of (slot state 21) 64).Disjoint (Range.of (slot state 19) 64) :=
    Range.disjoint_of_id_ne (slot_ne state 21 19 (by decide))
  have hd21 : (Range.of (slot state 21) 64).Disjoint (Range.of (slot state 20) 64) :=
    Range.disjoint_of_id_ne (slot_ne state 21 20 (by decide))
  have hd30 : (Range.of (slot state 22) 64).Disjoint (Range.of (slot state 19) 64) :=
    Range.disjoint_of_id_ne (slot_ne state 22 19 (by decide))
  have hd31 : (Range.of (slot state 22) 64).Disjoint (Range.of (slot state 20) 64) :=
    Range.disjoint_of_id_ne (slot_ne state 22 20 (by decide))
  have hd32 : (Range.of (slot state 22) 64).Disjoint (Range.of (slot state 21) 64) :=
    Range.disjoint_of_id_ne (slot_ne state 22 21 (by decide))
  have hd40 : (Range.of (slot state 23) 64).Disjoint (Range.of (slot state 19) 64) :=
    Range.disjoint_of_id_ne (slot_ne state 23 19 (by decide))
  have hd41 : (Range.of (slot state 23) 64).Disjoint (Range.of (slot state 20) 64) :=
    Range.disjoint_of_id_ne (slot_ne state 23 20 (by decide))
  have hd42 : (Range.of (slot state 23) 64).Disjoint (Range.of (slot state 21) 64) :=
    Range.disjoint_of_id_ne (slot_ne state 23 21 (by decide))
  have hd43 : (Range.of (slot state 23) 64).Disjoint (Range.of (slot state 22) 64) :=
    Range.disjoint_of_id_ne (slot_ne state 23 22 (by decide))
  fin_cases i
  · norm_num only [resultState, resultSlotMemory, resultSlots, Fin.val_zero, Fin.val_one, Fin.val_ofNat_lit, Nat.reduceAdd, Nat.reduceMod]
    rw [MemoryState.readAt_storeAt_disjoint hd40, MemoryState.readAt_storeAt_disjoint hd30, MemoryState.readAt_storeAt_disjoint hd20, MemoryState.readAt_storeAt_disjoint hd10]
    exact MemoryState.readAt_storeAt_self hf0 _
  · norm_num only [resultState, resultSlotMemory, resultSlots, Fin.val_zero, Fin.val_one, Fin.val_ofNat_lit, Nat.reduceAdd, Nat.reduceMod]
    rw [MemoryState.readAt_storeAt_disjoint hd41, MemoryState.readAt_storeAt_disjoint hd31, MemoryState.readAt_storeAt_disjoint hd21]
    exact MemoryState.readAt_storeAt_self hf1.storeAt _
  · norm_num only [resultState, resultSlotMemory, resultSlots, Fin.val_zero, Fin.val_one, Fin.val_ofNat_lit, Nat.reduceAdd, Nat.reduceMod]
    rw [MemoryState.readAt_storeAt_disjoint hd42, MemoryState.readAt_storeAt_disjoint hd32]
    exact MemoryState.readAt_storeAt_self hf2.storeAt.storeAt _
  · norm_num only [resultState, resultSlotMemory, resultSlots, Fin.val_zero, Fin.val_one, Fin.val_ofNat_lit, Nat.reduceAdd, Nat.reduceMod]
    rw [MemoryState.readAt_storeAt_disjoint hd43]
    exact MemoryState.readAt_storeAt_self hf3.storeAt.storeAt.storeAt _
  · norm_num only [resultState, resultSlotMemory, resultSlots, Fin.val_zero, Fin.val_one, Fin.val_ofNat_lit, Nat.reduceAdd, Nat.reduceMod]
    exact MemoryState.readAt_storeAt_self hf4.storeAt.storeAt.storeAt.storeAt _

theorem inputCleanState_read (g : Globals) (state : GlobalState) (input : Pointer)
    (bytes : BitVec 512) (i : Fin 5) :
    (inputCleanState g state input bytes).mem.readAt (resultSlots state i) 64 =
      finalWords g state bytes i := by
  have hs (j : Fin 8) : (inputSlots state j).id ≠ (resultSlots state i).id := by
    apply slot_ne
    have := j.isLt
    have := i.isLt
    omega
  have hn5 : (slot state 5).id ≠ (resultSlots state i).id := by
    apply slot_ne
    have := i.isLt
    omega
  have hn6 : (slot state 6).id ≠ (resultSlots state i).id := by
    apply slot_ne
    have := i.isLt
    omega
  have hn9 : (slot state 9).id ≠ (resultSlots state i).id := by
    apply slot_ne
    have := i.isLt
    omega
  have hn10 : (slot state 10).id ≠ (resultSlots state i).id := by
    apply slot_ne
    have := i.isLt
    omega
  simp only [inputCleanState, inputCleanupMemory,
    MemoryState.readAt_storeAt_disjoint (Range.disjoint_of_id_ne (hs _)),
    MemoryState.readAt_storeAt_disjoint (Range.disjoint_of_id_ne hn5),
    MemoryState.readAt_storeAt_disjoint (Range.disjoint_of_id_ne hn6),
    MemoryState.readAt_storeAt_disjoint (Range.disjoint_of_id_ne hn9),
    MemoryState.readAt_storeAt_disjoint (Range.disjoint_of_id_ne hn10)]
  exact resultState_read g state input bytes i

end Agave.Ed25519.Verifier.Execution.ScalarWide
