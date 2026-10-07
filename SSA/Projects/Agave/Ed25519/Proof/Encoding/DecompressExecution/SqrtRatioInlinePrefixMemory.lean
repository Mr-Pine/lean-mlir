import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.SqrtRatioInlinePrefixEntry

/-! Allocation facts for the actual sqrt entry: all scratch ranges are live,
mutually distinct and private; arbitrary caller field reads remain unchanged. -/
namespace Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline
open LeanMLIR.RIR
open Reduce64.Execution (SmallRange)
open SerialFieldMul

theorem allocate_slot_live (s : GlobalState) (hwf : s.WF) (ns : List Nat)
    (i : Nat) (hi : i < ns.length) (hbound : ns[i] < 2 ^ 63) :
    SmallRange (allocate s ns).mem (allocate s (ns.take i)).allocaPtr ns[i] := by
  induction ns generalizing s i with
  | nil => simp only [List.length_nil] at hi; omega
  | cons n ns ih =>
    cases i with
    | zero =>
      exact allocate_live (s.alloca n) hwf.alloca ns
        (by
          refine ⟨⟨n, 0⟩, ?_, hbound, ?_⟩
          · simp [allocate, GlobalState.alloca, GlobalState.allocaPtr, MemoryState.getElem?_eq]
          · simp [GlobalState.allocaPtr])
    | succ i =>
      exact ih (s.alloca n) hwf.alloca i (by simpa using hi) hbound

theorem slot_live (s : GlobalState) (hwf : s.WF) (i : Fin 22) :
    SmallRange (allocate s allocationSizes).mem (slot s i)
      (allocationSizes[i.val]'(by exact i.isLt)) := by
  exact allocate_slot_live s hwf allocationSizes i i.isLt
    (by fin_cases i <;> decide)

theorem slot_id (s : GlobalState) (i : Fin 22) :
    (slot s i).id.id = s.alloc.nextFreeBlock + i.val := by
  simp only [slot, GlobalState.allocaPtr_id_id, allocate_counter, List.length_take]
  rw [Nat.min_eq_left (by exact Nat.le_of_lt i.isLt)]

theorem slot_private (s : GlobalState) (i : Fin 22) :
    s.alloc.nextFreeBlock ≤ (slot s i).id.id := by
  rw [slot_id]
  omega

theorem slot_distinct (s : GlobalState) (i j : Fin 22) (h : i ≠ j) :
    (slot s i).id ≠ (slot s j).id := by
  intro heq
  have hn := congrArg BlockId.id heq
  rw [slot_id, slot_id] at hn
  exact h (Fin.ext (Nat.add_left_cancel hn))

theorem slot_caller_disjoint (s : GlobalState) (hwf : s.WF)
    (i : Fin 22) (p : Pointer) (h : SmallRange s.mem p bytes) :
    (slot s i).id ≠ p.id := by
  intro heq
  have hold := hwf.lt h.fits.mem
  have hn := congrArg BlockId.id heq
  rw [slot_id] at hn
  omega

theorem entry_live (g : Globals) (E : ⟪program.Γ⟫) (s : GlobalState)
    (hwf : s.WF) (p : Pointer) (h : SmallRange s.mem p bytes) :
    SmallRange (entryResult g E s).2.mem p bytes := by
  rw [entry_state]
  exact allocate_live s hwf _ h

theorem entry_readLimbs (g : Globals) (E : ⟪program.Γ⟫) (s : GlobalState)
    (hwf : s.WF) (p : Pointer) (h : SmallRange s.mem p 40) :
    readLimbs (entryResult g E s).2 p = readLimbs s p := by
  rw [entry_state]
  funext i
  exact allocate_read s hwf allocationSizes
    (h.fits_add (k := 8 * i.val) (count := 8) (by omega))

end Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline
