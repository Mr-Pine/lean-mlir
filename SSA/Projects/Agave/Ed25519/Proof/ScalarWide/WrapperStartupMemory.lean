import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.MontgomeryStartupMemory
import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.Linked

/-! The exact 24 heterogeneous outer allocations, with caller preservation and
all scratch provenance and liveness derived from the invocation state. -/
namespace Agave.Ed25519.Verifier.Execution.ScalarWide
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution (SmallRange)

/-- Source alloca indices 5–10 are 40-byte Scalar52 buffers; all others are u64. -/
def slotSize (i : Nat) : Nat := if 5 ≤ i ∧ i < 11 then 40 else 8

def wrapperAllocSteps (state : GlobalState) : Nat → GlobalState
  | 0 => state
  | n + 1 => (wrapperAllocSteps state n).alloca (slotSize n)

def slot (state : GlobalState) (i : Nat) : Pointer :=
  ⟨⟨state.alloc.nextFreeBlock + i⟩, 0⟩

theorem startupState_eq_wrapperAllocSteps (state : GlobalState) :
    startupState state = wrapperAllocSteps state 24 := rfl

theorem wrapperAllocSteps_count (state : GlobalState) (n : Nat) :
    (wrapperAllocSteps state n).alloc.nextFreeBlock = state.alloc.nextFreeBlock + n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change (wrapperAllocSteps state n).alloc.nextFreeBlock + 1 = state.alloc.nextFreeBlock + (n + 1)
      omega

theorem wrapperAllocSteps_ptr (state : GlobalState) (n : Nat) :
    (wrapperAllocSteps state n).allocaPtr = slot state n := by
  simp [slot, GlobalState.allocaPtr, wrapperAllocSteps_count]

theorem wrapperAllocSteps_wf (state : GlobalState) (hwf : state.WF) (n : Nat) :
    (wrapperAllocSteps state n).WF := by
  induction n with
  | zero => exact hwf
  | succ n ih => exact ih.alloca

theorem wrapperAllocSteps_range (state : GlobalState) (hwf : state.WF)
    (q : Pointer) (count : Nat) (h : SmallRange state.mem q count) (n : Nat) :
    SmallRange (wrapperAllocSteps state n).mem q count := by
  induction n with
  | zero => exact h
  | succ n ih =>
      exact ScalarMontgomeryMul.smallRange_alloca _
        (wrapperAllocSteps_wf state hwf n) q count (slotSize n) ih

theorem wrapperAllocSteps_fits (state : GlobalState) (hwf : state.WF)
    (q : Pointer) (width : Nat) (h : Fits state.mem q width) (n : Nat) :
    Fits (wrapperAllocSteps state n).mem q width := by
  induction n with
  | zero => exact h
  | succ n ih => exact Fits.alloca (wrapperAllocSteps_wf state hwf n) ih

theorem wrapperAllocSteps_read (state : GlobalState) (hwf : state.WF)
    (q : Pointer) (width : Nat) (h : Fits state.mem q width) (n : Nat) :
    (wrapperAllocSteps state n).mem.readAt q width = state.mem.readAt q width := by
  induction n with
  | zero => rfl
  | succ n ih => rw [wrapperAllocSteps, MemoryState.readAt_alloca
      (wrapperAllocSteps_wf state hwf n) (wrapperAllocSteps_fits state hwf q width h n), ih]

theorem slot_ne (state : GlobalState) (i j : Nat) (hne : i ≠ j) :
    (slot state i).id ≠ (slot state j).id := by
  intro he
  have hi := congrArg BlockId.id he
  simp only [slot] at hi
  omega

theorem slot_local (state : GlobalState) (i : Nat) :
    state.alloc.nextFreeBlock ≤ (slot state i).id.id := by simp [slot]

theorem slot_ne_caller (state : GlobalState) (hwf : state.WF)
    (q : Pointer) (width : Nat) (h : Fits state.mem q width) (i : Nat) :
    (slot state i).id ≠ q.id := by
  have hq := hwf.lt h.mem
  intro he
  have hs := slot_local state i
  rw [he] at hs
  omega

theorem wrapperAllocSteps_slot (state : GlobalState) (i n : Nat) (hi : i < n) :
    (wrapperAllocSteps state n).mem[(slot state i).id]? = some ⟨slotSize i, 0⟩ := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases he : i = n
    · subst i
      simp [wrapperAllocSteps, GlobalState.alloca, slot,
        wrapperAllocSteps_count, MemoryState.getElem?_eq]
    · have hne : (slot state i).id ≠ (wrapperAllocSteps state n).allocaPtr.id := by
        rw [wrapperAllocSteps_ptr]
        exact slot_ne state i n he
      rw [wrapperAllocSteps, GlobalState.getElem?_alloca hne]
      exact ih (by omega)

theorem startup_slot_range (state : GlobalState) (i : Fin 24) :
    SmallRange (startupState state).mem (slot state i.val) (slotSize i.val) := by
  refine ⟨⟨slotSize i.val, 0⟩, ?_, ?_, ?_⟩
  · rw [startupState_eq_wrapperAllocSteps]
    exact wrapperAllocSteps_slot state i.val 24 i.isLt
  · change slotSize i.val < 2 ^ 63
    unfold slotSize; split <;> decide
  · simp [slot]

theorem startup_slot_fits64 (state : GlobalState) (i : Fin 24) :
    Fits (startupState state).mem (slot state i.val) 64 := by
  apply Fits.mono (w := 8 * slotSize i.val) _ (startup_slot_range state i).fits
  unfold slotSize; split <;> decide

/-- Presence is transported across the literal allocation prefix. -/
theorem wrapperAllocSteps_global (state : GlobalState) (hwf : state.WF)
    (constant : ByteGlobal) (id : BlockId) (h : constant.Present id state.mem) (n : Nat) :
    constant.Present id (wrapperAllocSteps state n).mem := by
  induction n with
  | zero => exact h
  | succ n ih => exact ih.alloca (wrapperAllocSteps_wf state hwf n)

end Agave.Ed25519.Verifier.Execution.ScalarWide
