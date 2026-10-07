import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.Setup
import SSA.Projects.Agave.Ed25519.Proof.Reduce64.Execution.Memory

namespace Agave.Ed25519.ScalarReduce32.Execution
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution (SmallRange)
set_option maxRecDepth 10000

/-- The nine u128 slots are surrounded by nineteen and five u64 slots. -/
def allocationSize (n : Nat) : Nat := if 19 ≤ n ∧ n < 28 then 16 else 8

def allocationStates (s : GlobalState) : Nat → GlobalState
  | 0 => s
  | n + 1 => (allocationStates s n).alloca (allocationSize n)

def startupScratch (s : GlobalState) (i : Fin 33) : Pointer :=
  (allocationStates s i.val).allocaPtr

theorem allocationSchedule_state (E : Env program.Γ) (s : GlobalState) :
    (allocationSchedule E s).2 = allocationStates s 33 := rfl

theorem allocationStates_count (s : GlobalState) (n : Nat) :
    (allocationStates s n).alloc.nextFreeBlock = s.alloc.nextFreeBlock + n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change (allocationStates s n).alloc.nextFreeBlock + 1 = s.alloc.nextFreeBlock + (n + 1)
      rw [ih]
      omega

theorem allocationStates_wf (s : GlobalState) (h : s.WF) (n : Nat) :
    (allocationStates s n).WF := by
  induction n with
  | zero => exact h
  | succ n ih => exact ih.alloca

theorem scalar_smallRange_alloca (s : GlobalState) (hwf : s.WF)
    (q : Pointer) (count size : Nat) (h : SmallRange s.mem q count) :
    SmallRange (s.alloca size).mem q count := by
  rcases h with ⟨block, hblock, hsmall, hcount⟩
  have hf : Fits s.mem q (8 * count) := SmallRange.fits ⟨block, hblock, hsmall, hcount⟩
  refine ⟨block, ?_, hsmall, hcount⟩
  rw [GlobalState.getElem?_alloca (GlobalState.ne_allocaPtr_of_fits hwf hf)]
  exact hblock

theorem allocationStates_smallRange_later (s : GlobalState) (hwf : s.WF)
    (q : Pointer) (count start : Nat) (h : SmallRange (allocationStates s start).mem q count)
    (extra : Nat) : SmallRange (allocationStates s (start + extra)).mem q count := by
  induction extra with
  | zero => exact h
  | succ extra ih =>
      exact scalar_smallRange_alloca _ (allocationStates_wf s hwf (start + extra))
        q count (allocationSize (start + extra)) ih

theorem allocationStates_smallRange (s : GlobalState) (hwf : s.WF)
    (q : Pointer) (count : Nat) (h : SmallRange s.mem q count) (n : Nat) :
    SmallRange (allocationStates s n).mem q count := by
  simpa only [Nat.zero_add] using allocationStates_smallRange_later s hwf q count 0 h n

theorem allocationStates_read (s : GlobalState) (hwf : s.WF)
    (q : Pointer) (width : Nat) (h : SmallRange s.mem q count) (n : Nat) :
    (allocationStates s n).mem.readAt q width = s.mem.readAt q width := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [allocationStates, MemoryState.readAt_alloca (allocationStates_wf s hwf n)
        (allocationStates_smallRange s hwf q count h n).fits, ih]

theorem scalar_smallRange_allocaPtr (s : GlobalState) (n : Nat) (h : n < 2 ^ 63) :
    SmallRange (s.alloca n).mem s.allocaPtr n := by
  refine ⟨⟨n, 0⟩, ?_, h, ?_⟩
  · simp [GlobalState.alloca, GlobalState.allocaPtr, MemoryState.getElem?_eq]
  · simp [GlobalState.allocaPtr]

theorem startupScratch_live (s : GlobalState) (hwf : s.WF) (i : Fin 33) :
    SmallRange (allocationStates s 33).mem (startupScratch s i) (allocationSize i.val) := by
  have hsz : allocationSize i.val < 2 ^ 63 := by
    unfold allocationSize
    split <;> decide
  have hf := scalar_smallRange_allocaPtr (allocationStates s i.val) (allocationSize i.val) hsz
  have hl := allocationStates_smallRange_later s hwf (startupScratch s i)
    (allocationSize i.val) (i.val + 1) hf (33 - (i.val + 1))
  have he : i.val + 1 + (33 - (i.val + 1)) = 33 := by omega
  simpa only [he] using hl

theorem startupScratch_local (s : GlobalState) (i : Fin 33) :
    s.alloc.nextFreeBlock ≤ (startupScratch s i).id.id := by
  change s.alloc.nextFreeBlock ≤ (allocationStates s i.val).alloc.nextFreeBlock
  rw [allocationStates_count]
  omega

theorem startupScratch_ne_caller (s : GlobalState) (hwf : s.WF)
    (q : Pointer) (h : Fits s.mem q width) (i : Fin 33) :
    (startupScratch s i).id ≠ q.id := by
  have hq := hwf.lt h.mem
  have hs := startupScratch_local s i
  intro he
  rw [he] at hs
  omega

end Agave.Ed25519.ScalarReduce32.Execution
