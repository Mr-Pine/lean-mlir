import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.MontgomeryBody

/-! The nine concrete alloca states: caller memory transport, scratch liveness,
and freshness used to discharge the body-entry invariant. -/
namespace Agave.Ed25519.Verifier.Execution.ScalarMontgomeryMul
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution (SmallRange)

/-- Iterate the exact 16-byte allocation present nine times in the source. -/
def allocSteps (state : GlobalState) : Nat → GlobalState
  | 0 => state
  | n + 1 => (allocSteps state n).alloca 16

theorem startupState_eq_allocSteps (state : GlobalState) : startupState state = allocSteps state 9 := rfl

theorem allocSteps_count (state : GlobalState) (n : Nat) :
    (allocSteps state n).alloc.nextFreeBlock = state.alloc.nextFreeBlock + n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change (allocSteps state n).alloc.nextFreeBlock + 1 = state.alloc.nextFreeBlock + (n + 1)
      omega

theorem allocSteps_add (state : GlobalState) (m n : Nat) :
    allocSteps state (m + n) = allocSteps (allocSteps state m) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have hn : m + (n + 1) = (m + n) + 1 := by omega
      rw [hn]
      change (allocSteps state (m + n)).alloca 16 = (allocSteps (allocSteps state m) n).alloca 16
      exact congrArg (·.alloca 16) ih

theorem allocSteps_wf (state : GlobalState) (hwf : state.WF) (n : Nat) :
    (allocSteps state n).WF := by
  induction n with
  | zero => exact hwf
  | succ n ih => exact ih.alloca

theorem allocSteps_fits (state : GlobalState) (hwf : state.WF)
    (q : Pointer) (width : Nat) (h : Fits state.mem q width) (n : Nat) :
    Fits (allocSteps state n).mem q width := by
  induction n with
  | zero => exact h
  | succ n ih => exact Fits.alloca (allocSteps_wf state hwf n) ih

theorem smallRange_alloca (state : GlobalState) (hwf : state.WF)
    (q : Pointer) (count size : Nat) (h : SmallRange state.mem q count) :
    SmallRange (state.alloca size).mem q count := by
  rcases h with ⟨block, hblock, hsmall, hcount⟩
  have hfits : Fits state.mem q (8 * count) := SmallRange.fits ⟨block, hblock, hsmall, hcount⟩
  refine ⟨block, ?_, hsmall, hcount⟩
  rw [GlobalState.getElem?_alloca (GlobalState.ne_allocaPtr_of_fits hwf hfits)]
  exact hblock

theorem allocSteps_smallRange (state : GlobalState) (hwf : state.WF)
    (q : Pointer) (count : Nat) (h : SmallRange state.mem q count) (n : Nat) :
    SmallRange (allocSteps state n).mem q count := by
  induction n with
  | zero => exact h
  | succ n ih => exact smallRange_alloca _ (allocSteps_wf state hwf n) q count 16 ih

theorem allocSteps_read (state : GlobalState) (hwf : state.WF)
    (q : Pointer) (width : Nat) (h : Fits state.mem q width) (n : Nat) :
    (allocSteps state n).mem.readAt q width = state.mem.readAt q width := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [allocSteps, MemoryState.readAt_alloca (allocSteps_wf state hwf n)
        (allocSteps_fits state hwf q width h n), ih]

def scratchPtrs (state : GlobalState) (i : Fin 9) : Pointer :=
  (allocSteps state i.val).allocaPtr

theorem scratchPtrs_local (state : GlobalState) (i : Fin 9) :
    state.alloc.nextFreeBlock ≤ (scratchPtrs state i).id.id := by
  change state.alloc.nextFreeBlock ≤ (allocSteps state i.val).alloc.nextFreeBlock
  rw [allocSteps_count]
  omega

theorem scratchPtrs_ne_caller (state : GlobalState) (hwf : state.WF)
    (q : Pointer) (width : Nat) (h : Fits state.mem q width) (i : Fin 9) :
    (scratchPtrs state i).id ≠ q.id := by
  have hq := hwf.lt h.mem
  have hs := scratchPtrs_local state i
  intro he
  rw [he] at hs
  omega

theorem scratchPtrs_fits (state : GlobalState) (hwf : state.WF) (i : Fin 9) :
    Fits (startupState state).mem (scratchPtrs state i) 128 := by
  rw [startupState_eq_allocSteps]
  have hn : 9 = (i.val + 1) + (9 - (i.val + 1)) := by omega
  rw [hn, allocSteps_add]
  apply allocSteps_fits _ (allocSteps_wf state hwf (i.val + 1))
  exact Fits.allocaPtr (by decide : 128 ≤ 8 * 16)

/-- All body constants, arguments, and scratch registers are supplied by the
literal startup prefix. -/
theorem startup_bodyReady (E : Env program.Γ) (state : GlobalState)
    (out left right : Pointer)
    (ho : E.read (%arg0) = .value out)
    (hl : E.read (%arg1) = .value left)
    (hr : E.read (%arg2) = .value right) :
    BodyReady (startupEnv E state) out left right (scratchPtrs state) := by
  change E.args 0 = .value out at ho
  change E.args 1 = .value left at hl
  change E.args 2 = .value right at hr
  constructor
  · constructor <;> simp [startupEnv, scratchPtrs, allocSteps, ho, hl, hr, mlir_env]
  all_goals simp [startupEnv, scratchPtrs, allocSteps, ho, hl, hr, mlir_env]

end Agave.Ed25519.Verifier.Execution.ScalarMontgomeryMul
