import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.InvocationTailState

/-! Concrete families of the outer local slots. -/
namespace Agave.Ed25519.Verifier.Execution.ScalarWide
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution (SmallRange)

theorem startup_result_range (state : GlobalState) (i : Fin 5) :
    SmallRange (startupState state).mem (resultSlots state i) 8 := by
  have hs := startup_slot_range state ⟨19 + i.val, by omega⟩
  have hsize : slotSize (19 + i.val) = 8 := by unfold slotSize; rw [if_neg (by omega)]
  simpa only [resultSlots, hsize] using hs

theorem startup_input_range (state : GlobalState) (i : Fin 8) :
    SmallRange (startupState state).mem (inputSlots state i) 8 := by
  have hs := startup_slot_range state ⟨11 + i.val, by omega⟩
  have hsize : slotSize (11 + i.val) = 8 := by unfold slotSize; rw [if_neg (by omega)]
  simpa only [inputSlots, hsize] using hs

theorem startup_zero_range (state : GlobalState) (i : Fin 5) :
    SmallRange (startupState state).mem (zeroSlots state i) 8 := by
  have hs := startup_slot_range state ⟨i.val, by omega⟩
  have hsize : slotSize i.val = 8 := by unfold slotSize; rw [if_neg (by have := i.isLt; omega)]
  simpa only [zeroSlots, hsize] using hs

end Agave.Ed25519.Verifier.Execution.ScalarWide
