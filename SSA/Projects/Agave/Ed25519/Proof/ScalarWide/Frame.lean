import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.MontgomeryStores
import SSA.Projects.Agave.Ed25519.Proof.Verifier.ChallengeExecutionMemory

/-! Frame equations for the literal allocation prefixes and Montgomery store
suffix. These establish exact memory erasure, not just equality of reads. -/
namespace Agave.Ed25519.Verifier.Execution

open LeanMLIR.RIR

namespace ScalarMontgomeryMul

/-- Erasure commutes with the five ordered output stores. -/
theorem outputStores_erase (m : MemoryState) (out : Pointer)
    (words : Fin 5 → BitVec 64) (mark : Nat) :
    (outputStores m out words).eraseFrom mark =
      outputStores (m.eraseFrom mark) out words := by
  simp only [outputStores, MemoryState.eraseFrom_storeAt]

/-- Every one of the nine actual scratch zeroizations disappears at return. -/
theorem zeroizeStores_erase (m : MemoryState) (scratch : Fin 9 → Pointer) (mark : Nat)
    (hlocal : ∀ i, mark ≤ (scratch i).id.id) :
    (zeroizeStores m scratch).eraseFrom mark = m.eraseFrom mark := by
  simp only [zeroizeStores, MemoryState.eraseFrom_storeAt,
    MemoryState.storeAt_eraseFrom_of_le (hlocal _)]

/-- Exact frame result for the actual complete store/zeroize suffix. -/
theorem stores_erase (m base : MemoryState) (out : Pointer)
    (words : Fin 5 → BitVec 64) (scratch : Fin 9 → Pointer) (mark : Nat)
    (hframe : m.eraseFrom mark = base) (hlocal : ∀ i, mark ≤ (scratch i).id.id) :
    (zeroizeStores (outputStores m out words) scratch).eraseFrom mark =
      outputStores base out words := by
  rw [zeroizeStores_erase _ _ _ hlocal, outputStores_erase, hframe]

/-- The nine actual startup allocations contribute no caller memory changes. -/
theorem startupState_erase (state : GlobalState) (hwf : state.WF) :
    (startupState state).mem.eraseFrom state.alloc.nextFreeBlock = state.mem := by
  unfold startupState
  repeat rw [GlobalState.eraseFrom_alloca_of_le (by simp [GlobalState.alloca] <;> omega)]
  exact hwf.eraseFrom

end ScalarMontgomeryMul

namespace ScalarWide

/-- The twenty-four actual startup allocations vanish from the caller's frame. -/
theorem startupState_erase (state : GlobalState) (hwf : state.WF) :
    (startupState state).mem.eraseFrom state.alloc.nextFreeBlock = state.mem := by
  unfold startupState
  repeat rw [GlobalState.eraseFrom_alloca_of_le (by simp [GlobalState.alloca] <;> omega)]
  exact hwf.eraseFrom

end ScalarWide

end Agave.Ed25519.Verifier.Execution
