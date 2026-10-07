import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.WrapperCalls
import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.SplitStores
import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.ExactByteMemory
import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.Frame

/-! Exact frame equations for split stores, both Montgomery calls/copies, and
serialization. Every equality concerns complete memory, including domains. -/
namespace Agave.Ed25519.Verifier.Execution.ScalarWide
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution (SmallRange)
open Agave.Ed25519.ScalarReduce32.Execution (storeBytes storePrefix)

/-- All five stores to a wrapper-owned scalar buffer disappear at return. -/
theorem private_outputStores_erase (m : MemoryState) (out : Pointer)
    (words : Fin 5 → BitVec 64) (mark : Nat) (hlocal : mark ≤ out.id.id) :
    (ScalarMontgomeryMul.outputStores m out words).eraseFrom mark = m.eraseFrom mark := by
  have hadd (off : BitVec 64) : mark ≤ (out.add off).id.id := by
    simpa only [Pointer.add_id] using hlocal
  simp only [ScalarMontgomeryMul.outputStores, MemoryState.eraseFrom_storeAt,
    MemoryState.storeAt_eraseFrom_of_le hlocal,
    MemoryState.storeAt_eraseFrom_of_le (hadd _)]

theorem splitStores_erase (m : MemoryState) (low high : Pointer) (bytes : BitVec 512)
    (mark : Nat) (hlow : mark ≤ low.id.id) (hhigh : mark ≤ high.id.id) :
    (splitStores m low high bytes).eraseFrom mark = m.eraseFrom mark := by
  rw [splitStores, private_outputStores_erase _ _ _ _ hhigh,
    private_outputStores_erase _ _ _ _ hlow]

/-- Callee private allocations are already erased by its call rule; both
remaining stores target wrapper-local objects and disappear at wrapper return. -/
theorem montgomeryCopyState_erase (state : GlobalState) (a b : Fin 5 → BitVec 64)
    (tmp operand constant : Pointer) (mark : Nat)
    (htmp : mark ≤ tmp.id.id) (hop : mark ≤ operand.id.id) :
    (montgomeryCopyState state a b tmp operand constant).mem.eraseFrom mark =
      state.mem.eraseFrom mark := by
  simp only [montgomeryCopyState, copy40State, ScalarMontgomeryMul.callPostState,
    MemoryState.eraseFrom_storeAt, MemoryState.storeAt_eraseFrom_of_le hop]
  exact private_outputStores_erase _ _ _ _ htmp

theorem storePrefix_erase (m : MemoryState) (out : Pointer) (bits : BitVec 256)
    (mark n : Nat) :
    (storePrefix m out bits n).eraseFrom mark =
      storePrefix (m.eraseFrom mark) out bits n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [storePrefix, MemoryState.eraseFrom_storeAt, ih, storePrefix]

/-- Once local-state erasure is established, serialization produces exactly
one caller-visible 256-bit store, preserving every other bit and block. -/
theorem serialized_frame (m base : MemoryState) (out : Pointer) (bits : BitVec 256)
    (mark : Nat) (hframe : m.eraseFrom mark = base) (hlive : SmallRange base out 32) :
    (storeBytes m out (fun i => bits.extractLsb' (8 * i.val) 8)).eraseFrom mark =
      base.storeAt out bits := by
  have heq (mem : MemoryState) :
      storeBytes mem out (fun i => bits.extractLsb' (8 * i.val) 8) =
        storePrefix mem out bits 32 := by
    simp only [storeBytes, storePrefix, Pointer.add_zero]
    rfl
  rw [heq, storePrefix_erase, hframe, ← heq, storeBytes_exact _ _ _ hlive]

end Agave.Ed25519.Verifier.Execution.ScalarWide
