import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.SqrtRatioInlineCallsMemory

namespace Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline
open LeanMLIR.RIR SerialFieldMul
open Reduce64.Execution (SmallRange)
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

theorem callWrite_counter (s : GlobalState) (r : Pointer) (x extra : Words) (n : Nat) :
    (callWrite s r x extra n).alloc.nextFreeBlock =
      s.alloc.nextFreeBlock + if n = 6 then 20 else 0 := by
  unfold callWrite
  split <;> simp_all

theorem callsState_counter (s : GlobalState) (values : Nat → Words) (extra : Words) (n : Nat) :
    (callsState s values extra n).alloc.nextFreeBlock =
      s.alloc.nextFreeBlock + 22 + if 6 < n then 20 else 0 := by
  induction n with
  | zero => simpa only [callsState,allocate_counter,allocationSizes,List.length_cons,
      List.length_nil,Nat.reduceAdd,ite_false,Nat.not_lt_zero,Nat.add_zero]
  | succ n ih =>
    rw [callsState,callWrite_counter,ih]
    split_ifs <;> omega

theorem callWrite_private (s : GlobalState) (r : Pointer) (x extra : Words)
    (n mark : Nat) (h : mark ≤ r.id.id) :
    (callWrite s r x extra n).mem.eraseFrom mark = s.mem.eraseFrom mark := by
  unfold callWrite
  split
  · change ((storeLimbs s.mem r x).storeAt (r.add 40) (limbBytes extra)).eraseFrom mark = _
    rw [MemoryState.eraseFrom_storeAt,MemoryState.storeAt_eraseFrom_of_le (p := r.add 40) h,
      private_store_erase _ r x mark h]
  · exact private_store_erase s.mem r x mark h

theorem callsState_private (s : GlobalState) (values : Nat → Words) (extra : Words)
    (hwf : s.WF) (n : Nat) :
    (callsState s values extra n).mem.eraseFrom s.alloc.nextFreeBlock = s.mem := by
  induction n with
  | zero =>
    rw [callsState,allocate_erase s allocationSizes _ (Nat.le_refl _)]
    exact congrArg GlobalState.mem (GlobalState.eraseFrom_self hwf)
  | succ n ih =>
    exact (callWrite_private _ _ _ _ n s.alloc.nextFreeBlock (slot_private s (callSlot n))).trans ih

theorem callsState_ready (dg : Decode.Globals) (g : Globals) (s : GlobalState)
    (values : Nat → Words) (extra : Words) (hwf : s.WF) (hready : Ready dg g s)
    (n : Nat) : Ready dg g (callsState s values extra n) := by
  constructor
  · exact ⟨callsState_live s values extra (allocate_live s hwf _ hready.curveD.1) n,
      (callsState_read_old s values extra hwf hready.curveD.1 320 (by decide) n).trans hready.curveD.2⟩
  · exact ⟨callsState_live s values extra (allocate_live s hwf _ hready.sqrtM1.1) n,
      (callsState_read_old s values extra hwf hready.sqrtM1.1 320 (by decide) n).trans hready.sqrtM1.2⟩

end Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline
