import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.SqrtRatioInlineCallsMemory
import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.SqrtWords

namespace Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline
open LeanMLIR.RIR SerialFieldMul SerialPoint.Execution
open Reduce64.Execution (SmallRange)
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

theorem callsState_normal (s : GlobalState) (values : Nat → Words) (extra : Words)
    (n : Nat) (hn : n ≠ 6) :
    callsState s values extra (n+1) =
      {callsState s values extra n with mem := storeLimbs (callsState s values extra n).mem (slot s (callSlot n)) (values n)} := by
  rw [callsState]
  simp only [callWrite,ite_eq_right hn]

theorem callsState_six (s : GlobalState) (values : Nat → Words) (extra : Words) :
    callsState s values extra 7 =
      {alloc := ⟨(callsState s values extra 6).alloc.nextFreeBlock + 20⟩,
       mem := (storeLimbs (callsState s values extra 6).mem (slot s 7) (values 6)).storeAt (slot s 7 |>.add 40) (limbBytes extra)} := by
  rw [callsState]
  rfl

attribute [local irreducible] callsState machine Pow2k.iterateSquare

theorem calls_square (s : GlobalState) (values : Nat → Words) (extra : Words)
    (hwf : s.WF) (n count : Nat) (hn : n < 13) (hn6 : n ≠ 6)
    (hpos : 0 < count) (hcount : count < 2^32) (a : Pointer)
    (ha : SmallRange (allocate s allocationSizes).mem a 40)
    (hvalue : values n = Pow2k.iterateSquare count (readLimbs (callsState s values extra n) a)) :
    sqrtRatioPrimitives.pow2k (.cons (.value (slot s (callSlot n)))
      (.cons (.value a) (.cons (.value (BitVec.ofNat 32 count)) .nil)))
      (callsState s values extra n) = .value (.nil,callsState s values extra (n+1)) := by
  rw [callsState_normal s values extra n hn6,hvalue]
  exact Pow2k.program_call count hpos hcount _ a _ (callsState_wf s values extra hwf n)
    (call_destination_live s values extra hwf n n hn) (callsState_live s values extra ha n)

theorem calls_mul (s : GlobalState) (values : Nat → Words) (extra : Words)
    (hwf : s.WF) (n : Nat) (hn : n < 13) (hn6 : n ≠ 6) (a b : Pointer)
    (ha : SmallRange (allocate s allocationSizes).mem a 40)
    (hb : SmallRange (allocate s allocationSizes).mem b 40)
    (hvalue : values n = machine (readLimbs (callsState s values extra n) a)
      (readLimbs (callsState s values extra n) b)) :
    sqrtRatioPrimitives.mul (.cons (.value (slot s (callSlot n)))
      (.cons (.value a) (.cons (.value b) .nil)))
      (callsState s values extra n) = .value (.nil,callsState s values extra (n+1)) := by
  rw [callsState_normal s values extra n hn6,hvalue]
  exact kernel_call _ a b _ (callsState_wf s values extra hwf n)
    (call_destination_live s values extra hwf n n hn)
    (callsState_live s values extra ha n) (callsState_live s values extra hb n)

theorem calls_pow (s : GlobalState) (values : Nat → Words) (extra : Words)
    (hwf : s.WF) (hvalue : Pow22501.rawWordChain (values 5) = (values 6,extra)) :
    sqrtRatioPrimitives.pow22501 (.cons (.value (slot s 7)) (.cons (.value (slot s 14)) .nil))
      (callsState s values extra 6) = .value (.nil,callsState s values extra 7) := by
  have hc := Pow22501.program_call (slot s 7) (slot s 14) (callsState s values extra 6)
    (callsState_wf s values extra hwf 6) (callsState_slot_live s values extra hwf 7 6)
    (callsState_slot_live s values extra hwf 14 6)
  have hx : readLimbs (callsState s values extra 6) (slot s 14) = values 5 :=
    callsState_words_written s values extra hwf (i := 5) (by decide) (by decide)
  rw [hx,Pow22501.resultState,hvalue] at hc
  rw [callsState_six]
  simpa only [sqrtRatioPrimitives,Pow22501.program.args,BitVec.ofNat_eq_ofNat] using hc

theorem calls_copy (s : GlobalState) (values : Nat → Words) (extra : Words)
    (hwf : s.WF) (hvalue : values 7 = values 6) (E : Env Γ) :
    Operation.memcpy (.value (slot s 8)) (.value (slot s 7)) (.value 40#64) E
      (callsState s values extra 7) = .value (E,callsState s values extra 8) := by
  have hr := callsState_slot_live s values extra hwf 8 7
  have ha := call_destination_live s values extra hwf 6 7 (by decide)
  have hread : (callsState s values extra 7).mem.readAt (slot s 7) 320 = limbBytes (values 6) :=
    callsState_read320_written s values extra hwf (i := 6) (n := 7) (by decide) (by decide)
  have hc := run_memcpy (dst := slot s 8) (src := slot s 7) (len := 40#64) (n := 40)
    rfl (Or.inl (slot_distinct s 8 7 (by decide))) hr.fits ha.fits (env := E) (s := callsState s values extra 7)
  rw [callsState_normal s values extra 7 (by decide)]
  have hout : slot s (callSlot 7) = slot s 8 := rfl
  rw [hout,storeLimbs_exact (callsState s values extra 7).mem (slot s 8) (values 7) hr,hvalue]
  simpa only [hread] using hc

end Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline
