import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.Pow22501BodyCalls
import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.LimbReadState

/-! Memory history of the addition chain, independently of the arithmetic in
each stored field value and of the RIR instruction trace. -/
namespace Agave.Ed25519.Encoding.Decompress.Execution.Pow22501
open LeanMLIR.RIR
open SerialFieldMul
open SerialPoint.Execution
open Reduce64.Execution (SmallRange)
set_option maxRecDepth 20000
set_option maxHeartbeats 1600000

variable {s : GlobalState} {p : Pointer}

theorem scratchState_counter (s : GlobalState) (n : Nat) :
    (scratchState s n).alloc.nextFreeBlock = s.alloc.nextFreeBlock + n := by
  induction n with
  | zero => simp [scratchState]
  | succ n ih => simp [scratchState, GlobalState.alloca, ih, Nat.add_assoc]

theorem scratchState_wf (h : s.WF) (n : Nat) : (scratchState s n).WF := by
  induction n with
  | zero => exact h
  | succ n ih => exact ih.alloca

theorem scratchState_live (hwf : s.WF) (h : SmallRange s.mem p bytes) (n : Nat) :
    SmallRange (scratchState s n).mem p bytes := by
  induction n with
  | zero => exact h
  | succ n ih => exact smallRange_alloca (scratchState_wf hwf n) ih

theorem scratch_allocaPtr (s : GlobalState) (n : Nat) :
    (scratchState s n).allocaPtr = scratch s n := by
  simp only [GlobalState.allocaPtr, scratch, scratchState_counter]

theorem scratch_live (hwf : s.WF) (hi : i < n) :
    SmallRange (scratchState s n).mem (scratch s i) 40 := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases he : i = n
    · subst i
      rw [← scratch_allocaPtr]
      exact smallRange_alloca_self _ _ (by decide)
    · exact smallRange_alloca (scratchState_wf hwf n) (ih (by omega))

theorem scratch_ne (s : GlobalState) (h : i ≠ j) :
    (scratch s i).id ≠ (scratch s j).id := by
  intro he
  have hi := congrArg BlockId.id he
  change s.alloc.nextFreeBlock + i = s.alloc.nextFreeBlock + j at hi
  omega

theorem scratch_ne_old (hwf : s.WF) (h : Fits s.mem p bits) (n : Nat) :
    (scratch s n).id ≠ p.id := by
  have hp := hwf.lt h.mem
  intro he
  have hi := congrArg BlockId.id he
  change s.alloc.nextFreeBlock + n = p.id.id at hi
  omega

theorem scratchState_readLimbs (hwf : s.WF) (h : SmallRange s.mem p 40) (n : Nat) :
    readLimbs (scratchState s n) p = readLimbs s p := by
  induction n with
  | zero => rfl
  | succ n ih =>
    exact (readLimbMemory_alloca (scratchState_wf hwf n)
      (scratchState_live hwf h n) 40).trans ih

theorem scratchState_erase (hwf : s.WF) (n : Nat) :
    (scratchState s n).mem.eraseFrom s.alloc.nextFreeBlock = s.mem := by
  induction n with
  | zero => exact hwf.eraseFrom
  | succ n ih =>
    rw [scratchState, GlobalState.eraseFrom_alloca_of_le]
    · exact ih
    · simp [scratchState_counter]

/-- The second and third temporary registers are exchanged in source order. -/
def scratchIndex (n : Nat) : Nat :=
  if n = 1 then 17 else if n = 2 then 18 else 19 - n

theorem scratchIndex_lt (h : n < 20) : scratchIndex n < 20 := by
  unfold scratchIndex
  split_ifs <;> omega

theorem scratchIndex_injective (hi : i < 20) (hj : j < 20)
    (h : scratchIndex i = scratchIndex j) : i = j := by
  unfold scratchIndex at h
  split_ifs at h <;> omega

/-- The final multiplication writes the first caller output field. -/
def destination (initial : GlobalState) (out : Pointer) (n : Nat) : Pointer :=
  if n < 20 then scratch initial (scratchIndex n) else out

theorem destination_live (hwf : s.WF) (hout : SmallRange s.mem out 40) (n : Nat) :
    SmallRange (scratchState s 20).mem (destination s out n) 40 := by
  unfold destination
  split
  · exact scratch_live hwf (scratchIndex_lt ‹_›)
  · exact scratchState_live hwf hout 20

theorem destination_ne (hwf : s.WF) (hout : SmallRange s.mem out 40)
    (hi : i < 21) (hj : j < 21) (hne : i ≠ j) :
    (destination s out i).id ≠ (destination s out j).id := by
  by_cases h20i : i < 20 <;> by_cases h20j : j < 20
  · simp only [destination, ite_eq_left h20i, ite_eq_left h20j]
    exact scratch_ne s (fun he => hne (scratchIndex_injective h20i h20j he))
  · simp only [destination, ite_eq_left h20i, ite_eq_right h20j]
    exact scratch_ne_old hwf hout.fits _
  · simp only [destination, ite_eq_right h20i, ite_eq_left h20j]
    exact Ne.symm (scratch_ne_old hwf hout.fits _)
  · omega

/-- State before call `n`; its values are arbitrary complete field words. -/
def callState (initial : GlobalState) (out : Pointer) (values : Nat → Fin 5 → BitVec 64) :
    Nat → GlobalState
  | 0 => scratchState initial 20
  | n + 1 =>
      {callState initial out values n with mem := storeLimbs (callState initial out values n).mem (destination initial out n) (values n)}

def traceStates (initial : GlobalState) (out : Pointer) (values : Nat → Fin 5 → BitVec 64) :
    CallStates := fun i => callState initial out values (i.val + 1)

theorem callState_wf (initial : GlobalState) (out : Pointer) (values : Nat → Fin 5 → BitVec 64)
    (hwf : initial.WF) (n : Nat) : (callState initial out values n).WF := by
  induction n with
  | zero => exact scratchState_wf hwf 20
  | succ n ih => exact wf_storeLimbs ih _ _

theorem callState_live (initial : GlobalState) (out : Pointer) (values : Nat → Fin 5 → BitVec 64)
    (h : SmallRange (scratchState initial 20).mem p bytes) (n : Nat) :
    SmallRange (callState initial out values n).mem p bytes := by
  induction n with
  | zero => exact h
  | succ n ih => exact smallRange_storeLimbs ih _ _

theorem callState_alloc (initial : GlobalState) (out : Pointer) (values : Nat → Fin 5 → BitVec 64)
    (n : Nat) : (callState initial out values n).alloc = ⟨initial.alloc.nextFreeBlock + 20⟩ := by
  induction n with
  | zero => exact congrArg AllocState.mk (scratchState_counter initial 20)
  | succ n ih => exact ih

theorem callState_read_old (initial : GlobalState) (out : Pointer) (values : Nat → Fin 5 → BitVec 64)
    (hwf : initial.WF) (h : SmallRange initial.mem p 40) (hn : n ≤ 20) :
    readLimbs (callState initial out values n) p = readLimbs initial p := by
  induction n with
  | zero => exact scratchState_readLimbs hwf h 20
  | succ n ih =>
    have hn20 : n < 20 := by omega
    have hne : (destination initial out n).id ≠ p.id := by
      simp only [destination, ite_eq_left hn20]
      exact scratch_ne_old hwf h.fits _
    exact (readLimbs_storeLimbs_ne (callState initial out values n)
      (destination initial out n) p (values n) hne).trans (ih (by omega))

theorem callState_read_written (initial : GlobalState) (out : Pointer) (values : Nat → Fin 5 → BitVec 64)
    (hwf : initial.WF) (hout : SmallRange initial.mem out 40)
    (hi : i < k) (hk : k ≤ 21) :
    readLimbs (callState initial out values k) (destination initial out i) = values i := by
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases he : i = k
    · subst i
      exact readLimbs_storeLimbs (callState initial out values k) _ _
        (callState_live initial out values (destination_live hwf hout k) k)
    · exact (readLimbs_storeLimbs_ne (callState initial out values k)
        (destination initial out k) (destination initial out i) (values k)
        (destination_ne hwf hout (by omega) (by omega) (Ne.symm he))).trans
          (ih (by omega) (by omega))

theorem callState_read320_written (initial : GlobalState) (out : Pointer) (values : Nat → Fin 5 → BitVec 64)
    (hwf : initial.WF) (hout : SmallRange initial.mem out 40)
    (hi : i < k) (hk : k ≤ 21) :
    (callState initial out values k).mem.readAt (destination initial out i) 320 =
      limbBytes (values i) := by
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases he : i = k
    · subst i
      exact storeLimbs_read320 (callState initial out values k).mem _ _
        (callState_live initial out values (destination_live hwf hout k) k)
    · exact (readAt_storeLimbs_ne (callState initial out values k).mem
        (destination initial out k) (destination initial out i) (values k) 320
        (destination_ne hwf hout (by omega) (by omega) (Ne.symm he))).trans
          (ih (by omega) (by omega))

theorem callState_erase_scratch (initial : GlobalState) (out : Pointer)
    (values : Nat → Fin 5 → BitVec 64) (hwf : initial.WF) (hn : n ≤ 20) :
    (callState initial out values n).mem.eraseFrom initial.alloc.nextFreeBlock = initial.mem := by
  induction n with
  | zero => exact scratchState_erase hwf 20
  | succ n ih =>
    change (storeLimbs _ _ _).eraseFrom _ = _
    rw [eraseFrom_storeLimbs_fresh]
    · exact ih (by omega)
    · simp only [destination, ite_eq_left (show n < 20 by omega), scratch]
      omega

theorem callState_erase_final (initial : GlobalState) (out : Pointer)
    (values : Nat → Fin 5 → BitVec 64) (hwf : initial.WF) :
    (callState initial out values 21).mem.eraseFrom initial.alloc.nextFreeBlock =
      storeLimbs initial.mem out (values 20) := by
  change (storeLimbs (callState initial out values 20).mem
    (destination initial out 20) (values 20)).eraseFrom _ = _
  rw [eraseFrom_storeLimbs, callState_erase_scratch initial out values hwf (by decide)]
  rfl

/-- Erase the copied result using facts about an opaque final state. -/
theorem copyState_erase_of_facts (initial : GlobalState) (out : Pointer)
    (last : GlobalState) (first second : Fin 5 → BitVec 64)
    (ha : last.alloc = ⟨initial.alloc.nextFreeBlock + 20⟩)
    (hm : last.mem.eraseFrom initial.alloc.nextFreeBlock = storeLimbs initial.mem out first)
    (hr : last.mem.readAt (scratch initial 15) 320 = limbBytes second) :
    {(copyState initial out last) with
      mem := (copyState initial out last).mem.eraseFrom initial.alloc.nextFreeBlock} =
      {alloc := ⟨initial.alloc.nextFreeBlock + 20⟩,
       mem := (storeLimbs initial.mem out first).storeAt (out.add 40#64) (limbBytes second)} := by
  apply GlobalState.ext
  · exact ha
  · simp only [copyState, hr, MemoryState.eraseFrom_storeAt, hm]

/-- Complete output state after the actual copy and the call's frame erasure. -/
theorem copyState_erase (initial : GlobalState) (out : Pointer) (values : Nat → Fin 5 → BitVec 64)
    (hwf : initial.WF) (hout : SmallRange initial.mem out 40) :
    {(copyState initial out (callState initial out values 21)) with
      mem := (copyState initial out (callState initial out values 21)).mem.eraseFrom
        initial.alloc.nextFreeBlock} =
      {alloc := ⟨initial.alloc.nextFreeBlock + 20⟩,
       mem := (storeLimbs initial.mem out (values 20)).storeAt (out.add 40#64)
         (limbBytes (values 4))} := by
  exact copyState_erase_of_facts initial out (callState initial out values 21)
    (values 20) (values 4) (callState_alloc initial out values 21)
    (callState_erase_final initial out values hwf)
    (callState_read320_written initial out values hwf hout (i := 4) (k := 21)
      (by decide) (by decide))

end Agave.Ed25519.Encoding.Decompress.Execution.Pow22501
