import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.SqrtRatioInlinePrefixSquare
import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.Pow22501Execution
import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.LimbMemoryExact

/-! Exact private memory history of the thirteen field writes before pc117.
The seventh write is the real 80-byte exponentiation result. -/
namespace Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline
open LeanMLIR.RIR SerialFieldMul SerialPoint.Execution
open Reduce64.Execution (SmallRange)
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000

attribute [local irreducible] Pow2k.iterateSquare machine Pow22501.rawWordChain

def callSlot : Nat → Fin 22
  | 0 => 20 | 1 => 21 | 2 => 18 | 3 => 19 | 4 => 16 | 5 => 14
  | 6 => 7 | 7 => 8 | 8 => 6 | 9 => 15 | 10 => 17 | 11 => 12 | 12 => 13
  | _ => 0

theorem callSlot_injective (hi : i < 13) (hj : j < 13) (hne : i ≠ j) :
    callSlot i ≠ callSlot j := by
  interval_cases i <;> interval_cases j <;> norm_num [callSlot] at *

def callWrite (s : GlobalState) (r : Pointer) (x extra : Words) (n : Nat) : GlobalState :=
  let t : GlobalState := {s with mem := storeLimbs s.mem r x}
  if n = 6 then
    {alloc := ⟨s.alloc.nextFreeBlock + 20⟩, mem := t.mem.storeAt (r.add 40) (limbBytes extra)}
  else t

def callsState (s : GlobalState) (values : Nat → Words) (extra : Words) : Nat → GlobalState
  | 0 => allocate s allocationSizes
  | n + 1 => callWrite (callsState s values extra n) (slot s (callSlot n)) (values n) extra n

theorem callWrite_live (s : GlobalState) (r : Pointer) (x extra : Words) (n : Nat)
    {p : Pointer} {bytes : Nat} (h : SmallRange s.mem p bytes) :
    SmallRange (callWrite s r x extra n).mem p bytes := by
  unfold callWrite
  split
  · exact (smallRange_storeLimbs h r x).storeAt _ _
  · exact smallRange_storeLimbs h r x

theorem callWrite_wf (s : GlobalState) (r : Pointer) (x extra : Words) (n : Nat)
    (h : s.WF) : (callWrite s r x extra n).WF := by
  unfold callWrite
  split
  · exact (wf_storeLimbs h r x).add_blocks.storeAt
  · exact wf_storeLimbs h r x

theorem callWrite_read (s : GlobalState) (r : Pointer) (x extra : Words) (n : Nat)
    (p : Pointer) (bits : Nat) (hne : r.id ≠ p.id) :
    (callWrite s r x extra n).mem.readAt p bits = s.mem.readAt p bits := by
  unfold callWrite
  split
  · exact (MemoryState.readAt_storeAt_disjoint (p := r.add 40) (q := p)
      (m := storeLimbs s.mem r x) (v := 320) (w := bits) (Or.inl hne) _).trans
        (readAt_storeLimbs_ne s.mem r p x bits hne)
  · exact readAt_storeLimbs_ne s.mem r p x bits hne

theorem callWrite_words_ne (s : GlobalState) (r : Pointer) (x extra : Words) (n : Nat)
    (p : Pointer) (hne : r.id ≠ p.id) :
    readLimbs (callWrite s r x extra n) p = readLimbs s p := by
  funext i
  exact callWrite_read s r x extra n (p.add _) 64 hne

theorem callWrite_read320 (s : GlobalState) (r : Pointer) (x extra : Words) (n : Nat)
    (hr : SmallRange s.mem r 40) (h80 : n = 6 → SmallRange s.mem r 80) :
    (callWrite s r x extra n).mem.readAt r 320 = limbBytes x := by
  unfold callWrite
  split
  · rename_i hn
    have hoff : (r.add 40).offsetInBits = r.offsetInBits + 320 := by
      simpa using Pointer.offsetInBits_add ((h80 hn).no_wrap (k := 40) (by decide))
    have hd : (Range.of (r.add 40) 320).Disjoint (Range.of r 320) := by
      right
      simp only [Range.of, hoff]
      omega
    exact (MemoryState.readAt_storeAt_disjoint (m := storeLimbs s.mem r x)
      (p := r.add 40) (q := r) (v := 320) (w := 320) hd _).trans
        (storeLimbs_read320 s.mem r x hr)
  · exact storeLimbs_read320 s.mem r x hr

theorem callWrite_words (s : GlobalState) (r : Pointer) (x extra : Words) (n : Nat)
    (hr : SmallRange s.mem r 40) (h80 : n = 6 → SmallRange s.mem r 80) :
    readLimbs (callWrite s r x extra n) r = x :=
  readLimbs_of_limbBytes _ r x (callWrite_live s r x extra n hr)
    (callWrite_read320 s r x extra n hr h80)

theorem callsState_wf (s : GlobalState) (values : Nat → Words) (extra : Words)
    (hwf : s.WF) (n : Nat) : (callsState s values extra n).WF := by
  induction n with
  | zero => exact allocate_wf s hwf _
  | succ n ih => exact callWrite_wf _ _ _ _ _ ih

theorem callsState_live (s : GlobalState) (values : Nat → Words) (extra : Words)
    {p : Pointer} {bytes : Nat} (h : SmallRange (allocate s allocationSizes).mem p bytes)
    (n : Nat) : SmallRange (callsState s values extra n).mem p bytes := by
  induction n with
  | zero => exact h
  | succ n ih => exact callWrite_live _ _ _ _ _ ih

theorem callsState_slot_live (s : GlobalState) (values : Nat → Words) (extra : Words)
    (hwf : s.WF) (i : Fin 22) (n : Nat) :
    SmallRange (callsState s values extra n).mem (slot s i) allocationSizes[i.val] :=
  callsState_live s values extra (slot_live s hwf i) n

theorem call_destination_live (s : GlobalState) (values : Nat → Words) (extra : Words)
    (hwf : s.WF) (i n : Nat) (hi : i < 13) :
    SmallRange (callsState s values extra n).mem (slot s (callSlot i)) 40 := by
  have h := callsState_slot_live s values extra hwf (callSlot i) n
  interval_cases i <;> norm_num only [callSlot, allocationSizes, List.getElem_cons_zero,
    List.getElem_cons_succ, Fin.reduceFinMk] at h ⊢
  all_goals first | exact h | exact (by simpa only [Pointer.add_zero] using
    (smallRange_add h (k := 0) (count := 40) (by decide)))

theorem callsState_words_written (s : GlobalState) (values : Nat → Words) (extra : Words)
    (hwf : s.WF) (hi : i < n) (hn : n ≤ 13) :
    readLimbs (callsState s values extra n) (slot s (callSlot i)) = values i := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases he : i = n
    · subst i
      apply callWrite_words _ _ _ _ _ (call_destination_live s values extra hwf n n (by omega))
      intro hn6
      subst n
      exact callsState_slot_live s values extra hwf 7 6
    · exact (callWrite_words_ne _ _ _ _ _ _
        (slot_distinct s _ _ (callSlot_injective (by omega) (by omega) (Ne.symm he)))).trans
          (ih (by omega) (by omega))

theorem callsState_read320_written (s : GlobalState) (values : Nat → Words) (extra : Words)
    (hwf : s.WF) (hi : i < n) (hn : n ≤ 13) :
    (callsState s values extra n).mem.readAt (slot s (callSlot i)) 320 = limbBytes (values i) := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases he : i = n
    · subst i
      apply callWrite_read320 _ _ _ _ _ (call_destination_live s values extra hwf n n (by omega))
      intro hn6
      subst n
      exact callsState_slot_live s values extra hwf 7 6
    · exact (callWrite_read _ _ _ _ _ _ 320
        (slot_distinct s _ _ (callSlot_injective (by omega) (by omega) (Ne.symm he)))).trans
          (ih (by omega) (by omega))

theorem callsState_read_old (s : GlobalState) (values : Nat → Words) (extra : Words)
    (hwf : s.WF) {p : Pointer} {bytes : Nat} (h : SmallRange s.mem p bytes)
    (bits : Nat) (hbits : bits ≤ 8 * bytes) (n : Nat) :
    (callsState s values extra n).mem.readAt p bits = s.mem.readAt p bits := by
  induction n with
  | zero => exact allocate_read s hwf allocationSizes (h.fits.mono hbits)
  | succ n ih => exact (callWrite_read _ _ _ _ _ p bits
      (slot_caller_disjoint s hwf (callSlot n) p h)).trans ih

theorem callsState_words_old (s : GlobalState) (values : Nat → Words) (extra : Words)
    (hwf : s.WF) {p : Pointer} (h : SmallRange s.mem p 40) (n : Nat) :
    readLimbs (callsState s values extra n) p = readLimbs s p := by
  induction n with
  | zero =>
    funext i
    exact allocate_read s hwf allocationSizes
      (h.fits_add (k := 8*i.val) (count := 8) (by omega))
  | succ n ih => exact (callWrite_words_ne _ _ _ _ _ p
      (slot_caller_disjoint s hwf (callSlot n) p h)).trans ih

end Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline
