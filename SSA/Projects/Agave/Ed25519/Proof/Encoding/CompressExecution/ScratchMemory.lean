import SSA.Projects.Agave.Ed25519.Proof.Encoding.CompressExecution.Prefix
import SSA.Projects.Agave.Ed25519.Proof.SerialPoint.CallMemory

namespace Agave.Ed25519.Encoding.Compress.Execution
open LeanMLIR.RIR
open Reduce64.Execution (SmallRange)
open SerialFieldMul (readLimbs)

variable {s initial : GlobalState} {p : Pointer}

theorem scratchState_wf (h : s.WF) (n : Nat) : (scratchState s n).WF := by
  induction n with
  | zero => exact h
  | succ n ih => exact ih.alloca

theorem scratchState_live (hwf : s.WF) (h : SmallRange s.mem p bytes) (n : Nat) :
    SmallRange (scratchState s n).mem p bytes := by
  induction n with
  | zero => exact h
  | succ n ih => exact SerialPoint.Execution.smallRange_alloca (scratchState_wf hwf n) ih

@[simp] theorem scratch_id (s : GlobalState) (n : Nat) :
    (scratch s n).id.id = s.alloc.nextFreeBlock + n := by
  have hc : (scratchState s n).alloc.nextFreeBlock = s.alloc.nextFreeBlock + n := by
    induction n with
    | zero => simp [scratchState]
    | succ n ih => simp [scratchState, GlobalState.alloca, ih, Nat.add_assoc]
  simp [scratch, GlobalState.allocaPtr, hc]

@[simp] theorem scratch_offset (s : GlobalState) (n : Nat) :
    (scratch s n).offset = 0 := rfl

theorem scratch_ne (s : GlobalState) (h : i ≠ j) :
    (scratch s i).id ≠ (scratch s j).id := by
  intro he
  have := congrArg BlockId.id he
  simp only [scratch_id] at this
  omega

theorem scratch_disjoint (s : GlobalState) (h : i ≠ j) (a b : BitVec 64) (v w : Nat) :
    (Range.of ((scratch s i).add a) v).Disjoint (Range.of ((scratch s j).add b) w) :=
  Or.inl (scratch_ne s h)

theorem scratch_ne_old (hwf : s.WF) (h : Fits s.mem p bits) (n : Nat) :
    (scratch s n).id ≠ p.id := by
  have hp := hwf.lt h.mem
  intro he
  have := congrArg BlockId.id he
  simp only [scratch_id] at this
  omega

theorem scratchBytes_small (n : Nat) : scratchBytes n < 2^63 := by
  unfold scratchBytes
  split <;> norm_num

theorem scratch_live (hwf : s.WF) (hi : i < n) :
    SmallRange (scratchState s n).mem (scratch s i) (scratchBytes i) := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases he : i = n
    · subst i
      exact SerialPoint.Execution.smallRange_alloca_self _ _ (scratchBytes_small n)
    · exact SerialPoint.Execution.smallRange_alloca (scratchState_wf hwf n) (ih (by omega))

theorem scratchState_fits (hwf : s.WF) (h : Fits s.mem p bits) (n : Nat) :
    Fits (scratchState s n).mem p bits := by
  induction n with
  | zero => exact h
  | succ n ih => exact ih.alloca (scratchState_wf hwf n)

theorem scratchState_readAt (hwf : s.WF) (h : Fits s.mem p bits) (n w : Nat) :
    (scratchState s n).mem.readAt p w = s.mem.readAt p w := by
  induction n with
  | zero => rfl
  | succ n ih =>
    exact (MemoryState.readAt_alloca (scratchState_wf hwf n)
      (scratchState_fits hwf h n)).trans ih

theorem scratchState_readLimbs (hwf : s.WF) (h : SmallRange s.mem p 40) (n : Nat) :
    readLimbs (scratchState s n) p = readLimbs s p := by
  funext i
  exact scratchState_readAt hwf (h.fits_add (k := 8*i.val) (count := 8) (by omega)) n 64

theorem copyFirst_wf (h : s.WF) : (copyFirst initial s).WF := by
  simpa only [copyFirst, GlobalState.WF_storeAt] using h

theorem copySecond_wf (h : s.WF) : (copySecond initial s).WF := by
  simpa only [copySecond, GlobalState.WF_storeAt] using (copyFirst_wf (initial := initial) h)

theorem copyFirst_live (h : SmallRange s.mem p bytes) :
    SmallRange (copyFirst initial s).mem p bytes := h.storeAt _ _

theorem copySecond_live (h : SmallRange s.mem p bytes) :
    SmallRange (copySecond initial s).mem p bytes := (copyFirst_live h).storeAt _ _

/-- A 40-byte copy transports all five limbs, including for unaligned pointers. -/
theorem readLimbs_copy (s : GlobalState) (dst src : Pointer)
    (hd : SmallRange s.mem dst 40) (hs : SmallRange s.mem src 40) :
    readLimbs {s with mem := s.mem.storeAt dst (s.mem.readAt src 320)} dst =
      readLimbs s src := by
  funext i
  change (s.mem.storeAt dst (s.mem.readAt src 320)).readAt
      (dst.add (BitVec.ofNat 64 (8*i.val))) 64 =
    s.mem.readAt (src.add (BitVec.ofNat 64 (8*i.val))) 64
  have hi : (BitVec.ofNat 64 (8*i.val)).toNat * 8 + 64 ≤ 320 := by
    fin_cases i <;> decide
  rw [MemoryState.readAt_storeAt_add hd.fits (hd.no_wrap (by omega)) hi]
  exact (MemoryState.readAt_add_of_readAt hs.fits (hs.no_wrap (by omega)) hi rfl).symm

theorem readLimbs_storeAt_ne (s : GlobalState) (dst p : Pointer) (x : BitVec w)
    (hne : dst.id ≠ p.id) :
    readLimbs {s with mem := s.mem.storeAt dst x} p = readLimbs s p := by
  funext i
  change (s.mem.storeAt dst x).readAt (p.add (BitVec.ofNat 64 (8*i.val))) 64 = _
  exact MemoryState.readAt_storeAt_disjoint
    (show (Range.of dst w).Disjoint (Range.of (p.add (BitVec.ofNat 64 (8*i.val))) 64)
      from Or.inl hne) x

theorem copyFirst_readback (hd : SmallRange s.mem (scratch initial 3) 40)
    (hs : SmallRange s.mem (scratch initial 1) 40) :
    readLimbs (copyFirst initial s) (scratch initial 3) = readLimbs s (scratch initial 1) :=
  readLimbs_copy s _ _ hd hs

theorem copySecond_readback (hd : SmallRange s.mem (scratch initial 2) 40)
    (hs : SmallRange s.mem ((scratch initial 1).add 40) 40) :
    readLimbs (copySecond initial s) (scratch initial 2) =
      readLimbs s ((scratch initial 1).add 40) := by
  exact (readLimbs_copy (copyFirst initial s) _ _ (copyFirst_live hd) (copyFirst_live hs)).trans
    (readLimbs_storeAt_ne s _ _ _ (scratch_ne initial (by decide : 3 ≠ 1)))

theorem copySecond_first_readback (hd : SmallRange s.mem (scratch initial 3) 40)
    (hs : SmallRange s.mem (scratch initial 1) 40) :
    readLimbs (copySecond initial s) (scratch initial 3) = readLimbs s (scratch initial 1) := by
  exact (readLimbs_storeAt_ne (copyFirst initial s) _ _ _
    (scratch_ne initial (by decide : 2 ≠ 3))).trans (copyFirst_readback hd hs)

theorem copySecond_readLimbs_frame (h2 : (scratch initial 2).id ≠ p.id)
    (h3 : (scratch initial 3).id ≠ p.id) :
    readLimbs (copySecond initial s) p = readLimbs s p := by
  exact (readLimbs_storeAt_ne (copyFirst initial s) _ _ _ h2).trans
    (readLimbs_storeAt_ne s _ _ _ h3)

end Agave.Ed25519.Encoding.Compress.Execution
