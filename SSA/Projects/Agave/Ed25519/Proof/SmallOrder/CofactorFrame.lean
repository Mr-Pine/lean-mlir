import SSA.Projects.Agave.Ed25519.Proof.SmallOrder.CofactorMemory

namespace Agave.Ed25519.SmallOrder.Execution
open LeanMLIR.RIR SerialPoint SerialPoint.Execution SerialFieldMul
open Reduce64.Execution (SmallRange)
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

private theorem mulState_mem (s : GlobalState) (out a b : Pointer) :
    (mulState s out a b).mem = storeLimbs s.mem out (machine (readLimbs s a) (readLimbs s b)) := rfl

attribute [-simp] readLimbs_explicit in
/-- Conversion stores the four complete field arrays in their ABI order. -/
theorem convert4State_mem (s : GlobalState) (out input : Pointer)
    (hne : out.id ≠ input.id) :
    (convert4State s out input).mem =
      storePointWords s.mem out (pointToWords (asExtendedWord (readWordPoint s input))) := by
  simp (disch := simpa only [Pointer.add_id] using hne) only
    [convert4State, convert3State, mulState_mem, mulState_read_ne]
  simp [storePointWords, pointToWords, asExtendedWord, readWordPoint, storeLimbs,
    Pointer.add_add]

theorem storePointWords_erase (m : MemoryState) (out : Pointer) (v : PointWords) (mark : Nat) :
    (storePointWords m out v).eraseFrom mark = storePointWords (m.eraseFrom mark) out v := by
  simp only [storePointWords, MemoryState.eraseFrom_storeAt]

/-- Private writes disappear under the function's entry mark, leaving only
the final caller-visible twenty-word output. -/
theorem cofactorState_mem_exists (s : GlobalState) (out input : Pointer)
    (hwf : s.WF) (hout : SmallRange s.mem out 160) :
    ∃ v : WordPoint, (cofactorState s out input).mem = storePointWords s.mem out (pointToWords v) := by
  let s1 := s.alloca 160
  let s2 := s1.alloca 120
  let s3 := s2.alloca 120
  let base := s3.alloca 160
  let completedFinal := s.allocaPtr
  let temporary := s1.allocaPtr
  let projective := s2.allocaPtr
  let completedLoop := s3.allocaPtr
  let initialized := initialState base projective input
  let loop1 := loopState initialized completedLoop projective temporary
  let loop2 := loopState loop1 completedLoop projective temporary
  let completed := doubleState loop2 completedFinal projective
  refine ⟨asExtendedWord (readWordPoint completed completedFinal), ?_⟩
  have hne : out.id ≠ completedFinal.id := GlobalState.ne_allocaPtr_of_fits hwf hout.fits
  change (convert4State completed out completedFinal).mem.eraseFrom s.alloc.nextFreeBlock = _
  rw [convert4State_mem completed out completedFinal hne, storePointWords_erase]
  congr 1
  simp only [completed, loop2, loop1, initialized, loopState, initialState,
    doubleState, mulState, copyState, pointPost, storeLimbs, storePointWords,
    completedFinal, completedLoop, projective, temporary, base, s3, s2, s1]
  erase_frame

/-- Exact caller-memory normal form, with the noncanonical arithmetic word
representative identified by the independent readback proof. -/
theorem cofactorState_mem (s : GlobalState) (out input : Pointer)
    (hwf : s.WF) (hout : SmallRange s.mem out 160) (hin : SmallRange s.mem input 120) :
    (cofactorState s out input).mem =
      storePointWords s.mem out (pointToWords (eightTimesWord (readWordPoint s input))) := by
  obtain ⟨v, hv⟩ := cofactorState_mem_exists s out input hwf hout
  have hread : readWordPoint (cofactorState s out input) out = v := by
    rw [readWordPoint_eq]
    have hr : readPointWords (cofactorState s out input) out = pointToWords v := by
      funext i
      change (cofactorState s out input).mem.readAt _ _ = _
      rw [hv]
      exact storePointWords_readAt s.mem out (pointToWords v) hout i
    rw [hr, pointFromWords_toWords]
  rw [cofactorState_read s out input hwf hout hin] at hread
  simpa only [hread] using hv

/-- The whole function advances its allocation counter by nineteen and only
updates the caller's 160-byte point destination. -/
theorem cofactorState_eq_pointPost (s : GlobalState) (out input : Pointer)
    (hwf : s.WF) (hout : SmallRange s.mem out 160) (hin : SmallRange s.mem input 120) :
    cofactorState s out input =
      pointPost s out (pointToWords (eightTimesWord (readWordPoint s input))) 19 := by
  apply GlobalState.ext
  · exact congrArg AllocState.mk (cofactorState_alloc s out input)
  · exact cofactorState_mem s out input hwf hout hin

end Agave.Ed25519.SmallOrder.Execution
