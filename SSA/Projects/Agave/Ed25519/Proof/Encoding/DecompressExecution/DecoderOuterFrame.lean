import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.DecoderOuterExecution

/-! Normalize the exact output suffixes after the real call-frame erase. The
only frame premise is the caller-visible memory identity of the earlier source
prefix; the scratch point is required to belong to the private frame. -/
namespace Agave.Ed25519.Encoding.Decompress.Execution
open LeanMLIR.RIR

namespace Decode

theorem finishPointState_erase (s : GlobalState) (point y : Pointer) (mark : Nat)
    (hprivate : mark ≤ point.id.id) :
    (finishPointState s point y).mem.eraseFrom mark = s.mem.eraseFrom mark := by
  simp only [finishPointState, MemoryState.eraseFrom_storeAt,
    MemoryState.storeAt_eraseFrom_of_le (p := point.add _) hprivate]

theorem outerSuccessState_erase (s : GlobalState) (out : Pointer)
    (d : OuterSuccessData) (mark : Nat) (hprivate : mark ≤ d.point.id.id) :
    (outerSuccessState s out d).mem.eraseFrom mark =
      ((s.mem.eraseFrom mark).storeAt (out.add 8#64)
        (finishPointBits (s.mem.readAt d.point 1280) (s.mem.readAt d.y 320))).storeAt out (1#64) := by
  simp only [outerSuccessState, successState, MemoryState.eraseFrom_storeAt]
  rw [finishPointState_erase s d.point d.y mark hprivate]

/-- Once the earlier prefix frame fact is supplied, all private point assembly
stores disappear and only the exact caller payload and tag remain. -/
theorem outerSuccessState_public (entry s : GlobalState) (out : Pointer)
    (d : OuterSuccessData)
    (hprivate : entry.alloc.nextFreeBlock ≤ d.point.id.id)
    (hframe : s.mem.eraseFrom entry.alloc.nextFreeBlock = entry.mem) :
    {outerSuccessState s out d with
      mem := (outerSuccessState s out d).mem.eraseFrom entry.alloc.nextFreeBlock} =
    {s with mem := (successState entry out
      (finishPointBits (s.mem.readAt d.point 1280) (s.mem.readAt d.y 320))).mem} := by
  apply GlobalState.ext
  · rfl
  · rw [outerSuccessState_erase s out d entry.alloc.nextFreeBlock hprivate, hframe]
    rfl

theorem outerRejectionState_public (entry s : GlobalState) (out : Pointer)
    (hframe : s.mem.eraseFrom entry.alloc.nextFreeBlock = entry.mem) :
    {rejectionState s out with
      mem := (rejectionState s out).mem.eraseFrom entry.alloc.nextFreeBlock} =
    {s with mem := (rejectionState entry out).mem} := by
  apply GlobalState.ext
  · rfl
  · simp only [rejectionState, MemoryState.eraseFrom_storeAt, hframe]

end Decode

namespace SqrtRatio

theorem executionOutputState_erase (s : GlobalState) (out : Pointer)
    (flag : BitVec 8) (root : BitVec 320) (mark : Nat) :
    (outputState s out flag root).mem.eraseFrom mark =
      ((s.mem.eraseFrom mark).storeAt out flag).storeAt (out.add 8#64) root := by
  simp only [outputState, MemoryState.eraseFrom_storeAt]

theorem executionOutputState_public (entry s : GlobalState) (out : Pointer)
    (flag : BitVec 8) (root : BitVec 320)
    (hframe : s.mem.eraseFrom entry.alloc.nextFreeBlock = entry.mem) :
    {outputState s out flag root with
      mem := (outputState s out flag root).mem.eraseFrom entry.alloc.nextFreeBlock} =
    {alloc := (outputState s out flag root).alloc,
      mem := (entry.mem.storeAt out flag).storeAt (out.add 8#64) root} := by
  apply GlobalState.ext
  · rfl
  · rw [executionOutputState_erase, hframe]

end SqrtRatio
end Agave.Ed25519.Encoding.Decompress.Execution
