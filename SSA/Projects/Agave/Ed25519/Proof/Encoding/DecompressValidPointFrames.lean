import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.PointOutput
import SSA.Projects.RIR.Global

/-! Exact allocation-record preservation for the already checked final decoder
stores. Unlike a range-only frame, these equations also preserve allocation
lengths and therefore transport `ByteGlobal.Present`. Full-call preservation
still requires composition through the earlier decoder instructions. -/
namespace Agave.Ed25519.Encoding.Decompress.Valid
open LeanMLIR.RIR
open Execution

/-- The original success suffix changes only its scratch and output blocks.
Every other allocation record is exactly unchanged, not merely readable. -/
theorem finishPoint_allocation (s : GlobalState) (out scratch yptr q : Pointer)
    (payload : BitVec 1280) (hout : q.id ≠ out.id) (hscratch : q.id ≠ scratch.id) :
    (Decode.successState (Decode.finishPointState s scratch yptr) out payload).mem[q.id]? =
      s.mem[q.id]? := by
  simp only [Decode.successState, Decode.finishPointState]
  rw [MemoryState.getElem?_storeAt_ne (q := q) (p := out) hout,
    MemoryState.getElem?_storeAt_ne (q := q) (p := out.add 8#64) hout,
    MemoryState.getElem?_storeAt_ne (q := q) (p := scratch.add 88#64) hscratch,
    MemoryState.getElem?_storeAt_ne (q := q) (p := scratch.add 80#64) hscratch,
    MemoryState.getElem?_storeAt_ne (q := q) (p := scratch.add 40#64) hscratch]

theorem finishPoint_present (s : GlobalState) (out scratch yptr : Pointer)
    (payload : BitVec 1280) (g : ByteGlobal) (id : BlockId)
    (h : g.Present id s.mem) (hout : id ≠ out.id) (hscratch : id ≠ scratch.id) :
    g.Present id
      (Decode.successState (Decode.finishPointState s scratch yptr) out payload).mem :=
  (finishPoint_allocation s out scratch yptr (g.address id) payload hout hscratch).trans h

theorem rejection_allocation (s : GlobalState) (out q : Pointer) (hout : q.id ≠ out.id) :
    (Decode.rejectionState s out).mem[q.id]? = s.mem[q.id]? :=
  MemoryState.getElem?_storeAt_ne hout

theorem rejection_present (s : GlobalState) (out : Pointer) (g : ByteGlobal)
    (id : BlockId) (h : g.Present id s.mem) (hout : id ≠ out.id) :
    g.Present id (Decode.rejectionState s out).mem := h.storeAt hout

end Agave.Ed25519.Encoding.Decompress.Valid
