import SSA.Projects.Agave.Ed25519.Proof.Avx2SquareNegateD.ExecutionMachine
import SSA.Projects.Agave.Ed25519.Proof.Reduce64.Execution.Memory

namespace Agave.Ed25519.Avx2SquareNegateD.Execution
open LeanMLIR.RIR

/-- The five input loads read the initial memory, before any output is stored. -/
def readBlocks (m : MemoryState) (p : Pointer) : Blocks :=
  fun i => Vector.ofFn fun j =>
    Ty.extractVecElem 8 32 j (m.readAt (p.add (BitVec.ofNat 64 (32*i.val))) 256)

/-- The five stores, preserving every byte outside the 160-byte result. -/
def storeBlocks (m : MemoryState) (p : Pointer) (v : Blocks) : MemoryState :=
  ((((m.storeAt p (BitVec.packLanes (v 0))).storeAt (p.add 32)
    (BitVec.packLanes (v 1))).storeAt (p.add 64) (BitVec.packLanes (v 2))).storeAt
    (p.add 96) (BitVec.packLanes (v 3))).storeAt (p.add 128) (BitVec.packLanes (v 4))

/-- The five writes preserve the allocation map invariant without inspecting
any arithmetic output. This lets `func_init` use its frame-free call rule. -/
@[mlir_mem]
theorem storeBlocks_wf (s : GlobalState) (p : Pointer) (v : Blocks) (h : s.WF) :
    ({s with mem := storeBlocks s.mem p v} : GlobalState).WF := by
  simpa only [storeBlocks, GlobalState.WF_storeAt] using h

/-- Stores retain the caller's live-allocation and size witness. -/
theorem storeBlocks_smallRange {m : MemoryState} {p : Pointer} {bytes : Nat}
    (h : Reduce64.Execution.SmallRange m p bytes) (dst : Pointer) (v : Blocks) :
    Reduce64.Execution.SmallRange (storeBlocks m dst v) p bytes := by
  exact ((((h.storeAt _ _).storeAt _ _).storeAt _ _).storeAt _ _).storeAt _ _

end Agave.Ed25519.Avx2SquareNegateD.Execution
