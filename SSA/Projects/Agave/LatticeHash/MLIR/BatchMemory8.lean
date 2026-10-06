/- Released under Apache 2.0 license as described in the file LICENSE. -/
import SSA.Projects.Agave.LatticeHash.MLIR.BatchProof
import SSA.Projects.Agave.LatticeHash.MLIR.BatchTransposePath
import SSA.Projects.Agave.LatticeHash.MLIR.OutputRead
import SSA.Projects.Agave.LatticeHash.MLIR.CompressionSpec

namespace AgaveLatticeHash.MLIR
open LeanMLIR SLLVM Firedancer
open Blake3Compression CompressionExit

/-- Memory part of the batch8 outer-loop invariant. All caller allocations
are unchanged before the root-output loop; both local scratch buffers remain
valid across the repeatedly executed transpose stores. -/
structure BatchMemory8 (entry current : GlobalState) : Prop where
  caller : FrameBelow entry.alloc.nextFreeBlock entry current
  scratch : ∀ i : Fin 2, Fits current.mem (BatchEntry.scratch entry i) 4096

theorem batchMemory8_entry (s : GlobalState) : BatchMemory8 s (BatchEntry.entryState s) :=
  ⟨BatchEntry.entryState_frame s, BatchEntry.scratch_fits s⟩

/-- Every complete compiler transpose preserves the outer memory invariant,
regardless of the data written into either local scratch buffer. -/
theorem BatchMemory8.transpose {entry current : GlobalState}
    (h : BatchMemory8 entry current) (i : Fin 2) (lo hi : Vector (Vector Word 8) 8) :
    BatchMemory8 entry {current with mem := outputMem (BatchEntry.scratch entry i) (BatchTranspose.columns8 lo hi) 16 current.mem} := by
  constructor
  · intro b hb
    apply Eq.trans (outputMem_frame _ _ _ _ b ?_) (h.caller b hb)
    intro heq
    have hid := BatchEntry.scratch_id entry i
    have hbid := congrArg BlockId.id heq
    omega
  · intro j
    dsimp only
    exact fits_outputMem (BatchEntry.scratch entry i) (BatchTranspose.columns8 lo hi) 16 (h.scratch j)

/-- Original caller reads are preserved at every represented loop header. -/
theorem BatchMemory8.read {entry current : GlobalState}
    (h : BatchMemory8 entry current) (hs : entry.WF) {p : Pointer} {w : Nat}
    (hf : Fits entry.mem p w) : readWord? p w current.mem = readWord? p w entry.mem := by
  apply readWord?_of_live?_eq
  exact h.caller p.id (lt_nextFreeBlock_of_fits hs hf)

theorem BatchMemory8.fits {entry current : GlobalState}
    (h : BatchMemory8 entry current) (hs : entry.WF) {p : Pointer} {w : Nat}
    (hf : Fits entry.mem p w) : Fits current.mem p w :=
  fits_of_live?_eq (h.caller p.id (lt_nextFreeBlock_of_fits hs hf)) hf

/-- The actual transpose store sequence supplies every message vector required
by the compiled compression round, including same-allocation readback. -/
theorem BatchMemory8.message {entry current : GlobalState}
    (h : BatchMemory8 entry current) (lo hi : Vector (Vector Word 8) 8) :
    CompressionMessage
      (outputMem (BatchEntry.scratch entry 0) (BatchTranspose.columns8 lo hi) 16 current.mem)
      (BatchEntry.scratch entry 0) (BatchTranspose.columns8 lo hi) := by
  constructor
  · exact fits_outputMem _ _ _ (h.scratch 0)
  · intro i
    apply outputMem_read_row _ _ _ (h.scratch 0) _ 16 (by omega) i i.isLt
    simp [BatchEntry.scratch_zero]

/-- The root-message copy also preserves every caller allocation and both
scratch extents. Its source bytes may be the complete current transpose. -/
theorem BatchMemory8.copy {entry current : GlobalState}
    (h : BatchMemory8 entry current) (bytes : BitVec 4096) :
    BatchMemory8 entry {current with mem := current.mem.splice (BatchEntry.scratch entry 1) bytes} := by
  constructor
  · apply FrameBelow.splice _ h.caller
    rw [BatchEntry.scratch_id]
    omega
  · intro i
    exact fits_splice (h.scratch i)

end AgaveLatticeHash.MLIR
