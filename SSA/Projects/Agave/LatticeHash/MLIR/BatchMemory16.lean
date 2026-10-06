/- Released under Apache 2.0 license as described in the file LICENSE. -/
import SSA.Projects.Agave.LatticeHash.MLIR.BatchProof16
import SSA.Projects.Agave.LatticeHash.MLIR.BatchTranspose16
import SSA.Projects.Agave.LatticeHash.MLIR.CallerPacking
import SSA.Projects.Agave.LatticeHash.MLIR.OutputRead
import SSA.Projects.Agave.LatticeHash.MLIR.CompressionSpec

namespace AgaveLatticeHash.MLIR
open LeanMLIR SLLVM Firedancer
open Blake3Compression CompressionExit

/-- Memory part of the batch16 outer-loop invariant. All caller allocations
are unchanged before the root-output loop; both local scratch buffers remain
valid across the repeatedly executed transpose stores. -/
structure BatchMemory16 (entry current : GlobalState) : Prop where
  caller : FrameBelow entry.alloc.nextFreeBlock entry current
  scratch : ∀ i : Fin 2, Fits current.mem (BatchEntry16.scratch entry i) 8192

theorem batchMemory16_entry (s : GlobalState) : BatchMemory16 s (BatchEntry16.entryState s) :=
  ⟨BatchEntry16.entryState_frame s, BatchEntry16.scratch_fits s⟩

/-- Every complete compiler transpose preserves the outer memory invariant,
regardless of the data written into either local scratch buffer. -/
theorem BatchMemory16.transpose {entry current : GlobalState}
    (h : BatchMemory16 entry current) (i : Fin 2) (rows : Vector (Vector Word 16) 16) :
    BatchMemory16 entry {current with mem := outputMem (BatchEntry16.scratch entry i) (BatchTranspose16.columns16 rows) 16 current.mem} := by
  constructor
  · intro b hb
    apply Eq.trans (outputMem_frame _ _ _ _ b ?_) (h.caller b hb)
    intro heq
    have hid := BatchEntry16.scratch_id entry i
    have hbid := congrArg BlockId.id heq
    omega
  · intro j
    dsimp only
    exact fits_outputMem (BatchEntry16.scratch entry i) (BatchTranspose16.columns16 rows) 16 (h.scratch j)

/-- Original caller reads are preserved at every represented loop header. -/
theorem BatchMemory16.read {entry current : GlobalState}
    (h : BatchMemory16 entry current) (hs : entry.WF) {p : Pointer} {w : Nat}
    (hf : Fits entry.mem p w) : readWord? p w current.mem = readWord? p w entry.mem := by
  apply readWord?_of_live?_eq
  exact h.caller p.id (lt_nextFreeBlock_of_fits hs hf)

/-- A represented scalar offset admits a complete AVX512 source-row load. -/
theorem sourceRow16_fits {s : GlobalState} {src : Pointer}
    (hf : Fits s.mem src 131072) (lane : Fin 16) (len iteration : Nat) (hlen : len ≤ 1024) :
    Fits s.mem (src.withOffset (BitVec.ofNat 64 (1024*lane.val + batchOffset len iteration))) 512 := by
  have hb := batchOffset_le_960 len iteration hlen
  have hi := lane.isLt
  have hm : (1024*lane.val + batchOffset len iteration) % 18446744073709551616 =
      1024*lane.val + batchOffset len iteration := Nat.mod_eq_of_lt (by omega)
  apply Fits.mono (remainingFits s.mem src hf (BitVec.ofNat 64 (1024*lane.val + batchOffset len iteration)) ?_)
  · simp only [BitVec.toNat_ofNat, hm]
    omega
  · simp only [BitVec.toNat_ofNat, hm]
    omega

/-- Derive the transpose's physical source-row premises from the caller image
and the outer-loop memory frame. The rows include retained suffix bytes. -/
theorem BatchMemory16.source_row {entry current : GlobalState}
    (h : BatchMemory16 entry current) {src len out sched panic : Pointer}
    {p : AgavePhysicalStaging.Store} {a : AgaveStaging.Value}
    (hc : CallerMemory.Represents entry 16 src len out sched panic p a)
    (lane : Fin 16) (messageLen iteration : Nat) (hlen : messageLen ≤ 1024) :
    Fits current.mem (src.withOffset (BitVec.ofNat 64 (1024*lane.val + batchOffset messageLen iteration))) 512 ∧
    readWord? (src.withOffset (BitVec.ofNat 64 (1024*lane.val + batchOffset messageLen iteration))) 512 current.mem =
      some (packBits (CallerMemory.wordsLE 16 (fun i =>
        AgavePhysicalStaging.memoryAt p lane.val (batchOffset messageLen iteration+i)))) := by
  have hf := sourceRow16_fits hc.source.2.1 lane messageLen iteration hlen
  constructor
  · exact fits_of_live?_eq (h.caller _ (lt_nextFreeBlock_of_fits hc.wf hf)) hf
  · rw [h.read hc.wf hf]
    apply hc.read_source_words (by omega) lane 16 (batchOffset messageLen iteration)
    have := batchOffset_le_960 messageLen iteration hlen
    omega

/-- Readback of the complete transpose store sequence establishes the exact
message-memory contract used by the checked sixteen-lane compression rounds. -/
theorem BatchMemory16.message {entry current : GlobalState}
    (h : BatchMemory16 entry current) (rows : Vector (Vector Word 16) 16) :
    CompressionMessage
      (outputMem (BatchEntry16.scratch entry 0) (BatchTranspose16.columns16 rows) 16 current.mem)
      (BatchEntry16.scratch entry 0) (BatchTranspose16.columns16 rows) := by
  constructor
  · exact fits_outputMem (BatchEntry16.scratch entry 0) (BatchTranspose16.columns16 rows) 16 (h.scratch 0)
  · intro i
    apply outputMem_read_row _ _ _ (h.scratch 0) _ 16 (by omega) i i.isLt
    simp [BatchEntry16.scratch_zero]

/-- The retained-root memcpy also stays within the two local allocations. -/
theorem BatchMemory16.copy {entry current : GlobalState}
    (h : BatchMemory16 entry current) (i : Fin 2) (bytes : BitVec 8192) :
    BatchMemory16 entry {current with mem := current.mem.splice (BatchEntry16.scratch entry i) bytes} := by
  constructor
  · apply FrameBelow.splice (hf := h.caller)
    rw [BatchEntry16.scratch_id]
    omega
  · intro j
    dsimp only
    exact fits_splice (h.scratch j)

/-- Copying the complete transposed message preserves its per-word vector
contract at the retained-root destination. This establishes same-allocation
subread facts from the actual full-width memcpy write. -/
theorem copyMessage16 {m : MemoryState} {src dst : Pointer}
    {words : State (Vector Word 16)} (hmsg : CompressionMessage m src words)
    (hfit : Fits m dst 8192) (hsrc : src.offset = 0) (hdst : dst.offset = 0)
    (bytes : BitVec 8192) (hr : readWord? src 8192 m = some bytes) :
    CompressionMessage (m.splice dst bytes) dst words := by
  constructor
  · exact fits_splice hfit
  · intro i
    have hs : (src.withOffset (BitVec.ofNat 64 (64*i.val))).offsetInBits =
        src.offsetInBits + 512*i.val := by
      have hh := offsetInBits_withOffset_nat src (64*i.val) (by simp [hsrc]; have := i.isLt; omega)
      simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hh
    have hd : (dst.withOffset (BitVec.ofNat 64 (64*i.val))).offsetInBits =
        dst.offsetInBits + 512*i.val := by
      have hh := offsetInBits_withOffset_nat dst (64*i.val) (by simp [hdst]; have := i.isLt; omega)
      simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hh
    have hsread := readWord?_extract (q := src.withOffset (BitVec.ofNat 64 (64*i.val))) bytes hmsg.fits hr rfl hs
      (show 512*i.val + 512 ≤ 8192 by have := i.isLt; omega)
    have hrow := hmsg.read i
    have hbits : bytes.extractLsb' (512*i.val) 512 = packBits (words i) := by
      exact Option.some.inj (hsread.symm.trans hrow)
    have hdread := readWord?_extract (q := dst.withOffset (BitVec.ofNat 64 (64*i.val))) bytes (fits_splice hfit)
      (readWord?_splice_self bytes hfit) rfl hd
      (show 512*i.val + 512 ≤ 8192 by have := i.isLt; omega)
    rw [hbits] at hdread
    exact hdread

end AgaveLatticeHash.MLIR
