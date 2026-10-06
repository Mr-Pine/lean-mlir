/- Released under Apache 2.0 license as described in the file LICENSE. -/
import SSA.Projects.Agave.LatticeHash.MLIR.CallerPacking
import SSA.Projects.Agave.LatticeHash.MLIR.BatchMemory8

namespace AgaveLatticeHash.MLIR.CallerMemory
open LeanMLIR SLLVM Firedancer
open BatchLoads BatchFirstHalf

private theorem sourceAt_uniform (src : Pointer) (lane : Fin 8) :
    sourceAt src lane = src.withOffset (BitVec.ofNat 64 (1024*lane.val)) := by
  by_cases hz : lane.val = 0
  · simp [sourceAt, hz, Pointer.withOffset]
  · simp only [sourceAt, hz, ↓reduceIte]

/-- The compiler's nested row addressing equals the contiguous caller-image address. -/
theorem row_address8 (src : Pointer) (ms : Fin 8 → AgaveConcrete.Message)
    (iteration : Nat) (lane : Fin 8) (half : Nat) :
    rowPtr (sourceAt src lane) (wordAt ms iteration lane + BitVec.ofNat 64 (8*half)) =
      src.withOffset (BitVec.ofNat 64
        (1024*lane.val + (batchOffset (ms lane).length iteration + 32*half))) := by
  rw [sourceAt_uniform]
  unfold rowPtr wordAt
  rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, ← BitVec.ofNat_add, ← BitVec.ofNat_mul]
  have hn : (16 * min iteration (AgaveBatchControl.rootIndex (ms lane).length) + 8*half)*4 =
      batchOffset (ms lane).length iteration + 32*half := by unfold batchOffset; omega
  rw [hn]
  simp only [Pointer.withOffset, BitVec.ofNat_add, BitVec.add_assoc]

def rows8 (p : AgavePhysicalStaging.Store) (ms : Fin 8 → AgaveConcrete.Message)
    (iteration half : Nat) : Vector (Vector (BitVec 32) 8) 8 :=
  Vector.ofFn fun lane => wordsLE 8 (fun i => AgavePhysicalStaging.memoryAt p lane.val
    (batchOffset (ms lane).length iteration + 32*half+i))

/-- All bounds and read values for either actual load half follow from the
caller representation and the frame invariant; no per-load premise remains. -/
theorem represented_row8 {entry current : GlobalState} {src len out sched panic : Pointer}
    {p : AgavePhysicalStaging.Store} {a : AgaveStaging.Value}
    (h : Represents entry 8 src len out sched panic p a) (hm : BatchMemory8 entry current)
    (ms : Fin 8 → AgaveConcrete.Message) (iteration : Nat)
    (hms : ∀ lane, (ms lane).length ≤ 1024) (lane : Fin 8) (half : Nat) (hh : half ≤ 1) :
    Fits current.mem (rowPtr (sourceAt src lane)
      (wordAt ms iteration lane + BitVec.ofNat 64 (8*half))) 256 ∧
    readWord? (rowPtr (sourceAt src lane)
      (wordAt ms iteration lane + BitVec.ofNat 64 (8*half))) 256 current.mem =
      some (packBits (rows8 p ms iteration half)[lane.val]) := by
  have hb := batchOffset_le_960 (ms lane).length iteration (hms lane)
  have hl := lane.isLt
  have hoff : 1024*lane.val+(batchOffset (ms lane).length iteration+32*half) < 2^64 := by omega
  have hnat : (BitVec.ofNat 64
      (1024*lane.val+(batchOffset (ms lane).length iteration+32*half))).toNat =
      1024*lane.val+(batchOffset (ms lane).length iteration+32*half) := by
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hoff]
  have hf : Fits entry.mem
      (src.withOffset (BitVec.ofNat 64 (1024*lane.val+(batchOffset (ms lane).length iteration+32*half)))) 256 := by
    have hrem := remainingFits entry.mem src h.source.2.1
      (BitVec.ofNat 64 (1024*lane.val+(batchOffset (ms lane).length iteration+32*half))) (by rw [hnat]; omega)
    exact Fits.mono hrem (by rw [hnat]; omega)
  rw [row_address8]
  refine ⟨fits_of_live?_eq (hm.caller _ (lt_nextFreeBlock_of_fits h.wf hf)) hf, ?_⟩
  rw [hm.read h.wf hf]
  simpa only [rows8, Vector.getElem_ofFn] using
    h.read_source_words (by decide) lane 8 (batchOffset (ms lane).length iteration+32*half) (by omega)

/-- The four hypotheses consumed by the complete AVX2 transpose path. -/
theorem represented_loads8 {entry current : GlobalState} {src len out sched panic : Pointer}
    {p : AgavePhysicalStaging.Store} {a : AgaveStaging.Value}
    (h : Represents entry 8 src len out sched panic p a) (hm : BatchMemory8 entry current)
    (ms : Fin 8 → AgaveConcrete.Message) (iteration : Nat)
    (hms : ∀ lane, (ms lane).length ≤ 1024) :
    (∀ lane, Fits current.mem (rowPtr (sourceAt src lane) (wordAt ms iteration lane)) 256) ∧
    (∀ lane, readWord? (rowPtr (sourceAt src lane) (wordAt ms iteration lane)) 256 current.mem =
      some (packBits (rows8 p ms iteration 0)[lane.val])) ∧
    (∀ lane, Fits current.mem (rowPtr (sourceAt src lane) (wordAt ms iteration lane + 8)) 256) ∧
    (∀ lane, readWord? (rowPtr (sourceAt src lane) (wordAt ms iteration lane + 8)) 256 current.mem =
      some (packBits (rows8 p ms iteration 1)[lane.val])) := by
  have lo (lane : Fin 8) := represented_row8 h hm ms iteration hms lane 0 (by decide)
  have hi (lane : Fin 8) := represented_row8 h hm ms iteration hms lane 1 (by decide)
  have hz (v : BitVec 64) : v + BitVec.ofNat 64 (8*0) = v := BitVec.add_zero v
  simp only [hz] at lo
  exact ⟨fun lane => (lo lane).1, fun lane => (lo lane).2,
    fun lane => (hi lane).1, fun lane => (hi lane).2⟩

/-- The actual two-half transpose gives exactly each lane's retained block
words, including lanes stalled at their root block. -/
theorem columns8_retained (p : AgavePhysicalStaging.Store)
    (ms : Fin 8 → AgaveConcrete.Message) (iteration : Nat) (word : Fin 16) (lane : Fin 8) :
    (BatchTranspose.columns8 (BatchTransposePath.lowColumns (rows8 p ms iteration 0))
      (rows8 p ms iteration 1) word)[lane.val] =
      AgaveConcrete.decodeBlock (AgaveBatchControl.loadBlock (AgavePhysicalStaging.memoryAt p lane.val)
        (min iteration (AgaveBatchControl.rootIndex (ms lane).length))) word := by
  by_cases hw : word.val < 8
  · simp [BatchTranspose.columns8, hw, BatchTransposePath.lowColumns, rows8, wordsLE,
      AgaveConcrete.decodeBlock, AgaveBatchControl.loadBlock, batchOffset]
  · simp [BatchTranspose.columns8, hw, Vector.getElem_ofFn,
      rows8, wordsLE, AgaveConcrete.decodeBlock, AgaveBatchControl.loadBlock, batchOffset,
      Fin.getElem_fin]
    have hi (base k : Nat) : base+32+(4*(word.val-8)+k) = base+(4*word.val+k) := by omega
    have hi0 (base : Nat) : base+32+4*(word.val-8) = base+4*word.val := by omega
    simp only [hi, hi0]

/-- Padding correctness bridges the actual loaded/transposed words to the
independent scalar block, without requiring canonical zeroes in stale suffixes. -/
theorem columns8_scalarBlock (p : AgavePhysicalStaging.Store)
    (ms : Fin 8 → AgaveConcrete.Message) (iteration : Nat)
    (hstage : ∀ lane, AgaveBatchControl.ValidStaging (ms lane).length 1024
      (AgaveConcrete.bytes (ms lane)) (AgavePhysicalStaging.memoryAt p lane.val))
    (word : Fin 16) (lane : Fin 8) :
    (BatchTranspose.columns8 (BatchTransposePath.lowColumns (rows8 p ms iteration 0))
      (rows8 p ms iteration 1) word)[lane.val] =
      AgaveConcrete.decodeBlock (AgaveBatchControl.scalarBlock (AgaveConcrete.bytes (ms lane))
        (ms lane).length (min iteration (AgaveBatchControl.rootIndex (ms lane).length))) word := by
  rw [columns8_retained, AgaveBatchControl.load_eq_scalarBlock (hstage lane) (Nat.min_le_right ..)]

end AgaveLatticeHash.MLIR.CallerMemory
