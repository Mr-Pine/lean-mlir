/- Released under Apache 2.0 license as described in the file LICENSE. -/
import SSA.Projects.Agave.LatticeHash.MLIR.CallerBatch16

namespace AgaveLatticeHash.MLIR
open LeanMLIR SLLVM Firedancer Blake3Compression

def rootCVAt16 (ms : Fin 16 → AgaveConcrete.Message) (iteration : Nat) : CV (Vector Word 16) :=
  fun word => Vector.ofFn fun lane =>
    (AgaveBatchControl.stateAt AgaveConcrete.compress AgaveConcrete.iv
      (AgaveConcrete.bytes (ms lane)) (ms lane).length iteration).cv word

def rootSizes16 (ms : Fin 16 → AgaveConcrete.Message) (iteration : Nat) : Vector Word 16 :=
  Vector.ofFn fun lane => BitVec.ofNat 32
    (AgaveBatchControl.blockSize (ms lane).length (batchOffset (ms lane).length iteration))

def rootFlags16 (ms : Fin 16 → AgaveConcrete.Message) (iteration : Nat) : Vector Word 16 :=
  Vector.ofFn fun lane => BitVec.ofNat 32
    (AgaveBatchControl.blockFlags (ms lane).length (batchOffset (ms lane).length iteration))

/-- Once every lane is at its final block, the root parameters represented
by the compiler header yield exactly the scalar BLAKE3 one-chunk XOF words. -/
theorem rootCompression16_eq (p : AgavePhysicalStaging.Store)
    (ms : Fin 16 → AgaveConcrete.Message) (iteration : Nat)
    (hstage : ∀ lane, AgaveBatchControl.ValidStaging (ms lane).length 1024
      (AgaveConcrete.bytes (ms lane)) (AgavePhysicalStaging.memoryAt p lane.val))
    (hdone : ∀ lane, AgaveBatchControl.rootIndex (ms lane).length ≤ iteration)
    (counter : Fin 32) (lane : Fin 16) :
    scalarCompress (fun word => (rootCVAt16 ms iteration word)[lane])
      (fun word => (BatchTranspose16.columns16 (CallerMemory.rows16 p ms iteration) word)[lane])
      (BitVec.ofNat 64 counter.val) (rootSizes16 ms iteration)[lane] (rootFlags16 ms iteration)[lane] =
      AgaveConcrete.oneChunkWords (ms lane) counter := by
  have hm : (fun word => (BatchTranspose16.columns16 (CallerMemory.rows16 p ms iteration) word)[lane]) =
      AgaveConcrete.decodeBlock (AgaveBatchControl.scalarBlock (AgaveConcrete.bytes (ms lane))
        (ms lane).length (AgaveBatchControl.rootIndex (ms lane).length)) := by
    funext word
    simpa only [Fin.getElem_fin, Nat.min_eq_right (hdone lane)] using
      CallerMemory.columns16_scalarBlock p ms iteration hstage word lane
  rw [hm]
  simp only [rootCVAt16, rootSizes16, rootFlags16, Fin.getElem_fin, Vector.getElem_ofFn,
    AgaveBatchControl.stateAt, batchOffset, Nat.min_eq_right (hdone lane),
    AgaveBatchControl.root_size, AgaveBatchControl.root_flags,
    AgaveConcrete.oneChunkWords, AgaveBatchControl.scalarXofAt, AgaveConcrete.xof,
    AgaveConcrete.counter, Nat.mul_zero, Nat.add_zero]

/-- A compiled 32-halfword output chunk uses exactly the scalar LtHash
coordinate `32*counter+half`, including its little-endian halfword choice. -/
theorem oneChunk_chunk_index (message : AgaveConcrete.Message)
    (counter half : Fin 32) :
    AgaveConcrete.oneChunk message ⟨32*counter.val+half.val, by have := counter.isLt; have := half.isLt; omega⟩ =
      AgaveLattice.halfWord (AgaveConcrete.oneChunkWords message counter ⟨half.val/2, by have := half.isLt; omega⟩)
        ⟨half.val%2, by omega⟩ := by
  have hc := counter.isLt
  have hh := half.isLt
  have hdiv : (32*counter.val+half.val)/32 = counter.val := by omega
  have hmod : (32*counter.val+half.val)%32 = half.val := by omega
  have htwo : (32*counter.val+half.val)%2 = half.val%2 := by omega
  simp only [AgaveConcrete.oneChunk, hdiv, hmod, htwo]

end AgaveLatticeHash.MLIR
