/- Released under Apache 2.0 license as described in the file LICENSE. -/
import SSA.Projects.Agave.LatticeHash.MLIR.CallerPacking
import SSA.Projects.Agave.LatticeHash.MLIR.BatchMemory16

namespace AgaveLatticeHash.MLIR.CallerMemory
open LeanMLIR SLLVM Firedancer

def rows16 (p : AgavePhysicalStaging.Store) (ms : Fin 16 → AgaveConcrete.Message)
    (iteration : Nat) : Vector (Vector (BitVec 32) 16) 16 :=
  Vector.ofFn fun lane => wordsLE 16 (fun i => AgavePhysicalStaging.memoryAt p lane.val
    (batchOffset (ms lane).length iteration+i))

/-- Every word of the compiled sixteen-lane transpose is its retained input
word, including inactive lanes stalled at their final block. -/
theorem columns16_retained (p : AgavePhysicalStaging.Store)
    (ms : Fin 16 → AgaveConcrete.Message) (iteration : Nat) (word lane : Fin 16) :
    (BatchTranspose16.columns16 (rows16 p ms iteration) word)[lane.val] =
      AgaveConcrete.decodeBlock (AgaveBatchControl.loadBlock (AgavePhysicalStaging.memoryAt p lane.val)
        (min iteration (AgaveBatchControl.rootIndex (ms lane).length))) word := by
  simp [BatchTranspose16.columns16, rows16, wordsLE, AgaveConcrete.decodeBlock,
    AgaveBatchControl.loadBlock, batchOffset]

/-- Retained padding validity identifies the actual AVX512 transpose output
with the scalar compression block without requiring zeroed stale suffixes. -/
theorem columns16_scalarBlock (p : AgavePhysicalStaging.Store)
    (ms : Fin 16 → AgaveConcrete.Message) (iteration : Nat)
    (hstage : ∀ lane, AgaveBatchControl.ValidStaging (ms lane).length 1024
      (AgaveConcrete.bytes (ms lane)) (AgavePhysicalStaging.memoryAt p lane.val))
    (word lane : Fin 16) :
    (BatchTranspose16.columns16 (rows16 p ms iteration) word)[lane.val] =
      AgaveConcrete.decodeBlock (AgaveBatchControl.scalarBlock (AgaveConcrete.bytes (ms lane))
        (ms lane).length (min iteration (AgaveBatchControl.rootIndex (ms lane).length))) word := by
  rw [columns16_retained, AgaveBatchControl.load_eq_scalarBlock (hstage lane) (Nat.min_le_right ..)]

end AgaveLatticeHash.MLIR.CallerMemory
