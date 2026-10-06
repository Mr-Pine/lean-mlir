/- Released under Apache 2.0 license as described in the file LICENSE. -/
import SSA.Projects.Agave.LatticeHash.MLIR.CallerBatch16

namespace AgaveLatticeHash.MLIR
open LeanMLIR SLLVM Firedancer
open Blake3Compression CompressionExit

/-- Concrete memory at the compiler's outer-loop header after `iteration`
nonroot iterations: entry allocation followed by the actual sixteen scratch
stores for each visited block. Pure compression and updates do not alter it. -/
def outerMemoryAt16 (entry : GlobalState) (p : AgavePhysicalStaging.Store)
    (ms : Fin 16 → AgaveConcrete.Message) : Nat → GlobalState
  | 0 => BatchEntry16.entryState entry
  | iteration+1 =>
    let prev := outerMemoryAt16 entry p ms iteration
    {prev with mem := outputMem (BatchEntry16.scratch entry 0) (BatchTranspose16.columns16 (CallerMemory.rows16 p ms iteration)) 16 prev.mem}

/-- The caller-frame and scratch-validity invariant holds for every concrete
outer iteration, independently of the lane lengths or message contents. -/
theorem outerMemoryAt16_invariant (entry : GlobalState) (p : AgavePhysicalStaging.Store)
    (ms : Fin 16 → AgaveConcrete.Message) (iteration : Nat) :
    BatchMemory16 entry (outerMemoryAt16 entry p ms iteration) := by
  induction iteration with
  | zero => exact batchMemory16_entry entry
  | succ iteration ih => exact ih.transpose 0 (CallerMemory.rows16 p ms iteration)

/-- Every physical source-row read needed by the actual transpose follows
from the initialized caller image at each reachable scalar-prefix iteration. -/
theorem outerMemoryAt16_source (entry : GlobalState) (p : AgavePhysicalStaging.Store)
    (ms : Fin 16 → AgaveConcrete.Message) (iteration : Nat)
    {src len out sched panic : Pointer} {a : AgaveStaging.Value}
    (hc : CallerMemory.Represents entry 16 src len out sched panic p a)
    (hms : ∀ lane, (ms lane).length ≤ 1024) (lane : Fin 16) :
    Fits (outerMemoryAt16 entry p ms iteration).mem
      (src.withOffset (BitVec.ofNat 64 (1024*lane.val + batchOffset (ms lane).length iteration))) 512 ∧
    readWord? (src.withOffset (BitVec.ofNat 64 (1024*lane.val + batchOffset (ms lane).length iteration)))
      512 (outerMemoryAt16 entry p ms iteration).mem =
      some (packBits (CallerMemory.rows16 p ms iteration)[lane]) := by
  simp only [CallerMemory.rows16, Fin.getElem_fin, Vector.getElem_ofFn]
  exact (outerMemoryAt16_invariant entry p ms iteration).source_row hc lane
    (ms lane).length iteration (hms lane)

/-- After the next actual transpose, all sixteen word-major vectors read
back exactly as required by the checked compression loop. -/
theorem outerMemoryAt16_message (entry : GlobalState) (p : AgavePhysicalStaging.Store)
    (ms : Fin 16 → AgaveConcrete.Message) (iteration : Nat) :
    CompressionMessage (outerMemoryAt16 entry p ms (iteration+1)).mem
      (BatchEntry16.scratch entry 0)
      (BatchTranspose16.columns16 (CallerMemory.rows16 p ms iteration)) := by
  simp only [outerMemoryAt16]
  exact (outerMemoryAt16_invariant entry p ms iteration).message (CallerMemory.rows16 p ms iteration)

end AgaveLatticeHash.MLIR
