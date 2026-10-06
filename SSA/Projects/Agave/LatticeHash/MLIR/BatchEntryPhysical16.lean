/- Released under Apache 2.0 license as described in the file LICENSE. -/
import SSA.Projects.Agave.LatticeHash.MLIR.BatchRefinement16
import SSA.Projects.Agave.LatticeHash.MLIR.BatchState16

namespace AgaveLatticeHash.MLIR
open LeanMLIR SLLVM Firedancer
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

/-- The fully initialized physical caller image supplies both actual length
loads; the compiled entry starts the concrete scalar-prefix/memory invariant. -/
theorem physical_entry16 (entry : GlobalState) (src len out sched panic : Pointer)
    (p : AgavePhysicalStaging.Store) (a : AgaveStaging.Value)
    (hc : CallerMemory.Represents entry 16 src len out sched panic p a)
    (ms : Fin 16 → AgaveConcrete.Message)
    (hlen : ∀ lane, AgavePhysicalStaging.lengthAt p lane.val = (ms lane).length) :
    StateT.run (agave_batch_16.denote
      (Ctxt.Valuation.ofHVector [.value out, .value len, .value src]ₕ)) entry =
    StateT.run (agave_batch_16.blocks.run
      (BatchRefinement16.ambient16 entry src len out sched panic ms) (headerAt16 ms 0))
      (outerMemoryAt16 entry p ms 0) := by
  apply entry_to_header16 entry hc.wf src len out sched panic
  · exact hc.source.2.1
  · exact hc.lengths.2.1
  · have h := hc.read_length_run (by omega) 8 0 (by omega)
    have hp : len.withOffset 0 = len := by cases len; simp [Pointer.withOffset]
    simp only [Nat.zero_add] at h
    change readWord? (len.withOffset 0) 512 entry.mem = _ at h
    rw [hp] at h
    rw [h]
    congr 2
    apply Vector.ext
    intro i hi
    simp only [Vector.getElem_ofFn]
    rw [hlen ⟨i, by omega⟩]
  · have h := hc.read_length_run (by omega) 8 8 (by omega)
    change readWord? (len.withOffset 64) 512 entry.mem = _ at h
    rw [h]
    congr 2
    apply Vector.ext
    intro i hi
    simp only [Vector.getElem_ofFn]
    rw [show 8+i = i+8 by omega, hlen ⟨i+8, by omega⟩]
  · exact hc.schedule.1.1
  · exact hc.panic

end AgaveLatticeHash.MLIR
