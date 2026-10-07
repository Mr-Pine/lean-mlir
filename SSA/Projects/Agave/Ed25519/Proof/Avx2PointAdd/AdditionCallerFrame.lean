import SSA.Projects.Agave.Ed25519.Proof.Avx2PointAdd.PhasePipeline
import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionAvx2DalekAdapterFrame

namespace Agave.Ed25519.DoubleBase.ExecutionAvx2
open LeanMLIR.RIR
open Avx2PointAdd.Phases

/-- The exact point-add store frame preserves every caller-visible old byte
when all six written allocations belong to the private call stack. -/
theorem CallerFrame.pointAdd (h : CallerFrame initial before out)
    (hf : OutputFrame q before after)
    (hprivate : ∀ k, initial.alloc.nextFreeBlock ≤ (q.written k).id.id) :
    CallerFrame initial after out := by
  refine ⟨hf.wellFormed, fun p bytes hp => hf.live p bytes (h.live p bytes hp), ?_⟩
  intro p width hp hdis
  have hne : ∀ k, (q.written k).id ≠ p.id := by
    intro k he
    have hid := congrArg (fun id => id.id) he
    have hk := hprivate k
    omega
  exact (hf.read p width hne).trans (h.read p width hp hdis)

theorem pipelineState_callerFrame (h : CallerFrame initial s out)
    (hprivate : ∀ k, initial.alloc.nextFreeBlock ≤ (q.written k).id.id)
    (negative : Bool) (P C : Avx2PointAdd.Point) (stage : Fin 8) :
    CallerFrame initial (pipelineState s q negative P C stage) out :=
  h.pointAdd (pipelineState_frame s q negative P C h.wellFormed stage) hprivate

/-- Packed cached rows outside the six scratch allocations are unchanged. -/
theorem pointAddFrame_packedPoint (hf : OutputFrame q before after)
    (hp : ∀ k, (q.written k).id ≠ ptr.id) :
    packedPoint after.mem ptr = packedPoint before.mem ptr := by
  have hblocks : Avx2FieldMul.Execution.readBlocks after.mem ptr =
      Avx2FieldMul.Execution.readBlocks before.mem ptr := by
    funext i
    unfold Avx2FieldMul.Execution.readBlocks
    rw [hf.read _ 256 (by simpa using hp)]
  simp only [packedPoint, hblocks]

/-- The backend's concrete output, scratch and cached-table invariant is
preserved by the exact point-add frame when the cached table is separate. -/
theorem BackendReady.of_pointAddFrame (h : BackendReady r table slots A E before)
    (hf : OutputFrame q before after)
    (ht : ∀ k, (q.written k).id ≠ table.id) :
    BackendReady r table slots A E after := by
  refine ⟨h.outputRegisters, hf.wellFormed, hf.live r 160 h.output,
    fun i => hf.live (slots i) 160 (h.scratch i),
    hf.live table 1280 h.tableRange, ?_⟩
  intro k
  rw [pointAddFrame_packedPoint hf (by simpa using ht)]
  exact h.tableValues k

end Agave.Ed25519.DoubleBase.ExecutionAvx2
