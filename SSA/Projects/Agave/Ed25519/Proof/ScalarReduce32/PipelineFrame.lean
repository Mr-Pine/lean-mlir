import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.Pipeline
import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.Output

namespace Agave.Ed25519.ScalarReduce32.Execution
open LeanMLIR.RIR
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

/-- The actual allocation prefix disappears when its private frame is erased. -/
theorem allocationSchedule_erase (E : Env program.Γ) (s : GlobalState) (hwf : s.WF) :
    (allocationSchedule E s).2.mem.eraseFrom s.alloc.nextFreeBlock = s.mem := by
  unfold allocationSchedule
  repeat rw [GlobalState.eraseFrom_alloca_of_le (by simp [GlobalState.alloca] <;> omega)]
  exact hwf.eraseFrom

theorem unpackPhase_erase {E : Env program.Γ} {s : GlobalState} {a : Pointer}
    {scratch : Fin 4 → Pointer} {mark : Nat}
    (hl : ∀ i, mark ≤ (scratch i).id.id) :
    (unpackPhaseResult E s a scratch).2.mem.eraseFrom mark = s.mem.eraseFrom mark := by
  simp only [unpackPhaseResult, unpackScratch0Result, unpackScratch1Result,
    unpackScratch2Result, unpackScratch3Result, MemoryState.eraseFrom_storeAt,
    MemoryState.storeAt_eraseFrom_of_le (hl _)]

theorem productPhase_erase {s : GlobalState} {x : Fin 5 → BitVec 64}
    {scratch : Fin 9 → Pointer} {mark : Nat}
    (hl : ∀ i, mark ≤ (scratch i).id.id) :
    (productPhaseState s x scratch).mem.eraseFrom mark = s.mem.eraseFrom mark := by
  simp only [productPhaseState, MemoryState.eraseFrom_storeAt,
    MemoryState.storeAt_eraseFrom_of_le (hl _)]

theorem subtractState_erase {s : GlobalState} {x : Fin 5 → BitVec 52}
    {scratch : Fin 5 → Pointer} {mark : Nat}
    (hl : ∀ i, mark ≤ (scratch i).id.id) :
    (subtractState s x scratch).mem.eraseFrom mark = s.mem.eraseFrom mark := by
  simp only [subtractState, MemoryState.eraseFrom_storeAt,
    MemoryState.storeAt_eraseFrom_of_le (hl _)]

theorem cleanupPhase_erase {E : Env program.Γ} {s : GlobalState}
    {scratch : Fin 33 → Pointer} {mark : Nat}
    (hl : ∀ i, mark ≤ (scratch i).id.id) :
    (cleanupPhaseResult E s scratch).2.mem.eraseFrom mark = s.mem.eraseFrom mark := by
  simp only [cleanupPhaseResult, cleanupChunks0Result, cleanupChunks1Result,
    cleanupChunks2Result, cleanupChunks3Result, cleanupChunks4Result, cleanupChunks5Result,
    MemoryState.eraseFrom_storeAt, MemoryState.storeAt_eraseFrom_of_le (hl _)]

theorem storeBytes_erase (m : MemoryState) (out : Pointer) (bytes : Bytes) (mark : Nat) :
    (storeBytes m out bytes).eraseFrom mark = storeBytes (m.eraseFrom mark) out bytes := by
  simp only [storeBytes, MemoryState.eraseFrom_storeAt]

/-- The explicit pipeline retains only the 32 caller-output stores after erasure. -/
theorem pipeline_memory (out input : Pointer) (s : GlobalState) (d : PipelineData)
    (hwf : s.WF) (hlocal : ∀ i, s.alloc.nextFreeBlock ≤ (d.scratch i).id.id) :
    (pipelineStages out input s d 9).2.mem.eraseFrom s.alloc.nextFreeBlock =
      storeBytes s.mem out d.bytes := by
  have hu : ∀ i, s.alloc.nextFreeBlock ≤ (d.unpackScratch i).id.id := fun i => hlocal _
  have hp : ∀ i, s.alloc.nextFreeBlock ≤ (d.productScratch i).id.id := fun i => hlocal _
  have hs : ∀ i, s.alloc.nextFreeBlock ≤ (d.subtractScratch i).id.id := fun i => hlocal _
  simp only [pipelineStages, pipelineVector_get9, cleanupPhase_erase hlocal, storeBytes_erase,
    subtractState_erase hs, productPhase_erase hp, unpackPhase_erase hu,
    allocationSchedule_erase _ s hwf]

/-- Thirty-three reducer allocas plus the one real black-box allocation. -/
theorem pipeline_allocation_count (out input : Pointer) (s : GlobalState) (d : PipelineData) :
    (pipelineStages out input s d 9).2.alloc.nextFreeBlock = s.alloc.nextFreeBlock + 34 := by
  change (allocationSchedule (constantsEnv
    (Env.init (program.args (.value out) (.value input)).get)) s).2.alloc.nextFreeBlock + 1 = _
  rw [allocationSchedule_count]

/-- Exact public post-state of the composed pipeline, before identifying its bytes. -/
theorem pipeline_post_state (out input : Pointer) (s : GlobalState) (d : PipelineData)
    (hwf : s.WF) (hlocal : ∀ i, s.alloc.nextFreeBlock ≤ (d.scratch i).id.id) :
    {(pipelineStages out input s d 9).2 with
      mem := (pipelineStages out input s d 9).2.mem.eraseFrom s.alloc.nextFreeBlock} =
      {s with alloc := ⟨s.alloc.nextFreeBlock + 34⟩, mem := storeBytes s.mem out d.bytes} := by
  apply GlobalState.ext
  · cases ha : (pipelineStages out input s d 9).2.alloc with
    | mk counter =>
      have hc := pipeline_allocation_count out input s d
      rw [ha] at hc
      change counter = s.alloc.nextFreeBlock + 34 at hc
      rw [hc]
  · exact pipeline_memory out input s d hwf hlocal

/-- A direct actual-call equation whose remaining obligations are invariant
construction and the mathematical identity of the 32 serialized bytes. -/
theorem pipeline_call_public (out input : Pointer) (s : GlobalState) (d : PipelineData)
    (hr : PipelineReady out input s d) (hwf : s.WF)
    (hlocal : ∀ i, s.alloc.nextFreeBlock ≤ (d.scratch i).id.id) :
    program.call (program.args (.value out) (.value input)) s =
      .value (.nil, {s with alloc := ⟨s.alloc.nextFreeBlock + 34⟩, mem := storeBytes s.mem out d.bytes}) := by
  rw [pipeline_call out input s d hr, pipeline_post_state out input s d hwf hlocal]

end Agave.Ed25519.ScalarReduce32.Execution
