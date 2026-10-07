import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionAvx2LiveDefs
import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionAvx2DalekAdapterPrivateFrame
import SSA.Projects.Agave.Ed25519.Proof.Avx2PointAdd.AdditionBaseCache

/-! A concrete loop invariant inhabited by the actual entry and constructor.
Private arithmetic stores preserve its caller and cache observations. -/
namespace Agave.Ed25519.DoubleBase.ExecutionAvx2
open LeanMLIR.RIR RIR PointArithmetic
open Reduce64.Execution (SmallRange)
open Conformance.BackendExecution (Invocation)
open Avx2PointAdd.Phases
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

structure LiveContext (g : Avx2CFG.Globals) (i : Invocation) (initial : GlobalState)
    (E : ⟪avx2Kernel.Γ⟫) (s : GlobalState) : Prop where
  registers : LoopRegisters g i initial E
  framed : DalekContext i initial E s
  scratch : ∀ k : Fin 27, avx2StackSize k.val = 160 →
    SmallRange s.mem (avx2StackPtr initial k.val) 160
  base : BaseCache g.address2 s
  baseOld : g.address2.id.id < initial.alloc.nextFreeBlock

theorem liveContext_stable (g : Avx2CFG.Globals) (i : Invocation) (initial : GlobalState) :
    ContextStable (LiveContext g i initial) := by
  intro E E' s hf h
  exact ⟨h.registers.frame hf, dalekContext_stable i initial E E' s hf h.framed,
    h.scratch, h.base, h.baseOld⟩

theorem stack27_protected (initial : GlobalState) :
    initial.alloc.nextFreeBlock + 27 ≤ (avx2StackPtr initial 27).id.id := by
  simp [avx2StackPtr, GlobalState.allocaPtr_id_id, avx2Stack_nextFreeBlock]

theorem LiveContext.of_privateFrame (h : LiveContext g i initial E s)
    (hf : LoopPrivateFrame initial s s') : LiveContext g i initial E s' := by
  refine ⟨h.registers, ⟨?_, h.framed.2.of_loopPrivateFrame hf⟩,
    fun k hk => hf.live _ _ (h.scratch k hk), ?_, h.baseOld⟩
  · refine ⟨h.framed.1.outputRegisters, hf.wellFormed,
      hf.live _ _ h.framed.1.output, fun k => hf.live _ _ (h.framed.1.scratch k),
      hf.live _ _ h.framed.1.tableRange, ?_⟩
    intro k
    rw [hf.packedPoint (Or.inr (by simpa using stack27_protected initial))]
    exact h.framed.1.tableValues k
  · apply h.base.of_reads hf.live
    intro q width hq
    exact hf.read q width (Or.inl (by simpa only [hq] using h.baseOld))

/-- The extra register, private-range and static-table invariants come from
entry allocation, the retained prefix frame and the actual constructor frame. -/
theorem prefix_liveContext (g : Avx2CFG.Globals) (i : Invocation) (initial : GlobalState)
    (hinput : Input i initial) (hglobal : GlobalsReady g initial) :
    PrefixContext g i initial (LiveContext g i initial) := by
  intro ES s' hframe htable hvalues
  have hb := baseCache_of_globalsReady hglobal
  have hold : g.address2.id.id < initial.alloc.nextFreeBlock :=
    hinput.wellFormed.lt hb.1.fits.mem
  refine ⟨LoopRegisters.prefix hframe _,
    prefix_dalekContext g i initial hinput ES s' hframe htable hvalues, ?_, ?_, hold⟩
  · intro k hk
    apply htable.live
    have hs : avx2StackSize k.val < 2 ^ 63 := by rw [hk]; decide
    simpa only [NAF.Memory.Buffer, SmallRange, hk] using prefixState_stack_buffer initial
      (initial.mem.readAt i.scalarA 256) (initial.mem.readAt i.scalarB 256)
      hinput.wellFormed ⟨k.val, by omega⟩ hs
  · apply hb.of_reads
    · intro q bytes hq
      exact htable.live q bytes (prefixState_buffer _ _ _ hinput.wellFormed hq)
    · intro q width hq
      have hqold : q.id.id < initial.alloc.nextFreeBlock := by simpa only [hq] using hold
      rw [htable.read q width (Range.disjoint_of_id_ne (stack_separate_old hqold 27).symm)]
      exact prefix_read_old initial _ _ hqold width

theorem loopScratch_private (initial : GlobalState) (site : Fin 4) (k : Fin 6) :
    initial.alloc.nextFreeBlock ≤ ((loopScratch initial site).written k).id.id ∧
    ((loopScratch initial site).written k).id.id < initial.alloc.nextFreeBlock + 27 := by
  fin_cases site <;> fin_cases k <;>
    simp [loopScratch, Scratch.written, avx2StackPtr,
      GlobalState.allocaPtr_id_id, avx2Stack_nextFreeBlock] <;> omega

theorem loopScratch_digits (initial : GlobalState) (site : Fin 4) (k : Fin 6)
    (n : Nat) (hn : 27 ≤ n) :
    ((loopScratch initial site).written k).id ≠ (avx2StackPtr initial n).id := by
  intro he
  have he' := congrArg (fun id => id.id) he
  have h := (loopScratch_private initial site k).2
  simp only [avx2StackPtr, GlobalState.allocaPtr_id_id, avx2Stack_nextFreeBlock] at he'
  omega

theorem loopScratch_live (h : LiveContext g i initial E s)
    (site : Fin 4) (k : Fin 6) :
    SmallRange s.mem ((loopScratch initial site).written k) 160 := by
  fin_cases site <;> fin_cases k
  · simpa [loopScratch, Scratch.written] using h.scratch 24 (by decide)
  · simpa [loopScratch, Scratch.written] using h.scratch 16 (by decide)
  · simpa [loopScratch, Scratch.written] using h.scratch 15 (by decide)
  · simpa [loopScratch, Scratch.written] using h.scratch 14 (by decide)
  · simpa [loopScratch, Scratch.written] using h.scratch 13 (by decide)
  · simpa [loopScratch, Scratch.written] using h.scratch 17 (by decide)
  · simpa [loopScratch, Scratch.written] using h.scratch 25 (by decide)
  · simpa [loopScratch, Scratch.written] using h.scratch 12 (by decide)
  · simpa [loopScratch, Scratch.written] using h.scratch 11 (by decide)
  · simpa [loopScratch, Scratch.written] using h.scratch 10 (by decide)
  · simpa [loopScratch, Scratch.written] using h.scratch 9 (by decide)
  · simpa [loopScratch, Scratch.written] using h.scratch 17 (by decide)
  · simpa [loopScratch, Scratch.written] using h.scratch 22 (by decide)
  · simpa [loopScratch, Scratch.written] using h.scratch 7 (by decide)
  · simpa [loopScratch, Scratch.written] using h.scratch 6 (by decide)
  · simpa [loopScratch, Scratch.written] using h.scratch 5 (by decide)
  · simpa [loopScratch, Scratch.written] using h.scratch 4 (by decide)
  · simpa [loopScratch, Scratch.written] using h.scratch 8 (by decide)
  · simpa [loopScratch, Scratch.written] using h.scratch 23 (by decide)
  · simpa [loopScratch, Scratch.written] using h.scratch 3 (by decide)
  · simpa [loopScratch, Scratch.written] using h.scratch 2 (by decide)
  · simpa [loopScratch, Scratch.written] using h.scratch 1 (by decide)
  · simpa [loopScratch, Scratch.written] using h.scratch 0 (by decide)
  · simpa [loopScratch, Scratch.written] using h.scratch 8 (by decide)

theorem loopScratch_memory (h : LiveContext g i initial E s)
    (site : Fin 4) (cached : Pointer) (hc : SmallRange s.mem cached 160)
    (hid : cached.id.id < initial.alloc.nextFreeBlock ∨
      initial.alloc.nextFreeBlock + 27 ≤ cached.id.id) :
    MemoryReady s (loopScratch initial site) cached := by
  refine ⟨h.framed.1.wellFormed, ?_, ?_⟩
  · intro k
    fin_cases k
    · exact loopScratch_live h site 0
    · exact loopScratch_live h site 1
    · exact loopScratch_live h site 2
    · exact loopScratch_live h site 3
    · exact loopScratch_live h site 4
    · exact loopScratch_live h site 5
    · exact hc
  · intro x y he
    have hv := congrArg (fun id => id.id) he
    fin_cases site <;> fin_cases x <;> fin_cases y <;>
      simp [loopScratch, Scratch.address, avx2StackPtr, GlobalState.allocaPtr_id_id,
        avx2Stack_nextFreeBlock] at hv ⊢ <;> omega

end Agave.Ed25519.DoubleBase.ExecutionAvx2
