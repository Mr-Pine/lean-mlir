import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMAppendSemanticResult
import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMAppendFirstSemantic

namespace Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource
open LeanMLIR SLLVM Firedancer
open Agave.Ed25519.Reduce64.Execution
open FinishObservation
set_option maxRecDepth 100000
set_option maxHeartbeats 200000
attribute [local irreducible] init append core initMemory Init.memory

theorem observed_init {m : MemoryState} {p : Pointer} {r : RIR.MemoryState} {q : RIR.Pointer}
    (h : Observed m p r q) : Observed (initMemory m p) p (Init.memory r q) q := by
  refine ⟨?_, h.offset⟩
  rw [initMemory_block, rir_initMemory_block, h.block, h.offset]

theorem init_memory_represents_source (m : MemoryState) (p : Pointer)
    (h : Fits m p (224*8))
    (hsmall : ∀ b, m.live? p.id = some b → b.length < 2^63) :
    ContextRepresents (initMemory m p) p [] [] := by
  obtain ⟨b, hb, hlen⟩ := h
  have hlive : m.live? p.id = some b := by simp only [MemoryState.live?, hb]
  have h : Fits m p (224*8) := ⟨b, hb, hlen⟩
  have ho := snapshot_observed hlive
  have hr := snapshot_small (n := 224) h hlive (hsmall b hlive)
  have hi := observed_init ho
  have hp := Init.memory_represents (snapshot b) (snapshotPtr p) hr
  apply hi.context_back (observed_source_fits hi (Init.memory_live _ _ hr)) _ hp
  have hs := hsmall b hlive
  simp only [Pointer.offsetInBits, LiveBlock.lengthInBits] at hlen
  omega

end Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource
