import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMAppendMessageCorrect

namespace Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource
open LeanMLIR SLLVM Firedancer
namespace MessageExecution
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
attribute [local irreducible] append core Core.result sourceRead

private theorem Ready.store_base {s : GlobalState} {p data kp : Pointer} {n : BitVec 64}
    (h : Ready s p data kp n) (x : BitVec w) :
    Ready {s with mem := s.mem.splice p x} p data kp n := by
  simpa only [Pointer.withOffset, BitVec.add_zero] using h.store 0#64 x

private theorem Ready.short {s : GlobalState} {p data kp : Pointer} {n : BitVec 64}
    (h : Ready s p data kp n) :
    Ready {s with mem := appendMessageShortMemory s.mem p data n} p data kp n :=
  (((h.store _ _).store _ _).store _ _).store _ _

private theorem Ready.canonical_core {s : GlobalState} {p data kp src : Pointer} {n count : BitVec 64}
    (h : Ready s p data kp n) : Ready (coreState s p src count) p data kp n :=
  h.store _ _

private theorem Ready.tail {s : GlobalState} {p data kp rest : Pointer} {n tail : BitVec 64}
    (h : Ready s p data kp n) :
    Ready {s with mem := appendMessageTailMemory s.mem p rest tail} p data kp n :=
  ((h.store _ _).store_base _).store _ _

private theorem Ready.direct_tail {s : GlobalState} {p data kp rest : Pointer} {n size : BitVec 64}
    (h : Ready s p data kp n) :
    Ready {s with mem := appendMessageDirectTailMemory s.mem p rest size} p data kp n := by
  dsimp only [appendMessageDirectTailMemory]
  split
  · exact h
  · exact (h.store_base _).store _ _

/-- The source state model preserves the concrete allocation bounds and the
constants binding required by subsequent hashing calls. -/
theorem Ready.result {s : GlobalState} {p data kp : Pointer} {n : BitVec 64}
    (h : Ready s p data kp n) : Ready (resultState s p data n) p data kp n := by
  dsimp only [resultState]
  split_ifs
  · exact h
  · exact h.short
  · exact h.filled.canonical_core.store _ _
  · exact h.filled.canonical_core.tail
  · exact (h.filled.canonical_core.store _ _).canonical_core.direct_tail

theorem Ready.of_equiv {s t : GlobalState} {p data kp : Pointer} {n : BitVec 64}
    (h : Ready s p data kp n) (he : s ≈ t) : Ready t p data kp n := by
  refine ⟨h.wf.of_equiv he, h.contextRange.of_live_eq (he.live _).symm,
    h.messageRange.of_live_eq (he.live _).symm, h.constantsRange.of_live_eq (he.live _).symm,
    ?_, ?_, h.constantsSeparate, h.inputSeparate⟩
  · simpa only [GlobalPtr, ← he.globals] using h.constantsPtr
  · rw [Core.readBits_of_live_eq (he.live kp.id).symm]
    exact h.constantsValue

/-- Readiness is preserved by the actual third call, including the memory
conditions needed to instantiate the subsequent finish theorem. -/
theorem executes_ready (s : GlobalState) (p data kp : Pointer) (n : BitVec 64)
    (h : Ready s p data kp n)
    (hcount : sourceRead s.mem (p.withOffset 200#64) 64 = 64#64) :
    ∃ after : GlobalState,
      StateT.run (runFunction (append.denote
        (Ctxt.Valuation.ofHVector [.value n, .value data, .value p]ₕ))) s =
        .value ([.value p]ₕ, after) ∧
      Ready after p data kp n ∧ after.alloc = s.alloc ∧ after.globals = s.globals ∧
      (∀ q, after.mem.live? q = (resultState s p data n).mem.live? q) ∧
      (∀ q, q ≠ p.id → after.mem.live? q = s.mem.live? q) := by
  obtain ⟨after, he, _, ha, hg, hm, hf⟩ := executes s p data kp n h hcount
  have hEq : resultState s p data n ≈ after :=
    ⟨(resultState_alloc s p data n).trans ha.symm,
      (resultState_globals s p data n).trans hg.symm, fun q => (hm q).symm⟩
  exact ⟨after, he, h.result.of_equiv hEq, ha, hg, hm, hf⟩

end MessageExecution
end Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource
