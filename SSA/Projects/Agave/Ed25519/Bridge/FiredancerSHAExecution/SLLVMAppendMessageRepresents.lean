import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMAppendMessagePreservation
import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMAppendSemanticResult

namespace Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource
open LeanMLIR SLLVM Firedancer
namespace MessageExecution
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
attribute [local irreducible] append core

/-- The actual third append advances the reachable stream invariant. -/
theorem represents (s : GlobalState) (p data kp : Pointer) (n : BitVec 64)
    (completed pending : List (BitVec 8)) (h : Ready s p data kp n)
    (hp : ContextRepresents s.mem p completed pending) (hlen : pending.length = 64) :
    ∃ after : GlobalState,
      StateT.run (runFunction (append.denote
        (Ctxt.Valuation.ofHVector [.value n, .value data, .value p]ₕ))) s =
        .value ([.value p]ₕ, after) ∧
      Ready after p data kp n ∧ after.WF ∧ after.alloc = s.alloc ∧ after.globals = s.globals ∧
      (∀ q, q ≠ p.id → after.mem.live? q = s.mem.live? q) ∧
      ContextRepresents after.mem p
        (completed ++ StreamSpec.complete (pending ++ sourceReadBytes s.mem data n.toNat))
        (StreamSpec.pending (pending ++ sourceReadBytes s.mem data n.toNat)) := by
  have hcount : sourceRead s.mem (p.withOffset 200#64) 64 = 64#64 := by
    simpa only [hlen] using hp.pendingCount
  have hcsmall : ∀ b, s.mem.live? p.id = some b → b.length < 2^63 := by
    intro b hb
    obtain ⟨a, ha, hasmall, _⟩ := h.contextRange
    have he : a = b := Option.some.inj (ha.symm.trans hb)
    exact he ▸ hasmall
  have hdsmall : ∀ b, s.mem.live? data.id = some b → b.length < 2^63 := by
    intro b hb
    obtain ⟨a, ha, hasmall, _⟩ := h.messageRange
    have he : a = b := Option.some.inj (ha.symm.trans hb)
    exact he ▸ hasmall
  have hmodel := append_message_result_represents_source s p data n completed pending hp
    h.messageRange.fits h.inputSeparate hcsmall hdsmall hcount
  obtain ⟨after, hrun, hready, ha, hg, hm, hf⟩ := executes_ready s p data kp n h hcount
  exact ⟨after, hrun, hready, hready.wf, ha, hg, hf, hmodel.of_live_eq (hm p.id).symm⟩

/-- At the concrete after-R/after-A state, the imported third call represents
exactly the transcript R ++ A ++ M, for every addressable message length. -/
theorem after_R_A (s : GlobalState) (p data kp : Pointer) (n : BitVec 64)
    (R A M : List (BitVec 8)) (hR : R.length = 32) (hA : A.length = 32)
    (h : Ready s p data kp n) (hp : ContextRepresents s.mem p [] (R ++ A))
    (hmessage : sourceReadBytes s.mem data n.toNat = M) :
    ∃ after : GlobalState,
      StateT.run (runFunction (append.denote
        (Ctxt.Valuation.ofHVector [.value n, .value data, .value p]ₕ))) s =
        .value ([.value p]ₕ, after) ∧
      Ready after p data kp n ∧ after.WF ∧ after.alloc = s.alloc ∧ after.globals = s.globals ∧
      (∀ q, q ≠ p.id → after.mem.live? q = s.mem.live? q) ∧
      ContextRepresents after.mem p (StreamSpec.complete (R ++ A ++ M))
        (StreamSpec.pending (R ++ A ++ M)) := by
  have hlen : (R ++ A).length = 64 := by simp only [List.length_append, hR, hA]
  simpa only [hmessage, List.nil_append, List.append_assoc] using represents s p data kp n [] (R ++ A) h hp hlen

end MessageExecution
end Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource
