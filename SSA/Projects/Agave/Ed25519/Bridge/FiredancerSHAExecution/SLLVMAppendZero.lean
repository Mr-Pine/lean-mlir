import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSourceAppend
import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMAppendContext
import SSA.Projects.Firedancer.MLIR.DenoteStep
import SSA.Projects.Firedancer.Proof.Tactics
import SSA.Projects.Firedancer.Ref.Proof.MemoryOperations

namespace Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource
open LeanMLIR SLLVM Firedancer
open InstCombine (LLVM)
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
attribute [local irreducible] core

/-- A zero-byte append never dereferences either pointer. Even a poison message
operand is ignored by the actual imported source control flow. -/
theorem append_zero_body (p : Pointer) (data : PoisonOr Pointer) (s : GlobalState) :
    StateT.run (append.denote
      (Ctxt.Valuation.ofHVector [.value (0#64), data, .value p]ₕ)) s =
      .value ([.value p]ₕ, s) := by
  simp only [Cfg.denote]
  denote_expose
  denote_step_reduce v 11 [LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp']
  simp only [hv11, hv0, BlockCom.denote_term, Terminator.denote_condBr,
    simp_denote, simp_sllvm]
  denote_enter_block
  simp_return

/-- Function-frame cleanup is the only state effect of an empty append. -/
theorem append_zero_call (p : Pointer) (data : PoisonOr Pointer) (s : GlobalState) :
    StateT.run (runFunction (append.denote
      (Ctxt.Valuation.ofHVector [.value (0#64), data, .value p]ₕ))) s =
      .value ([.value p]ₕ, s.popFrame s.mem) :=
  @run_runFunction _ (append.denote
    (Ctxt.Valuation.ofHVector [.value (0#64), data, .value p]ₕ)) s s ([.value p]ₕ) (append_zero_body p data s)

/-- Empty append preserves every live allocation, including the complete
context, and hence preserves any reachable streaming invariant. -/
theorem append_zero_represents (p : Pointer) (data : PoisonOr Pointer) (s : GlobalState)
    (completed pending : List (BitVec 8)) (hwf : s.WF)
    (hp : ContextRepresents s.mem p completed pending) :
    ∃ after : GlobalState,
      StateT.run (runFunction (append.denote
        (Ctxt.Valuation.ofHVector [.value (0#64), data, .value p]ₕ))) s =
        .value ([.value p]ₕ, after) ∧
      after.WF ∧ after.alloc = s.alloc ∧ after.globals = s.globals ∧
      (∀ b, after.mem.live? b = s.mem.live? b) ∧
      ContextRepresents after.mem p completed pending := by
  have he := hwf.popFrame_equiv
  refine ⟨s.popFrame s.mem, append_zero_call p data s,
    hwf.of_equiv he, rfl, rfl, ?_, ?_⟩
  · intro b
    exact (he.live b).symm
  · exact hp.of_live_eq (he.live p.id)

end Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource
