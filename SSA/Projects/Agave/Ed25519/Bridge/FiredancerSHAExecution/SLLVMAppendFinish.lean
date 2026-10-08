import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMAppendMessageRepresents
import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMFinishClosed

/-! Composition of the actual third append and finalizer. The intermediate
context is obtained from execution, and its stream representation supplies the
finalizer's semantic premise. No compression or hash-call contract is assumed.
-/
namespace Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource
open LeanMLIR SLLVM Firedancer
namespace MessageExecution
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
attribute [local irreducible] append core finish

/-- Complete the concrete SHA transcript after the two fixed verifier appends.
The output may share an allocation with the message or constants; it must be
separate from the context. Both actual call outcomes and the final digest are
conclusions. -/
theorem append_finish_after_R_A
    (s : GlobalState) (p data o kp : Pointer) (n : BitVec 64)
    (R A M : List (BitVec 8)) (hR : R.length = 32) (hA : A.length = 32)
    (h : Ready s p data kp n) (hp : ContextRepresents s.mem p [] (R ++ A))
    (hmessage : sourceReadBytes s.mem data n.toNat = M)
    (ho : Core.SmallRange s.mem o 64) (hne : o.id ≠ p.id) :
    ∃ middle after : GlobalState,
      StateT.run (runFunction (append.denote
        (Ctxt.Valuation.ofHVector [.value n, .value data, .value p]ₕ))) s =
        .value ([.value p]ₕ, middle) ∧
      StateT.run (runFunction (finish.denote
        (.cons (.value o) (Ctxt.Valuation.singleton (.value p))))) middle =
        .value ([.value o]ₕ, after) ∧
      FinishCorrect.Post s after p o (R ++ A ++ M) := by
  obtain ⟨middle, happend, hready, _, halloc, hglobals, hframe, hrep⟩ :=
    after_R_A s p data kp n R A M hR hA h hp hmessage
  have hfinish : FinishCorrect.Ready middle p o kp :=
    ⟨hready.wf, hready.contextRange, ho.of_live_eq (hframe o.id hne),
      hready.constantsRange, hready.constantsPtr, hready.constantsValue,
      hready.constantsSeparate, hne⟩
  obtain ⟨after, hrun, hpost⟩ := FinishCorrect.call_digest_source middle p o kp
    (StreamSpec.complete (R ++ A ++ M)) (StreamSpec.pending (R ++ A ++ M))
    hfinish hrep
  have hpost' : FinishCorrect.Post middle after p o (R ++ A ++ M) := by
    simpa only [StreamSpec.partition] using hpost
  refine ⟨middle, after, happend, hrun, ?_⟩
  exact ⟨hpost'.wf, hpost'.alloc.trans halloc, hpost'.globalsEq.trans hglobals,
    hpost'.outputFits, hpost'.output,
    fun b hbp hbo => (hpost'.frame b hbp hbo).trans (hframe b hbp)⟩

end MessageExecution
end Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource
