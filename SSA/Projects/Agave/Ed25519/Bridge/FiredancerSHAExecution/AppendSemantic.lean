import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.AppendSemanticCombine

/-! End-to-end streaming observation refinement of the concrete imported C
append. The completed-byte prefix is ghost state; the input bytes are copied
and hashed in address order without any reinterpretation. -/
namespace Agave.Ed25519.Bridge.FiredancerSHAExecution.Append.Semantic
open LeanMLIR.RIR Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.SHA512 Agave.Ed25519.SHA512.Spec
open Agave.Ed25519.Bridge.Challenge
open Agave.Ed25519.Verifier.Execution.Challenge
set_option maxRecDepth 100000
set_option maxHeartbeats 700000

/-- Exact completed-prefix/pending-suffix witnesses after arbitrary append.
This theorem needs no execution, SHA result, or total-transcript size premise. -/
theorem result_represents (s : GlobalState) (context data : Pointer) (size : Word)
    (completed pending : Bytes)
    (hctx : ContextRepresents s.mem context completed pending)
    (hi : SmallRange s.mem data size.toNat) (hne : context.id ≠ data.id) :
    ContextRepresents (resultState s context data size).mem context
      (completed ++ StreamSpec.complete (pending ++ readBytes s.mem data size.toNat))
      (StreamSpec.pending (pending ++ readBytes s.mem data size.toNat)) := by
  let chunk := readBytes s.mem data size.toNat
  let q : StreamSpec.Context := ⟨Spec.run initialWords completed, pending,
    BitVec.ofNat 128 (8 * (completed.length + pending.length))⟩
  have h := result_rep s context data size q (of_context s.mem context completed pending hctx) hi hne
  refine ⟨h.live, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [List.length_append, Nat.add_mod, hctx.completedWhole, StreamSpec.complete_whole]
  · exact StreamSpec.pending_bound _
  · exact h.buffer
  · exact h.count
  · rw [readState_unpack _ context h.live, h.chain]
    change unpack (Spec.run (Spec.run initialWords completed)
      (StreamSpec.complete (pending ++ chunk))) = _
    rw [← Spec.run_append initialWords completed _ hctx.completedWhole]
  · rw [h.bits]
    change BitVec.ofNat 128 (8 * (completed.length + pending.length)) +
        BitVec.ofNat 128 (8 * chunk.length) = _
    rw [← BitVec.ofNat_add]
    congr 1
    have hp := congrArg List.length (StreamSpec.partition (pending ++ chunk))
    dsimp only [chunk] at hp ⊢
    simp only [List.length_append] at hp ⊢
    omega

/-- Convenient ghost-witness form for callers that append multiple chunks. -/
theorem result_represents_exists (s : GlobalState) (context data : Pointer) (size : Word)
    (completed pending : Bytes) (hctx : ContextRepresents s.mem context completed pending)
    (hi : SmallRange s.mem data size.toNat) (hne : context.id ≠ data.id) :
    ∃ completed' pending',
      ContextRepresents (resultState s context data size).mem context completed' pending' ∧
      completed' ++ pending' = (completed ++ pending) ++ readBytes s.mem data size.toNat := by
  refine ⟨_, _, result_represents s context data size completed pending hctx hi hne, ?_⟩
  rw [List.append_assoc, StreamSpec.partition, List.append_assoc]

/-- The actual returned memory advances the independent pure-stream invariant. -/
theorem result_stream_represents (s : GlobalState) (context data : Pointer) (size : Word)
    (completed pending : Bytes) (hctx : ContextRepresents s.mem context completed pending)
    (hi : SmallRange s.mem data size.toNat) (hne : context.id ≠ data.id) :
    StreamSpec.Represents (StreamSpec.observe (resultState s context data size).mem context)
      ((completed ++ pending) ++ readBytes s.mem data size.toNat) := by
  obtain ⟨done, buffer, hr, hm⟩ := result_represents_exists s context data size completed pending hctx hi hne
  rw [← hm]
  exact StreamSpec.observe_represents _ _ _ _ hr

/-- Concrete imported append plus concrete imported core, with the same
memory contract used by the complete verifier transcript composition. -/
theorem linked_call_represents (id : BlockId) (s : GlobalState) (context data : Pointer)
    (size : Word) (completed pending : Bytes) (hr : Resources id s context data size)
    (hctx : ContextRepresents s.mem context completed pending) :
    ∃ after,
      (program (linkedCore id)).call (program.args (.value context) (.value data) (.value size)) s =
        .value (.cons (.value context) .nil, after) ∧
      ContextRepresents after.mem context
        (completed ++ StreamSpec.complete (pending ++ readBytes s.mem data size.toNat))
        (StreamSpec.pending (pending ++ readBytes s.mem data size.toNat)) ∧
      StreamSpec.Represents (StreamSpec.observe after.mem context)
        ((completed ++ pending) ++ readBytes s.mem data size.toNat) ∧ after.WF := by
  have hm := of_context s.mem context completed pending hctx
  have hused : (s.mem.readAt (context.add 200#64) 64).toNat < 128 := by
    rw [hm.used]
    exact hctx.pendingBound
  exact ⟨_, linked_call id s context data size hr hused,
    result_represents s context data size completed pending hctx hr.inputLive hr.distinct,
    result_stream_represents s context data size completed pending hctx hr.inputLive hr.distinct,
    result_wf s context data size hr.wf⟩

end Agave.Ed25519.Bridge.FiredancerSHAExecution.Append.Semantic
