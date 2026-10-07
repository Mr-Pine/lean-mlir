import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.FinishCompositionDigest
import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.FinishCompositionFrame
import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.CoreConstants

/-! Source-bound finalizer endpoint using the exact imported constants global. -/
namespace Agave.Ed25519.Bridge.FiredancerSHAExecution.Finish
open LeanMLIR.RIR Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.SHA512 Agave.Ed25519.SHA512.Spec
open Agave.Ed25519.Verifier.Execution.Challenge
open Agave.Ed25519.Bridge.Challenge
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem constantsReady_source (state : GlobalState) (id : BlockId)
    (h : constantsGlobal.Present id state.mem) :
    ConstantsReady state.mem (constantsGlobal.address id) :=
  ⟨Core.constants_present_range state id h, Core.constants_present_word state id h⟩

theorem finishState_wf (state : GlobalState) (context output kp : Pointer)
    (used : Nat) (lo hi : Word) (h : Ready state context output kp) :
    (finishState state context output used lo hi).WF := by
  have hw := (h.preOutput used lo hi).wf
  simpa only [finishState, finalOutputState, outputMemory, GlobalState.WF_storeAt] using hw

/-- All observable guarantees of finalization, including the exact fine frame. -/
structure Result (before after : GlobalState) (context output : Pointer)
    (completed pending : Bytes) : Prop where
  digest : readBytes after.mem output 64 =
    bytesOf (n := 64) (SHA512.digest Spec.compression (completed ++ pending))
  alloc : after.alloc.nextFreeBlock = before.alloc.nextFreeBlock +
    (if pending.length < 112 then 1 else 2)
  wf : after.WF
  chaining : pack (readState after.mem context) =
    (finalBlocks pending (completed.length + pending.length)).foldl
      Spec.compression.run (Spec.run initialWords completed)
  frame : ∀ q bits,
    (Range.of context 1536).Disjoint (Range.of q bits) →
    (Range.of output 512).Disjoint (Range.of q bits) →
    after.mem.readAt q bits = before.mem.readAt q bits
  otherBlocks : ∀ id, id ≠ context.id → id ≠ output.id → after.mem[id]? = before.mem[id]?
  metadata : ∀ offset count, 192 ≤ offset → offset + count ≤ 224 →
    after.mem.readAt (context.add (BitVec.ofNat 64 offset)) (8 * count) =
      before.mem.readAt (context.add (BitVec.ofNat 64 offset)) (8 * count)

/-- The actual imported RIR C finalizer with the actual imported RIR C core.
The incoming context observation is established by init/append; all arithmetic,
padding, compression, output stores, return, and cleanup execute concretely. -/
theorem call_digest_source (id : BlockId) (context output : Pointer) (state : GlobalState)
    (completed pending : Bytes) (hwf : state.WF)
    (hp : ContextRepresents state.mem context completed pending)
    (ho : SmallRange state.mem output 64) (hk : constantsGlobal.Present id state.mem)
    (hck : context.id ≠ id) (hoc : output.id ≠ context.id) :
    ∃ after,
      (program (Core.program (constantsGlobal.address id)).call).call
        (program.args (.value context) (.value output)) state =
        .value (.cons (.value output) .nil, after) ∧
      Result state after context output completed pending := by
  let kp := constantsGlobal.address id
  let lo := state.mem.readAt (context.add 208#64) 64
  let hi := state.mem.readAt (context.add 216#64) 64
  have h : Ready state context output kp :=
    ⟨hwf, hp.live, ho, constantsReady_source state id hk, hck, hoc⟩
  refine ⟨finishState state context output pending.length lo hi,
    call kp context output state _ lo hi h hp.pendingBound hp.pendingCount rfl rfl, ?_⟩
  refine ⟨finishState_digest state context output kp completed pending lo hi h hp rfl rfl,
    finishState_alloc state context output _ lo hi,
    finishState_wf state context output kp _ lo hi h,
    finishState_chaining state context output kp completed pending lo hi h hp rfl rfl, ?_,
    finishState_other_block state context output _ lo hi, ?_⟩
  · intro q bits hdc hdo
    exact finishState_readAt_frame state context output q _ lo hi bits hp.live ho hp.pendingBound hdc hdo
  · intro offset count hloff hhi
    exact finishState_metadata state context output _ lo hi offset count hp.live ho hp.pendingBound hoc hloff hhi

end Agave.Ed25519.Bridge.FiredancerSHAExecution.Finish
