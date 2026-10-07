import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.FinishCompositionRun

/-! The concrete linked C finalizer computes the shared SHA-512 digest. No
whole-hash equality or finalization-correctness premise occurs in the theorem. -/
namespace Agave.Ed25519.Bridge.FiredancerSHAExecution.Finish
open LeanMLIR.RIR Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.SHA512 Agave.Ed25519.SHA512.Spec
open Agave.Ed25519.Verifier.Execution.Challenge
open Agave.Ed25519.Bridge.Challenge
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- One actual core call induces the common compression transition. -/
theorem compressionState_pack (state : GlobalState) (context : Pointer)
    (hr : SmallRange state.mem context 224) :
    pack (readState (compressionState state context).mem context) =
      compressBlockBytes (pack (readState state.mem context)) (readBytes state.mem context 128) := by
  rw [compressionState, coreCallState_state state context _ hr]
  simp only [compressBlockBytes, unpack_pack]

/-- Both concrete branches have the exact final-block fold of the common spec. -/
theorem beforeOutput_fold (state : GlobalState) (context output kp : Pointer)
    (completed pending : Bytes) (lo hi : Word)
    (h : Ready state context output kp)
    (hp : ContextRepresents state.mem context completed pending)
    (hlo : state.mem.readAt (context.add 208#64) 64 = lo)
    (hhi : state.mem.readAt (context.add 216#64) 64 = hi) :
    pack (readState (beforeOutput state context pending.length lo hi).mem context) =
      (finalBlocks pending (completed.length + pending.length)).foldl
        Spec.compression.run (Spec.run initialWords completed) := by
  have hcount : hi ++ lo = BitVec.ofNat 128 (8 * (completed.length + pending.length)) := by
    simpa only [hlo, hhi] using hp.bitCount
  have h128 : SmallRange state.mem context 128 := smallRange_mono h.contextLive (by decide)
  have hmarked := h.marker pending.length
  by_cases hs : pending.length < 112
  · have hprepared := hmarked.last (pending.length + 1) lo hi
    rw [beforeOutput, ite_eq_left hs, compressionState_pack _ _ hprepared.contextLive]
    change compressBlockBytes (pack (readState
      (lastMemory (markerMemory state.mem context pending.length) context (pending.length + 1) lo hi)
      context))
      (readBytes (lastMemory (markerMemory state.mem context pending.length)
        context (pending.length + 1) lo hi) context 128) = _
    rw [lastMemory_state (markerMemory state.mem context pending.length) context
      (pending.length + 1) lo hi hmarked.contextLive (by omega),
      markerMemory_state _ _ _ h.contextLive hp.pendingBound, hp.chaining, pack_unpack,
      onlyPaddingBlock_bytes _ _ pending _ lo hi h128 hs hp.pendingBytes hcount]
    simp only [finalBlocks, ite_eq_left hs, List.foldl_cons, List.foldl_nil, Spec.compression]
    rw [Spec.run_one_block _ _ (onlyPaddingBlock_length pending hs)]
  · let first := longState (markerState state context pending.length) context pending.length
    let middle := compressionState first context
    have hfirst : Ready first context output kp := hmarked.long pending.length
    have hmiddle : Ready middle context output kp := hfirst.compression
    have hprepared := hmiddle.last 0 lo hi
    rw [beforeOutput, ite_eq_right hs, compressionState_pack _ _ hprepared.contextLive]
    change compressBlockBytes (pack (readState (lastMemory middle.mem context 0 lo hi) context))
      (readBytes (lastMemory middle.mem context 0 lo hi) context 128) = _
    rw [lastMemory_state middle.mem context 0 lo hi hmiddle.contextLive (by decide),
      lastPaddingBlock_bytes _ _ _ lo hi (smallRange_mono hmiddle.contextLive (by decide)) hcount]
    have hpack := compressionState_pack first context hfirst.contextLive
    change pack (readState middle.mem context) = _ at hpack
    rw [hpack]
    change compressBlockBytes (compressBlockBytes
      (pack (readState (longMemory (markerMemory state.mem context pending.length)
        context pending.length) context))
      (readBytes (longMemory (markerMemory state.mem context pending.length)
        context pending.length) context 128)) (lastPaddingBlock _) = _
    rw [longMemory_state (markerMemory state.mem context pending.length) context
      pending.length hmarked.contextLive hp.pendingBound,
      markerMemory_state _ _ _ h.contextLive hp.pendingBound, hp.chaining, pack_unpack,
      firstPaddingBlock_bytes _ _ pending h128 hp.pendingBound hp.pendingBytes]
    simp only [finalBlocks, ite_eq_right hs, List.foldl_cons, List.foldl_nil, Spec.compression]
    rw [Spec.run_one_block _ _ (firstPaddingBlock_length pending hp.pendingBound),
      Spec.run_one_block _ _ (lastPaddingBlock_length _)]

/-- The context retains the final native chaining words after output stores. -/
theorem finishState_chaining (state : GlobalState) (context output kp : Pointer)
    (completed pending : Bytes) (lo hi : Word)
    (h : Ready state context output kp)
    (hp : ContextRepresents state.mem context completed pending)
    (hlo : state.mem.readAt (context.add 208#64) 64 = lo)
    (hhi : state.mem.readAt (context.add 216#64) 64 = hi) :
    pack (readState (finishState state context output pending.length lo hi).mem context) =
      (finalBlocks pending (completed.length + pending.length)).foldl
        Spec.compression.run (Spec.run initialWords completed) := by
  unfold finishState finalOutputState
  rw [outputMemory_state _ _ _ _ (h.preOutput pending.length lo hi).outputLive h.output_ne_context]
  exact beforeOutput_fold state context output kp completed pending lo hi h hp hlo hhi

/-- Observed digest bytes are the common SHA-512 digest of exactly the completed
prefix followed by the pending suffix. -/
theorem finishState_digest (state : GlobalState) (context output kp : Pointer)
    (completed pending : Bytes) (lo hi : Word)
    (h : Ready state context output kp)
    (hp : ContextRepresents state.mem context completed pending)
    (hlo : state.mem.readAt (context.add 208#64) 64 = lo)
    (hhi : state.mem.readAt (context.add 216#64) 64 = hi) :
    readBytes (finishState state context output pending.length lo hi).mem output 64 =
      bytesOf (n := 64) (digest Spec.compression (completed ++ pending)) := by
  rw [finishState_output state context output kp _ lo hi h,
    beforeOutput_fold state context output kp completed pending lo hi h hp hlo hhi]
  change bytesOf (n := 64) (finalize Spec.compression
    (Spec.compression.run initialWords completed) pending (completed.length + pending.length)) = _
  rw [finalize_eq_digest Spec.compression completed pending hp.completedWhole hp.pendingBound]

/-- Main concrete finalization contract. Its premises describe incoming memory
and the installed constant table; compression and both CFG branches are proved. -/
theorem call_digest (kp context output : Pointer) (state : GlobalState)
    (completed pending : Bytes) (hwf : state.WF)
    (hp : ContextRepresents state.mem context completed pending)
    (ho : SmallRange state.mem output 64) (hk : ConstantsReady state.mem kp)
    (hck : context.id ≠ kp.id) (hoc : output.id ≠ context.id) :
    ∃ after,
      (program (Core.program kp).call).call (program.args (.value context) (.value output)) state =
        .value (.cons (.value output) .nil, after) ∧
      readBytes after.mem output 64 =
        bytesOf (n := 64) (digest Spec.compression (completed ++ pending)) ∧
      after.alloc.nextFreeBlock = state.alloc.nextFreeBlock +
        (if pending.length < 112 then 1 else 2) ∧
      (∀ id, id ≠ context.id → id ≠ output.id → after.mem[id]? = state.mem[id]?) := by
  let lo := state.mem.readAt (context.add 208#64) 64
  let hi := state.mem.readAt (context.add 216#64) 64
  have h : Ready state context output kp := ⟨hwf, hp.live, ho, hk, hck, hoc⟩
  exact ⟨finishState state context output pending.length lo hi,
    call kp context output state _ lo hi h hp.pendingBound hp.pendingCount rfl rfl,
    finishState_digest state context output kp completed pending lo hi h hp rfl rfl,
    finishState_alloc state context output _ lo hi,
    finishState_other_block state context output _ lo hi⟩

end Agave.Ed25519.Bridge.FiredancerSHAExecution.Finish
