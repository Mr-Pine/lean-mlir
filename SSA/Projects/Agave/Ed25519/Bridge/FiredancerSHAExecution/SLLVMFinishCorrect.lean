import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMFinishReady

namespace Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource
open LeanMLIR SLLVM Firedancer
open Agave.Ed25519.SHA512 Agave.Ed25519.SHA512.Spec
open Agave.Ed25519.Bridge.Challenge
open FinishExecution FinishDigest FinishObservation
namespace FinishCorrect
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
attribute [local irreducible] core finish markerMemory longMemory lastMemory outputMemory word

/-- The caller-visible result of the actual source finalizer. -/
structure Post (before after : GlobalState) (p o : Pointer) (message : Bytes) : Prop where
  wf : after.WF
  alloc : after.alloc = before.alloc
  globalsEq : after.globals = before.globals
  outputFits : Fits after.mem o 512
  output : sourceRead after.mem o 512 = digest Spec.compression message
  frame : ∀ b, b ≠ p.id → b ≠ o.id → after.mem.live? b = before.mem.live? b

private theorem output_post (s after : GlobalState) (p o : Pointer) (message : Bytes)
    (hwf : s.WF) (ho : Fits s.mem o 512) (ha : Core.SmallRange after.mem o 64)
    (hne : o.id ≠ p.id)
    (hd : serialize (pack (sourceReadState after.mem p)) = digest Spec.compression message)
    (hf : ∀ b, b ≠ p.id → after.mem.live? b = s.mem.live? b) :
    Post s (s.popFrame (outputMemory after.mem p o)) p o message := by
  have hold := lt_nextFreeBlock_of_fits hwf ho
  have hread : (s.popFrame (outputMemory after.mem p o)).mem.live? o.id =
      (outputMemory after.mem p o).live? o.id := live?_killFrom_of_lt hold
  refine ⟨?_, rfl, rfl, ?_, ?_, ?_⟩
  · intro q hq
    exact live?_killFrom_of_le hq
  · exact fits_of_live?_eq hread (outputMemory_fits ha.fits)
  · rw [sourceRead_of_live_eq hread, output_serialized after.mem p o ha hne, hd]
  · intro b hp ho
    change ((outputMemory after.mem p o).killFrom s.alloc.nextFreeBlock).live? b = s.mem.live? b
    by_cases hb : b.id < s.alloc.nextFreeBlock
    · rw [live?_killFrom_of_lt hb, outputMemory_frame _ _ _ _ ho, hf b hp]
    · rw [live?_killFrom_of_le (by omega), hwf b (by omega)]

/-- Only the local compression execution theorem is parameterized here. Every
finalizer instruction, branch, padding byte, output store, and return is proved. -/
theorem short_correct
    (hcore : ∀ (s : GlobalState) (kp chain data : Pointer) (count : BitVec 64),
      Core.Ready s kp chain data count → Core.Executes s chain data count)
    (s : GlobalState) (p o kp : Pointer) (completed pending : Bytes)
    (h : Ready s p o kp) (hp : ContextRepresents s.mem p completed pending)
    (hn : pending.length < 112) :
    ∃ after, StateT.run (runFunction (finish.denote
        (.cons (.value o) (Ctxt.Valuation.singleton (.value p))))) s =
      .value ([.value o]ₕ, after) ∧ Post s after p o (completed ++ pending) := by
  let lo := sourceRead s.mem (p.withOffset 208#64) 64
  let hi := sourceRead s.mem (p.withOffset 216#64) 64
  let m1 : GlobalState := {s with mem := markerMemory s.mem p pending.length}
  let m2 : GlobalState := {m1 with mem := lastMemory m1.mem p (pending.length+1) lo hi}
  have h1 : Ready m1 p o kp := h.marker pending.length
  have h2 : Ready m2 p o kp := h1.last _ lo hi
  obtain ⟨a, hrun, hawf, haalloc, haglobals, haframe⟩ := hcore m2 kp _ p 1#64 h2.core
  have ha : Ready a p o kp := h2.after_core hawf haglobals haframe
  have hstate : sourceReadState m2.mem p = sourceReadState s.mem p := by
    rw [FinishDigest.last_state _ _ h1.contextRange _ lo hi (by omega),
      FinishDigest.marker_state _ _ h.contextRange _ hp.pendingBound]
  have hbytes : Core.readBytes m2.mem p 128 =
      onlyPaddingBlock pending (completed.length+pending.length) :=
    short_bytes s.mem p h.contextRange pending _ lo hi hn hp.pendingBytes hp.bitCount
  have hpacked := core_result_state m2 a p h2.contextRange haframe
  rw [hstate, hp.chaining, pack_unpack, hbytes] at hpacked
  have hd : serialize (pack (sourceReadState a.mem p)) =
      digest Spec.compression (completed ++ pending) := by
    rw [hpacked]
    simpa only [finalize, finalBlocks, hn, ite_eq_left, List.foldl_cons, List.foldl_nil,
      Spec.compression] using
      (finalize_eq_digest Spec.compression completed pending hp.completedWhole hp.pendingBound)
  have hf : ∀ b, b ≠ p.id → a.mem.live? b = s.mem.live? b := by
    intro b hb
    rw [haframe b, live?_splice_ne (show (p.withOffset 128#64).id ≠ b from Ne.symm hb)]
    change (lastMemory (markerMemory s.mem p pending.length) p (pending.length+1) lo hi).live? b = _
    rw [lastMemory_frame _ _ _ _ _ _ hb, markerMemory_frame _ _ _ _ hb]
  refine ⟨s.popFrame (outputMemory a.mem p o), ?_,
    output_post s a p o _ h.wf h.outputRange.fits ha.outputRange h.outputSeparate hd hf⟩
  exact short_call p o s a pending.length lo hi hn h.contextRange.fits
    ((word_sourceRead _ _).trans hp.pendingCount)
    (word_sourceRead _ _) (word_sourceRead _ _) ha.contextRange.fits ha.outputRange.fits hrun

theorem long_correct
    (hcore : ∀ (s : GlobalState) (kp chain data : Pointer) (count : BitVec 64),
      Core.Ready s kp chain data count → Core.Executes s chain data count)
    (s : GlobalState) (p o kp : Pointer) (completed pending : Bytes)
    (h : Ready s p o kp) (hp : ContextRepresents s.mem p completed pending)
    (hn : ¬pending.length < 112) :
    ∃ after, StateT.run (runFunction (finish.denote
        (.cons (.value o) (Ctxt.Valuation.singleton (.value p))))) s =
      .value ([.value o]ₕ, after) ∧ Post s after p o (completed ++ pending) := by
  let lo := sourceRead s.mem (p.withOffset 208#64) 64
  let hi := sourceRead s.mem (p.withOffset 216#64) 64
  let m1 : GlobalState := {s with mem := markerMemory s.mem p pending.length}
  let m2 : GlobalState := {m1 with mem := longMemory m1.mem p pending.length}
  have h1 : Ready m1 p o kp := h.marker pending.length
  have h2 : Ready m2 p o kp := h1.long _
  obtain ⟨mid, hrunFirst, hmidwf, hmidalloc, hmidglobals, hmidframe⟩ := hcore m2 kp _ p 1#64 h2.core
  have hmid : Ready mid p o kp := h2.after_core hmidwf hmidglobals hmidframe
  let m3 : GlobalState := {mid with mem := lastMemory mid.mem p 0 lo hi}
  have h3 : Ready m3 p o kp := hmid.last 0 lo hi
  obtain ⟨a, hrun, hawf, haalloc, haglobals, haframe⟩ := hcore m3 kp _ p 1#64 h3.core
  have ha : Ready a p o kp := h3.after_core hawf haglobals haframe
  have hstateFirst : sourceReadState m2.mem p = sourceReadState s.mem p := by
    rw [FinishDigest.long_state _ _ h1.contextRange _ hp.pendingBound,
      FinishDigest.marker_state _ _ h.contextRange _ hp.pendingBound]
  have hbytesFirst : Core.readBytes m2.mem p 128 = firstPaddingBlock pending :=
    first_bytes s.mem p h.contextRange pending hp.pendingBound hp.pendingBytes
  have hpackedFirst := core_result_state m2 mid p h2.contextRange hmidframe
  rw [hstateFirst, hp.chaining, pack_unpack, hbytesFirst] at hpackedFirst
  have hstateLast : sourceReadState m3.mem p = sourceReadState mid.mem p :=
    FinishDigest.last_state mid.mem p hmid.contextRange 0 lo hi (by decide)
  have hbytesLast : Core.readBytes m3.mem p 128 =
      lastPaddingBlock (completed.length+pending.length) :=
    last_bytes mid.mem p hmid.contextRange _ lo hi hp.bitCount
  have hpacked := core_result_state m3 a p h3.contextRange haframe
  rw [hstateLast, hpackedFirst, hbytesLast] at hpacked
  have hd : serialize (pack (sourceReadState a.mem p)) =
      digest Spec.compression (completed ++ pending) := by
    rw [hpacked]
    simpa only [finalize, finalBlocks, ite_eq_right hn, List.foldl_cons, List.foldl_nil,
      Spec.compression] using
      (finalize_eq_digest Spec.compression completed pending hp.completedWhole hp.pendingBound)
  have hf : ∀ b, b ≠ p.id → a.mem.live? b = s.mem.live? b := by
    intro b hb
    rw [haframe b, live?_splice_ne (show (p.withOffset 128#64).id ≠ b from Ne.symm hb)]
    change (lastMemory mid.mem p 0 lo hi).live? b = _
    rw [lastMemory_frame _ _ _ _ _ _ hb, hmidframe b,
      live?_splice_ne (show (p.withOffset 128#64).id ≠ b from Ne.symm hb)]
    change (longMemory (markerMemory s.mem p pending.length) p pending.length).live? b = _
    rw [longMemory_frame _ _ _ _ hb, markerMemory_frame _ _ _ _ hb]
  refine ⟨s.popFrame (outputMemory a.mem p o), ?_,
    output_post s a p o _ h.wf h.outputRange.fits ha.outputRange h.outputSeparate hd hf⟩
  exact long_call p o s mid a pending.length lo hi hp.pendingBound (by omega) h.contextRange.fits
    ((word_sourceRead _ _).trans hp.pendingCount)
    (word_sourceRead _ _) (word_sourceRead _ _) ha.contextRange.fits ha.outputRange.fits
    hmid.contextRange.fits hrunFirst hrun

/-- Actual source CFG finalization of the represented byte stream, including
both padding branches, return pointer, output digest, and caller frame. The
sole remaining local dependency is the separately proved scalar-core contract. -/
theorem call_digest
    (hcore : ∀ (s : GlobalState) (kp chain data : Pointer) (count : BitVec 64),
      Core.Ready s kp chain data count → Core.Executes s chain data count)
    (s : GlobalState) (p o kp : Pointer) (completed pending : Bytes)
    (h : Ready s p o kp) (hp : ContextRepresents s.mem p completed pending) :
    ∃ after, StateT.run (runFunction (finish.denote
        (.cons (.value o) (Ctxt.Valuation.singleton (.value p))))) s =
      .value ([.value o]ₕ, after) ∧ Post s after p o (completed ++ pending) := by
  by_cases hn : pending.length < 112
  · exact short_correct hcore s p o kp completed pending h hp hn
  · exact long_correct hcore s p o kp completed pending h hp hn

end FinishCorrect
end Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource
