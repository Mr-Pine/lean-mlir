import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.SqrtRatioInlineComposeMemory
import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.DecoderOuterFrame

/-! The actual sqrt call and caller observations from its exact finite prefix.
Only instructions before pc1047 remain a premise; the final instructions,
black-box call, return and stack erasure are supplied by checked execution. -/
namespace Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.CallFromPrefix
open LeanMLIR.RIR
open Reduce64.Execution (SmallRange)
open SmallOrder.Execution (PrivateFrame)
open Verifier.Execution.Dalek (OutputFrame ReadBytes disjoint_add_subrange)
set_option maxRecDepth 32000
set_option maxHeartbeats 2000000
attribute [local irreducible] wordSqrt

/-- An exact original-source prefix and its concrete output-cut observations. -/
def PrefixWitness (g : Globals) (out u v : Pointer) (entry : GlobalState)
    (result : Bool × Pow22501.TightWords) : Prop :=
  ∃ (E : ⟪program.Γ⟫) (s : GlobalState) (d : ExecutionOutputData),
    Cutpoint.segment (program sqrtRatioPrimitives g) 0 0 1047
      (Env.init (program.args (.value out) (.value u) (.value v)).get) entry = .value (E,s) ∧
    ExecutionOutputReady E s out d ∧ Inline.ScratchFrame entry s ∧
    s.mem.readAt d.root 320 = limbBytes result.2.limbs ∧
    d.first ||| d.second = if result.1 then 1#8 else 0#8

/-- Exact caller state after the actual callee stack erasure. -/
def callState (entry reached : GlobalState) (out : Pointer) (flag : BitVec 8)
    (root : BitVec 320) : GlobalState :=
  {alloc := ⟨reached.alloc.nextFreeBlock + 1⟩,
    mem := (entry.mem.storeAt out flag).storeAt (out.add 8#64) root}

theorem callState_wf (entry reached : GlobalState) (out : Pointer)
    (flag : BitVec 8) (root : BitVec 320) (hwf : entry.WF)
    (hc : entry.alloc.nextFreeBlock ≤ reached.alloc.nextFreeBlock) :
    (callState entry reached out flag root).WF := by
  have hw : ({entry with mem := (entry.mem.storeAt out flag).storeAt (out.add 8#64) root} : GlobalState).WF :=
    hwf.storeAt.storeAt
  intro id hid
  exact lt_of_lt_of_le (hw id hid) (by dsimp [callState]; omega)

theorem callState_frame (entry reached : GlobalState) (out : Pointer)
    (flag : BitVec 8) (root : BitVec 320) (hwf : entry.WF)
    (hc : entry.alloc.nextFreeBlock ≤ reached.alloc.nextFreeBlock)
    (hout : SmallRange entry.mem out 48) :
    OutputFrame entry (callState entry reached out flag root) out 48 := by
  refine ⟨callState_wf entry reached out flag root hwf hc, ?_, ?_⟩
  · intro q n h
    exact (h.storeAt _ _).storeAt _ _
  · intro q w hd
    have h0 := disjoint_add_subrange hout hd (k := 0) (count := 1) (by decide)
    have h8 := disjoint_add_subrange hout hd (k := 8) (count := 40) (by decide)
    simp only [Pointer.add_zero] at h0
    exact (MemoryState.readAt_storeAt_disjoint h8.symm root).trans
      (MemoryState.readAt_storeAt_disjoint h0.symm flag)

theorem callState_flag (entry reached : GlobalState) (out : Pointer)
    (flag : BitVec 8) (root : BitVec 320) (hout : SmallRange entry.mem out 48) :
    (callState entry reached out flag root).mem.readAt out 8 = flag :=
  outputState_flag hout flag root

theorem callState_root (entry reached : GlobalState) (out : Pointer)
    (flag : BitVec 8) (root : BitVec 320) (hout : SmallRange entry.mem out 48) :
    ReadBytes (callState entry reached out flag root) (out.add 8#64) 40 root :=
  outputState_root hout flag root

theorem callState_allocation (entry reached : GlobalState) (out : Pointer)
    (flag : BitVec 8) (root : BitVec 320) (id : BlockId) (hi : id ≠ out.id) :
    (callState entry reached out flag root).mem[id]? = entry.mem[id]? := by
  simp only [callState]
  rw [MemoryState.getElem?_storeAt_ne (p := out.add 8#64) (q := ⟨id,0⟩) hi,
    MemoryState.getElem?_storeAt_ne (p := out) (q := ⟨id,0⟩) hi]

theorem callState_shape (entry reached : GlobalState) (out : Pointer)
    (flag : BitVec 8) (root : BitVec 320) (id : BlockId) :
    ((callState entry reached out flag root).mem[id]?).map MemoryBlock.length =
      (entry.mem[id]?).map MemoryBlock.length := by
  simp only [callState, SerialPoint.Execution.storeAt_allocationShape]

/-- A sqrt output in an enclosing caller's scratch remains private to that caller. -/
theorem callState_private (entry reached : GlobalState) (out : Pointer)
    (flag : BitVec 8) (root : BitVec 320)
    (hc : entry.alloc.nextFreeBlock ≤ reached.alloc.nextFreeBlock)
    (h : PrivateFrame before entry) (hi : before.alloc.nextFreeBlock ≤ out.id.id) :
    PrivateFrame before (callState entry reached out flag root) := by
  refine ⟨callState_wf entry reached out flag root h.wellFormed hc, ?_, ?_⟩
  · have := h.counter
    dsimp [callState]
    omega
  · simp only [callState, MemoryState.eraseFrom_storeAt]
    rw [MemoryState.storeAt_eraseFrom_of_le (p := out) hi,
      MemoryState.storeAt_eraseFrom_of_le (p := out.add 8#64) hi, h.memory]

theorem call_of_prefix (g : Globals) (out u v : Pointer) (entry s : GlobalState)
    (E : ⟪program.Γ⟫) (d : ExecutionOutputData)
    (hprefix : Cutpoint.segment (program sqrtRatioPrimitives g) 0 0 1047
      (Env.init (program.args (.value out) (.value u) (.value v)).get) entry = .value (E,s))
    (hready : ExecutionOutputReady E s out d) (hframe : Inline.ScratchFrame entry s) :
    (program sqrtRatioPrimitives g).call (program.args (.value out) (.value u) (.value v)) entry =
      .value (.nil, callState entry s out (d.first ||| d.second) (s.mem.readAt d.root 320)) := by
  have hp := Cutpoint.after_segment (program sqrtRatioPrimitives g) 0 0 1047
    (Env.init (program.args (.value out) (.value u) (.value v)).get) E entry s hprefix
  rw [Cutpoint.zero] at hp
  have hs := output_run g E s out d.root d.first d.second hready.wf hready.outputLive
    hready.rootLive hready.disjoint hready.outputRegister hready.rootRegister
    hready.firstRegister hready.secondRegister hready.eightRegister hready.fortyRegister
  rw [Func.call_eq_run_bind, Func.run_runFrom_eq]
  change ((program sqrtRatioPrimitives g).runFrom
    (Env.init (program.args (.value out) (.value u) (.value v)).get) 0 entry >>= _) = _
  rw [hp, hs]
  simp only [PoisonOr.value_bind]
  rw [executionOutputState_public entry s out _ _ hframe.publicFrame.memory]
  rfl

/-- These caller observations are conclusions of exact execution, not premises. -/
structure CallObservation (entry after : GlobalState) (out : Pointer)
    (result : Bool × Pow22501.TightWords) : Prop where
  frame : OutputFrame entry after out 48
  flag : after.mem.readAt out 8 = if result.1 then 1#8 else 0#8
  root : ReadBytes after (out.add 8#64) 40 (limbBytes result.2.limbs)
  allocation : ∀ id : BlockId, id ≠ out.id → after.mem[id]? = entry.mem[id]?
  shape : ∀ id : BlockId, (after.mem[id]?).map MemoryBlock.length =
    (entry.mem[id]?).map MemoryBlock.length
  privateFrame : ∀ before, PrivateFrame before entry → before.alloc.nextFreeBlock ≤ out.id.id →
    PrivateFrame before after

theorem call_of_witness (g : Globals) (out u v : Pointer) (entry : GlobalState)
    (result : Bool × Pow22501.TightWords) (hwf : entry.WF) (hout : SmallRange entry.mem out 48)
    (h : PrefixWitness g out u v entry result) :
    ∃ after, (program sqrtRatioPrimitives g).call
      (program.args (.value out) (.value u) (.value v)) entry = .value (.nil,after) ∧
      CallObservation entry after out result := by
  obtain ⟨E,s,d,hp,hr,hf,hroot,hflag⟩ := h
  refine ⟨callState entry s out (if result.1 then 1#8 else 0#8) (limbBytes result.2.limbs), ?_, ?_⟩
  · simpa only [hroot,hflag] using call_of_prefix g out u v entry s E d hp hr hf
  · exact ⟨callState_frame entry s out _ _ hwf hf.publicFrame.counter hout,
      callState_flag entry s out _ _ hout, callState_root entry s out _ _ hout,
      callState_allocation entry s out _ _, callState_shape entry s out _ _,
      fun before hbefore hi => callState_private entry s out _ _ hf.publicFrame.counter hbefore hi⟩

end Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.CallFromPrefix
