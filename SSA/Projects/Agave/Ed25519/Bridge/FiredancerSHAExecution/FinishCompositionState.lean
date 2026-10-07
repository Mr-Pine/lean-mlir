import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.FinishCompositionMemory

namespace Agave.Ed25519.Bridge.FiredancerSHAExecution.Finish
open LeanMLIR.RIR Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.SHA512 Agave.Ed25519.SHA512.Spec
open Agave.Ed25519.Verifier.Execution.Challenge
open Agave.Ed25519.Bridge.Challenge
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

structure Ready (state : GlobalState) (context output kp : Pointer) : Prop where
  wf : state.WF
  contextLive : SmallRange state.mem context 224
  outputLive : SmallRange state.mem output 64
  constants : ConstantsReady state.mem kp
  context_ne_constants : context.id ≠ kp.id
  output_ne_context : output.id ≠ context.id

theorem Ready.storeAt {state : GlobalState} {context output kp p : Pointer}
    {w : Nat} (h : Ready state context output kp) (x : BitVec w)
    (hp : p.id = context.id) :
    Ready {state with mem := state.mem.storeAt p x} context output kp := by
  exact ⟨h.wf.storeAt, h.contextLive.storeAt _ _, h.outputLive.storeAt _ _,
    h.constants.storeAt x (by rw [hp]; exact h.context_ne_constants),
    h.context_ne_constants, h.output_ne_context⟩

def markerState (state : GlobalState) (context : Pointer) (used : Nat) : GlobalState :=
  {state with mem := markerMemory state.mem context used}

def longState (state : GlobalState) (context : Pointer) (used : Nat) : GlobalState :=
  {state with mem := longMemory state.mem context used}

def lastState (state : GlobalState) (context : Pointer) (n : Nat) (lo hi : Word) : GlobalState :=
  {state with mem := lastMemory state.mem context n lo hi}

def compressionState (state : GlobalState) (context : Pointer) : GlobalState :=
  Core.coreCallState state (context.add 128#64) context (readState state.mem context)

def finalOutputState (state : GlobalState) (context output : Pointer) : GlobalState :=
  {state with mem := outputMemory state.mem output (readState state.mem context)}

def beforeOutput (state : GlobalState) (context : Pointer) (used : Nat) (lo hi : Word) : GlobalState :=
  let marked := markerState state context used
  if used < 112 then compressionState (lastState marked context (used + 1) lo hi) context
  else
    let middle := compressionState (longState marked context used) context
    compressionState (lastState middle context 0 lo hi) context

def finishState (state : GlobalState) (context output : Pointer) (used : Nat)
    (lo hi : Word) : GlobalState :=
  finalOutputState (beforeOutput state context used lo hi) context output

theorem Ready.marker {state : GlobalState} {context output kp : Pointer}
    (h : Ready state context output kp) (used : Nat) :
    Ready (markerState state context used) context output kp :=
  h.storeAt _ rfl

theorem Ready.long {state : GlobalState} {context output kp : Pointer}
    (h : Ready state context output kp) (used : Nat) :
    Ready (longState state context used) context output kp :=
  h.storeAt _ rfl

theorem Ready.last {state : GlobalState} {context output kp : Pointer}
    (h : Ready state context output kp) (n : Nat) (lo hi : Word) :
    Ready (lastState state context n lo hi) context output kp :=
  by
    have h1 := h.storeAt (p := context.add (BitVec.ofNat 64 n)) ((0#8).replicate (112 - n)) rfl
    have h2 := h1.storeAt (p := context.add 112#64)
      (Agave.Ed25519.Verifier.Execution.SHA512Finalization.swapBytes hi) rfl
    exact h2.storeAt (p := context.add 120#64)
      (Agave.Ed25519.Verifier.Execution.SHA512Finalization.swapBytes lo) rfl

theorem Ready.compression {state : GlobalState} {context output kp : Pointer}
    (h : Ready state context output kp) :
    Ready (compressionState state context) context output kp := by
  refine ⟨Core.coreCallState_wf _ _ _ _ h.wf, h.contextLive.storeAt _ _,
    h.outputLive.storeAt _ _, h.constants.storeAt _ h.context_ne_constants,
    h.context_ne_constants, h.output_ne_context⟩

theorem Ready.preOutput {state : GlobalState} {context output kp : Pointer}
    (h : Ready state context output kp) (used : Nat) (lo hi : Word) :
    Ready (beforeOutput state context used lo hi) context output kp := by
  unfold beforeOutput
  split_ifs
  · exact ((h.marker used).last _ lo hi).compression
  · exact ((((h.marker used).long used).compression).last 0 lo hi).compression

theorem compression_call (kp context output : Pointer) (state : GlobalState)
    (h : Ready state context output kp) :
    (Core.program kp).call
      (Core.program.args (.value (context.add 128#64)) (.value context) (.value 1#64)) state =
      .value (.nil, compressionState state context) :=
  core_call_context kp context state h.wf h.contextLive h.constants

theorem finishState_output (state : GlobalState) (context output kp : Pointer)
    (used : Nat) (lo hi : Word) (h : Ready state context output kp) :
    readBytes (finishState state context output used lo hi).mem output 64 =
      bytesOf (n := 64) (serialize (pack (readState
        (beforeOutput state context used lo hi).mem context))) :=
  outputMemory_bytes _ _ (h.preOutput used lo hi).outputLive _

/-- Core private allocations advance the counter once per padding block. -/
theorem finishState_alloc (state : GlobalState) (context output : Pointer)
    (used : Nat) (lo hi : Word) :
    (finishState state context output used lo hi).alloc.nextFreeBlock =
      state.alloc.nextFreeBlock + (if used < 112 then 1 else 2) := by
  unfold finishState finalOutputState beforeOutput
  split_ifs <;> simp [compressionState, Core.coreCallState, lastState, longState,
    markerState, Nat.add_assoc]

/-- Erasing the finalizer's frame leaves precisely its explicit context/output
stores; every temporary core ring was already erased by its own call. -/
theorem finishState_erase (state : GlobalState) (context output : Pointer)
    (used : Nat) (lo hi : Word) (hwf : state.WF) :
    (finishState state context output used lo hi).mem.eraseFrom state.alloc.nextFreeBlock =
      (finishState state context output used lo hi).mem := by
  have he := congrArg GlobalState.mem (GlobalState.eraseFrom_self hwf)
  change state.mem.eraseFrom state.alloc.nextFreeBlock = state.mem at he
  unfold finishState finalOutputState beforeOutput
  split_ifs <;>
    simp only [compressionState, Core.coreCallState, lastState, longState, markerState,
      outputMemory, lastMemory, longMemory, markerMemory, MemoryState.eraseFrom_storeAt, he]

/-- All allocations other than context and output are exactly unchanged. -/
theorem finishState_other_block (state : GlobalState) (context output : Pointer)
    (used : Nat) (lo hi : Word) (id : BlockId)
    (hc : id ≠ context.id) (ho : id ≠ output.id) :
    (finishState state context output used lo hi).mem[id]? = state.mem[id]? := by
  have hctx (k : Word) : (⟨id, 0⟩ : Pointer).id ≠ (context.add k).id := hc
  have hout (k : Word) : (⟨id, 0⟩ : Pointer).id ≠ (output.add k).id := ho
  unfold finishState finalOutputState beforeOutput
  split_ifs <;>
    simp only [compressionState, Core.coreCallState, lastState, longState, markerState,
      outputMemory, lastMemory, longMemory, markerMemory,
      MemoryState.getElem?_storeAt_ne (hctx _), MemoryState.getElem?_storeAt_ne (hout _),
      MemoryState.getElem?_storeAt_ne (q := ⟨id, 0⟩) ho]

end Agave.Ed25519.Bridge.FiredancerSHAExecution.Finish
