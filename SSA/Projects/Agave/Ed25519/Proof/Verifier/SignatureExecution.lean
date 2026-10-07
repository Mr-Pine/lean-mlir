import SSA.Projects.Agave.Ed25519.Proof.Verifier.SignatureExecutionProgram
import SSA.Projects.Agave.Ed25519.Proof.Verifier.WrapperExecution

namespace Agave.Ed25519.Verifier.Execution.Signature
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution (SmallRange)

/-- The exact two stores of the dependency's signature constructor. -/
def copied (state : GlobalState) (destination source : Pointer) : GlobalState :=
  { state with mem :=
    ((state.mem.storeAt destination (state.mem.readAt source 256)).storeAt
      (destination.add 32#64) (state.mem.readAt (source.add 32#64) 256)) }

set_option maxRecDepth 10000 in
set_option maxHeartbeats 800000 in
/-- Execution on arbitrary signature bytes. The two live 64-byte ranges and
separate allocations are the only input constraints; there is no scalar or
point-validity requirement. No allocation is performed by this helper. -/
theorem program_call (destination source : Pointer) (state : GlobalState)
    (hwf : state.WF) (hd : SmallRange state.mem destination 64)
    (hs : SmallRange state.mem source 64) (hne : destination.id ≠ source.id) :
    program.call (program.args (.value destination) (.value source)) state =
      .value (.nil, copied state destination source) := by
  have hd0 := hd.fits_add (k := 0) (count := 32) (by decide)
  have hs0 := hs.fits_add (k := 0) (count := 32) (by decide)
  have hd32 := hd.fits_add (k := 32) (count := 32) (by decide)
  have hs32 := hs.fits_add (k := 32) (count := 32) (by decide)
  simp only [Pointer.add_zero] at hd0 hs0
  have hdisjoint : (Range.of destination 256).Disjoint (Range.of source 256) :=
    Range.disjoint_of_id_ne hne
  have hdisjoint32 : (Range.of (destination.add 32#64) 256).Disjoint
      (Range.of (source.add 32#64) 256) := Range.disjoint_of_id_ne hne
  have hsource32 : (Range.of destination 256).Disjoint
      (Range.of (source.add 32#64) 256) := Range.disjoint_of_id_ne hne
  func_init
  block_init
  step_pure
  have hgep := hs.gep (k := 32) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  step_memcpy
  have hgep := hd.gep (k := 32) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  step_memcpy
  finish_block
  rw [hS]
  erase_frame
  subst_vars
  rfl

theorem copied_wf (state : GlobalState) (destination source : Pointer) (hwf : state.WF) :
    (copied state destination source).WF :=
  hwf.storeAt.storeAt

theorem copied_smallRange (state : GlobalState) (destination source query : Pointer)
    (bytes : Nat) (h : SmallRange state.mem query bytes) :
    SmallRange (copied state destination source).mem query bytes :=
  (h.storeAt destination (state.mem.readAt source 256)).storeAt
    (destination.add 32#64) (state.mem.readAt (source.add 32#64) 256)

/-- Every unrelated byte range is unchanged. This includes the input bytes,
message, public key and copied public-key payload when allocations differ. -/
theorem copied_read_frame (state : GlobalState) (destination source query : Pointer)
    (width : Nat) (hne : destination.id ≠ query.id) :
    (copied state destination source).mem.readAt query width =
      state.mem.readAt query width := by
  dsimp only [copied]
  rw [MemoryState.readAt_storeAt_disjoint
    (Range.disjoint_of_id_ne (p := destination.add 32#64) (q := query) hne),
    MemoryState.readAt_storeAt_disjoint (Range.disjoint_of_id_ne hne)]

theorem copied_read_R (state : GlobalState) (destination source : Pointer)
    (hd : SmallRange state.mem destination 64) :
    (copied state destination source).mem.readAt destination 256 =
      state.mem.readAt source 256 := by
  have hchunks := hd.disjoint_chunks (i := 1) (j := 0) (by decide) (by decide) (by decide)
  simp only [Nat.mul_zero, Nat.mul_one, Pointer.add_zero] at hchunks
  have hfit := hd.fits_add (k := 0) (count := 32) (by decide)
  simp only [Pointer.add_zero] at hfit
  dsimp only [copied]
  rw [MemoryState.readAt_storeAt_disjoint hchunks, MemoryState.readAt_storeAt_self hfit]

theorem copied_read_S (state : GlobalState) (destination source : Pointer)
    (hd : SmallRange state.mem destination 64) :
    (copied state destination source).mem.readAt (destination.add 32#64) 256 =
      state.mem.readAt (source.add 32#64) 256 := by
  dsimp only [copied]
  apply MemoryState.readAt_storeAt_self
  exact (hd.storeAt destination (state.mem.readAt source 256)).fits_add
    (k := 32) (count := 32) (by decide)

/-- Specialize the exact constructor to the wrapper's signature call site.
The state includes the wrapper's preceding public-key payload copy. -/
theorem wrapper_signature (i : Invocation) (initial afterKey : GlobalState)
    (hwf : (Wrapper.copiedKey initial afterKey).WF)
    (hd : SmallRange (Wrapper.copiedKey initial afterKey).mem
      (Wrapper.signatureSlot initial) 64)
    (hs : SmallRange (Wrapper.copiedKey initial afterKey).mem i.signature 64)
    (hne : (Wrapper.signatureSlot initial).id ≠ i.signature.id) :
    program.call (Wrapper.ptrArgs (Wrapper.signatureSlot initial) i.signature)
      (Wrapper.copiedKey initial afterKey) = .value (.nil,
        copied (Wrapper.copiedKey initial afterKey) (Wrapper.signatureSlot initial) i.signature) := by
  exact program_call _ _ _ hwf hd hs hne

/-- Discharge the signature field of the wrapper's primitive contracts by
linking the extracted dependency body. Only the separate Dalek call remains. -/
theorem wrapper_successCalls (p : Wrapper.Primitives) (i : Invocation)
    (initial afterKey afterDalek : GlobalState) (accepted : Bool)
    (hmemory : Wrapper.KeyMemory initial afterKey)
    (hwf : (Wrapper.copiedKey initial afterKey).WF)
    (hd : SmallRange (Wrapper.copiedKey initial afterKey).mem
      (Wrapper.signatureSlot initial) 64)
    (hs : SmallRange (Wrapper.copiedKey initial afterKey).mem i.signature 64)
    (hne : (Wrapper.signatureSlot initial).id ≠ i.signature.id)
    (hdalek : p.verifyDalek
      (Wrapper.dalekArgs (Wrapper.keySlot initial) (Wrapper.signatureSlot initial)
        i.message i.length)
      (copied (Wrapper.copiedKey initial afterKey) (Wrapper.signatureSlot initial) i.signature) =
      .value (.cons (.value (resultCode accepted)) .nil, afterDalek)) :
    Wrapper.SuccessCalls { p with signatureFromBytes := program.call } i initial afterKey
      (copied (Wrapper.copiedKey initial afterKey) (Wrapper.signatureSlot initial) i.signature)
      afterDalek accepted := by
  exact ⟨hmemory, wrapper_signature i initial afterKey hwf hd hs hne, hdalek⟩

end Agave.Ed25519.Verifier.Execution.Signature
