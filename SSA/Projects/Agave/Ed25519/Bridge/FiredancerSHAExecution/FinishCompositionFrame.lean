import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.FinishCompositionState

/-! Fine caller frame, including untouched metadata in the context allocation. -/
namespace Agave.Ed25519.Bridge.FiredancerSHAExecution.Finish
open LeanMLIR.RIR Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.SHA512.Spec
open Agave.Ed25519.Verifier.Execution.Challenge
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- Any inbounds subrange inherits disjointness from its containing range. -/
theorem disjoint_subrange (mem : MemoryState) (p q : Pointer) (bytes i count bits : Nat)
    (hr : SmallRange mem p bytes) (hi : i + count ≤ bytes)
    (hd : (Range.of p (8 * bytes)).Disjoint (Range.of q bits)) :
    (Range.of (p.add (BitVec.ofNat 64 i)) (8 * count)).Disjoint (Range.of q bits) := by
  have hb := hr.offset_lt
  have hi64 : i < 2^64 := by omega
  have hoff := Pointer.offsetInBits_add (hr.no_wrap (k := i) (by omega))
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi64] at hoff
  rcases hd with hne | hb | ha
  · exact Or.inl hne
  · apply Or.inr ∘ Or.inl
    change p.offsetInBits + 8 * bytes ≤ q.offsetInBits at hb
    change (p.add (BitVec.ofNat 64 i)).offsetInBits + 8 * count ≤ q.offsetInBits
    rw [hoff]
    omega
  · apply Or.inr ∘ Or.inr
    change q.offsetInBits + bits ≤ p.offsetInBits at ha
    change q.offsetInBits + bits ≤ (p.add (BitVec.ofNat 64 i)).offsetInBits
    rw [hoff]
    omega

/-- The exact finalizer only writes context bytes 0..191 and output bytes 0..63.
This frame also applies to distinct ranges within one caller allocation. -/
theorem finishState_readAt_frame (state : GlobalState) (context output q : Pointer)
    (used : Nat) (lo hi : Word) (bits : Nat)
    (hc : SmallRange state.mem context 224) (ho : SmallRange state.mem output 64)
    (hu : used < 128)
    (hdc : (Range.of context 1536).Disjoint (Range.of q bits))
    (hdo : (Range.of output 512).Disjoint (Range.of q bits)) :
    (finishState state context output used lo hi).mem.readAt q bits = state.mem.readAt q bits := by
  have hctx (i count : Nat) (hb : i + count ≤ 192) :=
    disjoint_subrange state.mem context q 192 i count bits
      (smallRange_mono hc (by decide)) hb hdc
  have hout (i : Nat) (hb : i + 8 ≤ 64) :=
    disjoint_subrange state.mem output q 64 i 8 bits ho hb hdo
  have hmarker := hctx used 1 (by omega)
  have hlong := hctx (used + 1) (127 - used) (by omega)
  have hout0 : (Range.of output 64).Disjoint (Range.of q bits) := by
    simpa using hout 0 (by decide)
  have hzero : (Range.of context 896).Disjoint (Range.of q bits) := by
    simpa using hctx 0 112 (by decide)
  have h112 := hctx 112 8 (by decide)
  have h120 := hctx 120 8 (by decide)
  have hchain := hctx 128 64 (by decide)
  unfold finishState finalOutputState beforeOutput
  split_ifs with hs
  · have hshort := hctx (used + 1) (112 - (used + 1)) (by omega)
    simp only [compressionState, Core.coreCallState, lastState, markerState,
      outputMemory, lastMemory, markerMemory,
      MemoryState.readAt_storeAt_disjoint hout0,
      MemoryState.readAt_storeAt_disjoint (hout 8 (by decide)),
      MemoryState.readAt_storeAt_disjoint (hout 16 (by decide)),
      MemoryState.readAt_storeAt_disjoint (hout 24 (by decide)),
      MemoryState.readAt_storeAt_disjoint (hout 32 (by decide)),
      MemoryState.readAt_storeAt_disjoint (hout 40 (by decide)),
      MemoryState.readAt_storeAt_disjoint (hout 48 (by decide)),
      MemoryState.readAt_storeAt_disjoint (hout 56 (by decide)),
      MemoryState.readAt_storeAt_disjoint hchain,
      MemoryState.readAt_storeAt_disjoint h120,
      MemoryState.readAt_storeAt_disjoint h112,
      MemoryState.readAt_storeAt_disjoint hshort,
      MemoryState.readAt_storeAt_disjoint hmarker]
  · simp only [compressionState, Core.coreCallState, lastState, longState, markerState,
      outputMemory, lastMemory, longMemory, markerMemory,
      MemoryState.readAt_storeAt_disjoint hout0,
      MemoryState.readAt_storeAt_disjoint (hout 8 (by decide)),
      MemoryState.readAt_storeAt_disjoint (hout 16 (by decide)),
      MemoryState.readAt_storeAt_disjoint (hout 24 (by decide)),
      MemoryState.readAt_storeAt_disjoint (hout 32 (by decide)),
      MemoryState.readAt_storeAt_disjoint (hout 40 (by decide)),
      MemoryState.readAt_storeAt_disjoint (hout 48 (by decide)),
      MemoryState.readAt_storeAt_disjoint (hout 56 (by decide)),
      MemoryState.readAt_storeAt_disjoint hchain,
      MemoryState.readAt_storeAt_disjoint h120,
      MemoryState.readAt_storeAt_disjoint h112,
      MemoryState.readAt_storeAt_disjoint hzero,
      MemoryState.readAt_storeAt_disjoint hlong,
      MemoryState.readAt_storeAt_disjoint hmarker, Pointer.add_zero]

/-- Magic/padding fields and all three counters at bytes 192..223 survive fini. -/
theorem finishState_metadata (state : GlobalState) (context output : Pointer)
    (used : Nat) (lo hi : Word) (offset count : Nat)
    (hc : SmallRange state.mem context 224) (ho : SmallRange state.mem output 64)
    (hu : used < 128) (hne : output.id ≠ context.id)
    (hloff : 192 ≤ offset) (hhi : offset + count ≤ 224) :
    (finishState state context output used lo hi).mem.readAt
      (context.add (BitVec.ofNat 64 offset)) (8 * count) =
      state.mem.readAt (context.add (BitVec.ofNat 64 offset)) (8 * count) := by
  apply finishState_readAt_frame state context output _ used lo hi _ hc ho hu
  · have hdis := smallRange_disjoint_offsets hc (i := 0) (countI := 192)
      (j := offset) (countJ := count) (by decide) hhi (Or.inl (by omega))
    simpa [Nat.mul_comm] using hdis
  · exact Or.inl hne

end Agave.Ed25519.Bridge.FiredancerSHAExecution.Finish
