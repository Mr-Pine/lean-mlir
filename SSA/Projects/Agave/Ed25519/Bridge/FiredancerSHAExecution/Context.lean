import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.Initialize
import SSA.Projects.Agave.Ed25519.Proof.SHA512.CompressionFold
import SSA.Projects.Agave.Ed25519.Proof.Verifier.ChallengeExecutionMemory

/-! Byte/word observations sufficient for streaming SHA refinement. Unlike a
whole-interpreter state equality, this relation ignores unused buffer bytes and
magic/padding fields. It carries no assumed machine-execution conclusion. -/
namespace Agave.Ed25519.Bridge.FiredancerSHAExecution
open LeanMLIR.RIR Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.SHA512 Agave.Ed25519.SHA512.Spec
open Agave.Ed25519.Verifier.Execution.Challenge
open Agave.Ed25519.Bridge.Challenge
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def stateWord (s : State) (i : Fin 8) : Word :=
  match i.val with
  | 0 => s.a | 1 => s.b | 2 => s.c | 3 => s.d
  | 4 => s.e | 5 => s.f | 6 => s.g | _ => s.h

def readState (m : MemoryState) (context : Pointer) : State :=
  ⟨m.readAt (context.add 128#64) 64, m.readAt (context.add 136#64) 64,
   m.readAt (context.add 144#64) 64, m.readAt (context.add 152#64) 64,
   m.readAt (context.add 160#64) 64, m.readAt (context.add 168#64) 64,
   m.readAt (context.add 176#64) 64, m.readAt (context.add 184#64) 64⟩

structure ContextRepresents (m : MemoryState) (context : Pointer)
    (completed pending : Bytes) : Prop where
  live : SmallRange m context 224
  completedWhole : completed.length % 128 = 0
  pendingBound : pending.length < 128
  pendingBytes : readBytes m context pending.length = pending
  pendingCount : m.readAt (context.add 200#64) 64 = BitVec.ofNat 64 pending.length
  chaining : readState m context = unpack (Spec.run initialWords completed)
  bitCount : m.readAt (context.add 216#64) 64 ++ m.readAt (context.add 208#64) 64 =
    BitVec.ofNat 128 (8 * (completed.length + pending.length))

namespace Init

theorem memory_live (m : MemoryState) (context : Pointer) (h : SmallRange m context 224) :
    SmallRange (memory m context) context 224 := by
  unfold memory
  repeat apply SmallRange.storeAt
  exact h

theorem memory_word (m : MemoryState) (context : Pointer) (h : SmallRange m context 224)
    (i : Fin 8) :
    (memory m context).readAt (context.add (BitVec.ofNat 64 (128 + 8 * i.val))) 64 =
      stateWord initial i := by
  fin_cases i
  · simp only [memory, stateWord, initial, Nat.reduceMul, Nat.reduceAdd]
    have hz := smallRange_disjoint_offsets h (i := 200) (countI := 24)
      (j := 128) (countJ := 8) (by decide) (by decide) (Or.inr (by decide))
    have hd1 := smallRange_disjoint_offsets h (i := 136) (countI := 8)
      (j := 128) (countJ := 8) (by decide) (by decide) (Or.inr (by decide))
    have hd2 := smallRange_disjoint_offsets h (i := 144) (countI := 8)
      (j := 128) (countJ := 8) (by decide) (by decide) (Or.inr (by decide))
    have hd3 := smallRange_disjoint_offsets h (i := 152) (countI := 8)
      (j := 128) (countJ := 8) (by decide) (by decide) (Or.inr (by decide))
    have hd4 := smallRange_disjoint_offsets h (i := 160) (countI := 8)
      (j := 128) (countJ := 8) (by decide) (by decide) (Or.inr (by decide))
    have hd5 := smallRange_disjoint_offsets h (i := 168) (countI := 8)
      (j := 128) (countJ := 8) (by decide) (by decide) (Or.inr (by decide))
    have hd6 := smallRange_disjoint_offsets h (i := 176) (countI := 8)
      (j := 128) (countJ := 8) (by decide) (by decide) (Or.inr (by decide))
    have hd7 := smallRange_disjoint_offsets h (i := 184) (countI := 8)
      (j := 128) (countJ := 8) (by decide) (by decide) (Or.inr (by decide))
    rw [MemoryState.readAt_storeAt_disjoint hz, MemoryState.readAt_storeAt_disjoint hd7, MemoryState.readAt_storeAt_disjoint hd6, MemoryState.readAt_storeAt_disjoint hd5, MemoryState.readAt_storeAt_disjoint hd4, MemoryState.readAt_storeAt_disjoint hd3, MemoryState.readAt_storeAt_disjoint hd2, MemoryState.readAt_storeAt_disjoint hd1]
    have hf := h.fits_add (k := 128) (count := 8) (by decide)
    exact MemoryState.readAt_storeAt_self hf _
  · simp only [memory, stateWord, initial, Nat.reduceMul, Nat.reduceAdd]
    have hz := smallRange_disjoint_offsets h (i := 200) (countI := 24)
      (j := 136) (countJ := 8) (by decide) (by decide) (Or.inr (by decide))
    have hd2 := smallRange_disjoint_offsets h (i := 144) (countI := 8)
      (j := 136) (countJ := 8) (by decide) (by decide) (Or.inr (by decide))
    have hd3 := smallRange_disjoint_offsets h (i := 152) (countI := 8)
      (j := 136) (countJ := 8) (by decide) (by decide) (Or.inr (by decide))
    have hd4 := smallRange_disjoint_offsets h (i := 160) (countI := 8)
      (j := 136) (countJ := 8) (by decide) (by decide) (Or.inr (by decide))
    have hd5 := smallRange_disjoint_offsets h (i := 168) (countI := 8)
      (j := 136) (countJ := 8) (by decide) (by decide) (Or.inr (by decide))
    have hd6 := smallRange_disjoint_offsets h (i := 176) (countI := 8)
      (j := 136) (countJ := 8) (by decide) (by decide) (Or.inr (by decide))
    have hd7 := smallRange_disjoint_offsets h (i := 184) (countI := 8)
      (j := 136) (countJ := 8) (by decide) (by decide) (Or.inr (by decide))
    rw [MemoryState.readAt_storeAt_disjoint hz, MemoryState.readAt_storeAt_disjoint hd7, MemoryState.readAt_storeAt_disjoint hd6, MemoryState.readAt_storeAt_disjoint hd5, MemoryState.readAt_storeAt_disjoint hd4, MemoryState.readAt_storeAt_disjoint hd3, MemoryState.readAt_storeAt_disjoint hd2]
    have hf := h.fits_add (k := 136) (count := 8) (by decide)
    exact MemoryState.readAt_storeAt_self hf.storeAt _
  · simp only [memory, stateWord, initial, Nat.reduceMul, Nat.reduceAdd]
    have hz := smallRange_disjoint_offsets h (i := 200) (countI := 24)
      (j := 144) (countJ := 8) (by decide) (by decide) (Or.inr (by decide))
    have hd3 := smallRange_disjoint_offsets h (i := 152) (countI := 8)
      (j := 144) (countJ := 8) (by decide) (by decide) (Or.inr (by decide))
    have hd4 := smallRange_disjoint_offsets h (i := 160) (countI := 8)
      (j := 144) (countJ := 8) (by decide) (by decide) (Or.inr (by decide))
    have hd5 := smallRange_disjoint_offsets h (i := 168) (countI := 8)
      (j := 144) (countJ := 8) (by decide) (by decide) (Or.inr (by decide))
    have hd6 := smallRange_disjoint_offsets h (i := 176) (countI := 8)
      (j := 144) (countJ := 8) (by decide) (by decide) (Or.inr (by decide))
    have hd7 := smallRange_disjoint_offsets h (i := 184) (countI := 8)
      (j := 144) (countJ := 8) (by decide) (by decide) (Or.inr (by decide))
    rw [MemoryState.readAt_storeAt_disjoint hz, MemoryState.readAt_storeAt_disjoint hd7, MemoryState.readAt_storeAt_disjoint hd6, MemoryState.readAt_storeAt_disjoint hd5, MemoryState.readAt_storeAt_disjoint hd4, MemoryState.readAt_storeAt_disjoint hd3]
    have hf := h.fits_add (k := 144) (count := 8) (by decide)
    exact MemoryState.readAt_storeAt_self hf.storeAt.storeAt _
  · simp only [memory, stateWord, initial, Nat.reduceMul, Nat.reduceAdd]
    have hz := smallRange_disjoint_offsets h (i := 200) (countI := 24)
      (j := 152) (countJ := 8) (by decide) (by decide) (Or.inr (by decide))
    have hd4 := smallRange_disjoint_offsets h (i := 160) (countI := 8)
      (j := 152) (countJ := 8) (by decide) (by decide) (Or.inr (by decide))
    have hd5 := smallRange_disjoint_offsets h (i := 168) (countI := 8)
      (j := 152) (countJ := 8) (by decide) (by decide) (Or.inr (by decide))
    have hd6 := smallRange_disjoint_offsets h (i := 176) (countI := 8)
      (j := 152) (countJ := 8) (by decide) (by decide) (Or.inr (by decide))
    have hd7 := smallRange_disjoint_offsets h (i := 184) (countI := 8)
      (j := 152) (countJ := 8) (by decide) (by decide) (Or.inr (by decide))
    rw [MemoryState.readAt_storeAt_disjoint hz, MemoryState.readAt_storeAt_disjoint hd7, MemoryState.readAt_storeAt_disjoint hd6, MemoryState.readAt_storeAt_disjoint hd5, MemoryState.readAt_storeAt_disjoint hd4]
    have hf := h.fits_add (k := 152) (count := 8) (by decide)
    exact MemoryState.readAt_storeAt_self hf.storeAt.storeAt.storeAt _
  · simp only [memory, stateWord, initial, Nat.reduceMul, Nat.reduceAdd]
    have hz := smallRange_disjoint_offsets h (i := 200) (countI := 24)
      (j := 160) (countJ := 8) (by decide) (by decide) (Or.inr (by decide))
    have hd5 := smallRange_disjoint_offsets h (i := 168) (countI := 8)
      (j := 160) (countJ := 8) (by decide) (by decide) (Or.inr (by decide))
    have hd6 := smallRange_disjoint_offsets h (i := 176) (countI := 8)
      (j := 160) (countJ := 8) (by decide) (by decide) (Or.inr (by decide))
    have hd7 := smallRange_disjoint_offsets h (i := 184) (countI := 8)
      (j := 160) (countJ := 8) (by decide) (by decide) (Or.inr (by decide))
    rw [MemoryState.readAt_storeAt_disjoint hz, MemoryState.readAt_storeAt_disjoint hd7, MemoryState.readAt_storeAt_disjoint hd6, MemoryState.readAt_storeAt_disjoint hd5]
    have hf := h.fits_add (k := 160) (count := 8) (by decide)
    exact MemoryState.readAt_storeAt_self hf.storeAt.storeAt.storeAt.storeAt _
  · simp only [memory, stateWord, initial, Nat.reduceMul, Nat.reduceAdd]
    have hz := smallRange_disjoint_offsets h (i := 200) (countI := 24)
      (j := 168) (countJ := 8) (by decide) (by decide) (Or.inr (by decide))
    have hd6 := smallRange_disjoint_offsets h (i := 176) (countI := 8)
      (j := 168) (countJ := 8) (by decide) (by decide) (Or.inr (by decide))
    have hd7 := smallRange_disjoint_offsets h (i := 184) (countI := 8)
      (j := 168) (countJ := 8) (by decide) (by decide) (Or.inr (by decide))
    rw [MemoryState.readAt_storeAt_disjoint hz, MemoryState.readAt_storeAt_disjoint hd7, MemoryState.readAt_storeAt_disjoint hd6]
    have hf := h.fits_add (k := 168) (count := 8) (by decide)
    exact MemoryState.readAt_storeAt_self hf.storeAt.storeAt.storeAt.storeAt.storeAt _
  · simp only [memory, stateWord, initial, Nat.reduceMul, Nat.reduceAdd]
    have hz := smallRange_disjoint_offsets h (i := 200) (countI := 24)
      (j := 176) (countJ := 8) (by decide) (by decide) (Or.inr (by decide))
    have hd7 := smallRange_disjoint_offsets h (i := 184) (countI := 8)
      (j := 176) (countJ := 8) (by decide) (by decide) (Or.inr (by decide))
    rw [MemoryState.readAt_storeAt_disjoint hz, MemoryState.readAt_storeAt_disjoint hd7]
    have hf := h.fits_add (k := 176) (count := 8) (by decide)
    exact MemoryState.readAt_storeAt_self hf.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt _
  · simp only [memory, stateWord, initial, Nat.reduceMul, Nat.reduceAdd]
    have hz := smallRange_disjoint_offsets h (i := 200) (countI := 24)
      (j := 184) (countJ := 8) (by decide) (by decide) (Or.inr (by decide))
    rw [MemoryState.readAt_storeAt_disjoint hz]
    have hf := h.fits_add (k := 184) (count := 8) (by decide)
    exact MemoryState.readAt_storeAt_self hf.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt _

theorem memory_chaining (m : MemoryState) (context : Pointer) (h : SmallRange m context 224) :
    readState (memory m context) context = initial := by
  unfold readState
  congr 1
  · exact memory_word m context h 0
  · exact memory_word m context h 1
  · exact memory_word m context h 2
  · exact memory_word m context h 3
  · exact memory_word m context h 4
  · exact memory_word m context h 5
  · exact memory_word m context h 6
  · exact memory_word m context h 7

theorem memory_count (m : MemoryState) (context : Pointer) (h : SmallRange m context 224)
    (i : Fin 3) :
    (memory m context).readAt (context.add (BitVec.ofNat 64 (200 + 8 * i.val))) 64 = 0 := by
  have hbase : SmallRange m (context.add 200#64) 24 := smallRange_add h (by decide)
  have hf := hbase.fits
  have hov := hbase.no_wrap (k := 8 * i.val) (by have := i.isLt; omega)
  let before := ((((((((m.storeAt (context.add 128#64) 7640891576956012808#64).storeAt (context.add 136#64) 13503953896175478587#64).storeAt (context.add 144#64) 4354685564936845355#64).storeAt (context.add 152#64) 11912009170470909681#64).storeAt (context.add 160#64) 5840696475078001361#64).storeAt (context.add 168#64) 11170449401992604703#64).storeAt (context.add 176#64) 2270897969802886507#64).storeAt (context.add 184#64) 6620516959819538809#64)
  have hbefore : Fits before (context.add 200#64) 192 :=
    hf.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt
  change (before.storeAt (context.add 200#64) 0#192).readAt _ _ = _
  have hread := MemoryState.readAt_storeAt_add
    (off := BitVec.ofNat 64 (8 * i.val))
    hbefore hov
    (show (BitVec.ofNat 64 (8 * i.val)).toNat * 8 + 64 ≤ 192 by
      have hi := i.isLt
      simp only [BitVec.toNat_ofNat]
      omega) (0#192)
  fin_cases i <;> simpa [Pointer.add_add] using hread

/-- The actual initializer establishes the streaming relation on the empty
transcript, for arbitrary incoming bytes in the context allocation. -/
theorem memory_represents (m : MemoryState) (context : Pointer) (h : SmallRange m context 224) :
    ContextRepresents (memory m context) context [] [] := by
  refine ⟨memory_live m context h, by decide, by decide, ?_, ?_, ?_, ?_⟩
  · simp [readBytes]
  · exact memory_count m context h 0
  · rw [memory_chaining m context h, Spec.run_empty, extracted_initial_eq]
  · have hlo := memory_count m context h 1
    have hhi := memory_count m context h 2
    change (memory m context).readAt (context.add 216#64) 64 ++
      (memory m context).readAt (context.add 208#64) 64 = 0#128
    change (memory m context).readAt (context.add 208#64) 64 = 0#64 at hlo
    change (memory m context).readAt (context.add 216#64) 64 = 0#64 at hhi
    rw [hlo, hhi]
    rfl

theorem call_represents (state : GlobalState) (context : Pointer)
    (hwf : state.WF) (h : SmallRange state.mem context 224) :
    ∃ after,
      program.call (program.args (.value context)) state =
        .value (.cons (.value context) .nil, after) ∧
      ContextRepresents after.mem context [] [] ∧ after.WF := by
  exact ⟨_, call state context hwf h, memory_represents state.mem context h,
    memory_wf state context hwf⟩

end Init
end Agave.Ed25519.Bridge.FiredancerSHAExecution
