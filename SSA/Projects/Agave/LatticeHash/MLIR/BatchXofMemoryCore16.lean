/- Released under Apache 2.0 license as described in the file LICENSE. -/
import SSA.Projects.Agave.LatticeHash.MLIR.BatchXofLoop16

namespace AgaveLatticeHash.MLIR.BatchXofLoop16
open LeanMLIR SLLVM Firedancer Blake3Compression CompressionRound
open InstCombine (LLVM)
open BatchReduction16
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false

/-- Initial scratch-message, schedule, and accumulator reads and allocation separation. -/
structure InitialMemory (s : GlobalState) (out msg sched : Pointer)
    (m : State Words16) (old : Nat → Vector (BitVec 16) 32) : Prop where
  scheduleFits : ∀ r i, Fits s.mem (schedulePtr16 sched r i) 64
  scheduleRead : ∀ r i, readWord? (schedulePtr16 sched r i) 64 s.mem = some (BitVec.ofNat 64 (schedule r i).val)
  messageFits : ∀ i, Fits s.mem (messagePtr16 msg i) 512
  messageRead : ∀ i, readWord? (messagePtr16 msg i) 512 s.mem = some (packBits (m i))
  outputFits : Fits s.mem out 16384
  outputWrap : out.offset.toNat + 2048 ≤ 2^64
  outputRead : ∀ c, c < 32 → readWord? (outputPtr out c) 512 s.mem = some (packBits (old c))
  scheduleSeparate : out.id ≠ sched.id
  messageSeparate : out.id ≠ msg.id

theorem outputPtr_offset (out : Pointer) (hw : out.offset.toNat + 2048 ≤ 2^64)
    (c : Nat) (hc : c < 32) :
    (outputPtr out c).offsetInBits = out.offsetInBits + 512*c := by
  rw [outputPtr, offsetInBits_withOffset_nat out (64*c) (by omega)]
  omega

theorem fits_accumulatedState (s : GlobalState) (out : Pointer)
    (cv : CV Words16) (len flags : Words16) (m : State Words16)
    (old : Nat → Vector (BitVec 16) 32) (c : Nat) {p : Pointer} {w : Nat}
    (h : Fits s.mem p w) : Fits (accumulatedState s out cv len flags m old c).mem p w := by
  induction c with
  | zero => exact h
  | succ c ih => exact fits_splice ih

theorem read_accumulatedState_ne (s : GlobalState) (out : Pointer)
    (cv : CV Words16) (len flags : Words16) (m : State Words16)
    (old : Nat → Vector (BitVec 16) 32) (c : Nat) {p : Pointer} {w : Nat}
    (h : out.id ≠ p.id) :
    readWord? p w (accumulatedState s out cv len flags m old c).mem = readWord? p w s.mem := by
  induction c with
  | zero => rfl
  | succ c ih =>
    simp only [accumulatedState, accumulate]
    rw [readWord?_splice_ne (show (outputPtr out c).id ≠ p.id from h)]
    exact ih

theorem read_accumulatedState_future (s : GlobalState) (out : Pointer)
    (cv : CV Words16) (len flags : Words16) (m : State Words16)
    (old : Nat → Vector (BitVec 16) 32) (hw : out.offset.toNat + 2048 ≤ 2^64)
    (num c : Nat) (hn : num ≤ c) (hc : c < 32) :
    readWord? (outputPtr out c) 512 (accumulatedState s out cv len flags m old num).mem =
      readWord? (outputPtr out c) 512 s.mem := by
  induction num with
  | zero => rfl
  | succ k ih =>
    have hk : k < 32 := by omega
    have ko := outputPtr_offset out hw k hk
    have co := outputPtr_offset out hw c hc
    simp only [accumulatedState, accumulate]
    rw [readWord?_splice_disjoint _ (Or.inl (by rw [ko, co]; omega))]
    exact ih (by omega)

/-- All intermediate memory premises follow from initial reads and separated allocations. -/
theorem InitialMemory.iteration (s : GlobalState) (out msg sched : Pointer)
    (cv : CV Words16) (len flags : Words16) (m : State Words16)
    (old : Nat → Vector (BitVec 16) 32) (h : InitialMemory s out msg sched m old)
    (c : Nat) (hc : c < 32) :
    IterationMemory (accumulatedState s out cv len flags m old c) out msg sched c m (old c) := by
  have fo : Fits s.mem (outputPtr out c) 512 := by
    obtain ⟨b, hb, hn⟩ := h.outputFits
    refine ⟨b, hb, ?_⟩
    rw [outputPtr_offset out h.outputWrap c hc]
    omega
  constructor
  · intro r i
    exact fits_accumulatedState _ _ _ _ _ _ _ _ (h.scheduleFits r i)
  · intro r i
    rw [read_accumulatedState_ne s out cv len flags m old c
      (show out.id ≠ (schedulePtr16 sched r i).id from h.scheduleSeparate)]
    exact h.scheduleRead r i
  · intro i
    exact fits_accumulatedState _ _ _ _ _ _ _ _ (h.messageFits i)
  · intro i
    rw [read_accumulatedState_ne s out cv len flags m old c
      (show out.id ≠ (messagePtr16 msg i).id from h.messageSeparate)]
    exact h.messageRead i
  · exact fits_accumulatedState _ _ _ _ _ _ _ _ fo
  · rw [read_accumulatedState_future s out cv len flags m old h.outputWrap c c (by omega) hc]
    exact h.outputRead c hc

/-- Completed counter slices contain their exact modular sums and cannot be overwritten later. -/
theorem InitialMemory.completed_reads (s : GlobalState) (out msg sched : Pointer)
    (cv : CV Words16) (len flags : Words16) (m : State Words16)
    (old : Nat → Vector (BitVec 16) 32) (h : InitialMemory s out msg sched m old)
    (num c : Nat) (hn : num ≤ 32) (hc : c < num) :
    readWord? (outputPtr out c) 512 (accumulatedState s out cv len flags m old num).mem =
      some (packBits (BatchOutput16.sums32 (old c) (delta cv len flags m c))) := by
  induction num with
  | zero => omega
  | succ k ih =>
    have hk : k < 32 := by omega
    have hc32 : c < 32 := by omega
    by_cases he : c = k
    · subst c
      have hm := h.iteration s out msg sched cv len flags m old k hk
      simp only [accumulatedState, accumulate]
      exact readWord?_splice_self _ hm.outputFits
    · have ko := outputPtr_offset out h.outputWrap k hk
      have co := outputPtr_offset out h.outputWrap c hc32
      simp only [accumulatedState, accumulate]
      rw [readWord?_splice_disjoint _ (Or.inr (by rw [ko, co]; omega))]
      exact ih (by omega) (by omega)

def outputSlice (a : Vector (BitVec 16) 1024) (c : Nat) : Vector (BitVec 16) 32 :=
  Vector.ofFn fun i => a[32*(c%32)+i.val]'(by have := i.isLt; omega)

private theorem packBits_as_packLanes {n w : Nat} (v : Vector (BitVec w) n) :
    packBits v = BitVec.packLanes v := by
  unfold packBits LLVM.Ty.flattenBV
  congr 1
  apply Vector.ext
  intro i hi
  simp only [Vector.getElem_ofFn]
  change ((v.map PoisonOr.value)[i]).toOption.getD 0 = v[i]
  rw [Vector.getElem_map]
  rfl

theorem InitialMemory.ofPacked (s : GlobalState) (out msg sched : Pointer)
    (m : State Words16) (a : Vector (BitVec 16) 1024)
    (hsi : ∀ r i, Fits s.mem (schedulePtr16 sched r i) 64)
    (hsv : ∀ r i, readWord? (schedulePtr16 sched r i) 64 s.mem = some (BitVec.ofNat 64 (schedule r i).val))
    (hmi : ∀ i, Fits s.mem (messagePtr16 msg i) 512)
    (hmv : ∀ i, readWord? (messagePtr16 msg i) 512 s.mem = some (packBits (m i)))
    (hf : Fits s.mem out 16384) (hw : out.offset.toNat + 2048 ≤ 2^64)
    (hr : readWord? out 16384 s.mem = some (packBits a))
    (hs : out.id ≠ sched.id) (hm : out.id ≠ msg.id) :
    InitialMemory s out msg sched m (outputSlice a) := by
  refine ⟨hsi, hsv, hmi, hmv, hf, hw, ?_, hs, hm⟩
  intro c hc
  have hoff := outputPtr_offset out hw c hc
  have hread := readWord?_extract (packBits a) hf hr
    (q := outputPtr out c) rfl hoff (show 512*c+512 ≤ 16384 by omega)
  rw [packBits_as_packLanes, show 512*c = 16*(32*c) by omega,
    BitVec.extractLsb'_packLanes_run a 32 (32*c) (by omega)] at hread
  simpa only [outputSlice, Nat.mod_eq_of_lt hc, packBits_as_packLanes] using hread

end AgaveLatticeHash.MLIR.BatchXofLoop16
