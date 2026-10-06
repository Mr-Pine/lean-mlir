/- Released under Apache 2.0 license as described in the file LICENSE. -/
import SSA.Projects.Agave.LatticeHash.MLIR.BatchXofLoop

namespace AgaveLatticeHash.MLIR.BatchXofLoop
open LeanMLIR SLLVM Firedancer Blake3Compression
open InstCombine (LLVM)
open BatchReduction
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

/-- Initial reads of the scratch root block, schedule, and accumulator. -/
structure InitialMemory (s : GlobalState) (out msg sched : Pointer)
    (m : State Words8) (lo hi : Nat → Vector (BitVec 16) 16) : Prop where
  scheduleFits : ∀ r i, Fits s.mem (CompressionRound.schedulePtr sched r i) 64
  scheduleRead : ∀ r i, readWord? (CompressionRound.schedulePtr sched r i) 64 s.mem =
    some (BitVec.ofNat 64 (schedule r i).val)
  messageFits : ∀ i, Fits s.mem (CompressionRound.messagePtr8 msg i) 256
  messageRead : ∀ i, readWord? (CompressionRound.messagePtr8 msg i) 256 s.mem = some (packBits (m i))
  outputFits : Fits s.mem out 16384
  outputWrap : out.offset.toNat + 2048 ≤ 2^64
  lowerRead : ∀ c, c < 32 → readWord? (outputPtr out c) 256 s.mem = some (packBits (lo c))
  upperRead : ∀ c, c < 32 → readWord? (outputPtr (out.withOffset 32) c) 256 s.mem = some (packBits (hi c))
  scheduleSeparate : out.id ≠ sched.id
  messageSeparate : out.id ≠ msg.id

theorem outputPtr_offset (out : Pointer) (hw : out.offset.toNat + 2048 ≤ 2^64)
    (c : Nat) (hc : c < 32) :
    (outputPtr out c).offsetInBits = out.offsetInBits + 512*c := by
  rw [outputPtr, offsetInBits_withOffset_nat out (64*c) (by omega)]
  omega

theorem outputPtr_high_offset (out : Pointer) (hw : out.offset.toNat + 2048 ≤ 2^64)
    (c : Nat) (hc : c < 32) :
    (outputPtr (out.withOffset 32) c).offsetInBits = out.offsetInBits + 256 + 512*c := by
  have hh := offsetInBits_withOffset_nat out 32 (by omega)
  change (out.withOffset 32).offsetInBits = out.offsetInBits + 8*32 at hh
  have hn : (out.withOffset 32).offset.toNat = out.offset.toNat + 32 := by
    simp only [Pointer.offsetInBits] at hh
    omega
  rw [outputPtr, offsetInBits_withOffset_nat (out.withOffset 32) (64*c) (by rw [hn]; omega)]
  change (out.withOffset 32).offsetInBits + 8*(64*c) = _
  rw [hh]
  omega

theorem fits_accumulatedState (s : GlobalState) (out outHigh : Pointer)
    (cv : CV Words8) (len flags : Words8) (m : State Words8)
    (lo hi : Nat → Vector (BitVec 16) 16) (c : Nat) {p : Pointer} {w : Nat}
    (h : Fits s.mem p w) :
    Fits (accumulatedState s out outHigh cv len flags m lo hi c).mem p w := by
  induction c with
  | zero => exact h
  | succ c ih => exact fits_splice (fits_splice ih)

/-- All root-message and schedule bytes remain unchanged by the output writes. -/
theorem read_accumulatedState_ne (s : GlobalState) (out outHigh : Pointer)
    (cv : CV Words8) (len flags : Words8) (m : State Words8)
    (lo hi : Nat → Vector (BitVec 16) 16) (c : Nat) {p : Pointer} {w : Nat}
    (hl : out.id ≠ p.id) (hh : outHigh.id ≠ p.id) :
    readWord? p w (accumulatedState s out outHigh cv len flags m lo hi c).mem =
      readWord? p w s.mem := by
  induction c with
  | zero => rfl
  | succ c ih =>
    simp only [accumulatedState, accumulate]
    rw [readWord?_splice_ne (show (outputPtr outHigh c).id ≠ p.id from hh),
      readWord?_splice_ne (show (outputPtr out c).id ≠ p.id from hl)]
    exact ih

/-- A later output slice still contains its initial accumulator value. -/
theorem read_accumulatedState_future (s : GlobalState) (out : Pointer)
    (cv : CV Words8) (len flags : Words8) (m : State Words8)
    (lo hi : Nat → Vector (BitVec 16) 16)
    (hw : out.offset.toNat + 2048 ≤ 2^64) (num c : Nat)
    (hn : num ≤ c) (hc : c < 32) :
    readWord? (outputPtr out c) 256
        (accumulatedState s out (out.withOffset 32) cv len flags m lo hi num).mem =
      readWord? (outputPtr out c) 256 s.mem ∧
    readWord? (outputPtr (out.withOffset 32) c) 256
        (accumulatedState s out (out.withOffset 32) cv len flags m lo hi num).mem =
      readWord? (outputPtr (out.withOffset 32) c) 256 s.mem := by
  induction num with
  | zero => exact ⟨rfl, rfl⟩
  | succ k ih =>
    have hk : k < 32 := by omega
    obtain ⟨ihl, ihh⟩ := ih (by omega)
    have kl := outputPtr_offset out hw k hk
    have kh := outputPtr_high_offset out hw k hk
    have cl := outputPtr_offset out hw c hc
    have ch := outputPtr_high_offset out hw c hc
    constructor
    · simp only [accumulatedState, accumulate]
      rw [readWord?_splice_disjoint _ (Or.inl (by rw [kh, cl]; omega)),
        readWord?_splice_disjoint _ (Or.inl (by rw [kl, cl]; omega))]
      exact ihl
    · simp only [accumulatedState, accumulate]
      rw [readWord?_splice_disjoint _ (Or.inl (by rw [kh, ch]; omega)),
        readWord?_splice_disjoint _ (Or.inl (by rw [kl, ch]; omega))]
      exact ihh

/-- The loop's intermediate read obligations follow from initial memory and
separation of the output allocation from the two read-only allocations. -/
theorem InitialMemory.iteration (s : GlobalState) (out msg sched : Pointer)
    (cv : CV Words8) (len flags : Words8) (m : State Words8)
    (lo hi : Nat → Vector (BitVec 16) 16) (h : InitialMemory s out msg sched m lo hi)
    (c : Nat) (hc : c < 32) :
    IterationMemory (accumulatedState s out (out.withOffset 32) cv len flags m lo hi c)
      out (out.withOffset 32) msg sched c m (lo c) (hi c) := by
  have ol := outputPtr_offset out h.outputWrap c hc
  have oh := outputPtr_high_offset out h.outputWrap c hc
  have fl : Fits s.mem (outputPtr out c) 256 := by
    obtain ⟨b, hb, hn⟩ := h.outputFits
    refine ⟨b, hb, ?_⟩
    rw [ol]
    omega
  have fh : Fits s.mem (outputPtr (out.withOffset 32) c) 256 := by
    obtain ⟨b, hb, hn⟩ := h.outputFits
    refine ⟨b, hb, ?_⟩
    rw [oh]
    omega
  constructor
  · intro r i
    exact fits_accumulatedState _ _ _ _ _ _ _ _ _ _ (h.scheduleFits r i)
  · intro r i
    rw [read_accumulatedState_ne s out (out.withOffset 32) cv len flags m lo hi c
      (show out.id ≠ (CompressionRound.schedulePtr sched r i).id from h.scheduleSeparate)
      (show (out.withOffset 32).id ≠ (CompressionRound.schedulePtr sched r i).id from h.scheduleSeparate)]
    exact h.scheduleRead r i
  · intro i
    exact fits_accumulatedState _ _ _ _ _ _ _ _ _ _ (h.messageFits i)
  · intro i
    rw [read_accumulatedState_ne s out (out.withOffset 32) cv len flags m lo hi c
      (show out.id ≠ (CompressionRound.messagePtr8 msg i).id from h.messageSeparate)
      (show (out.withOffset 32).id ≠ (CompressionRound.messagePtr8 msg i).id from h.messageSeparate)]
    exact h.messageRead i
  · exact fits_accumulatedState _ _ _ _ _ _ _ _ _ _ fl
  · exact fits_accumulatedState _ _ _ _ _ _ _ _ _ _ fh
  · rw [(read_accumulatedState_future s out cv len flags m lo hi h.outputWrap c c (by omega) hc).1]
    exact h.lowerRead c hc
  · rw [(read_accumulatedState_future s out cv len flags m lo hi h.outputWrap c c (by omega) hc).2]
    exact h.upperRead c hc
  · left
    rw [ol, oh]
    omega

/-- A completed output slice reads back exactly its modular half-word sums;
later counters cannot overwrite it. -/
theorem InitialMemory.completed_reads (s : GlobalState) (out msg sched : Pointer)
    (cv : CV Words8) (len flags : Words8) (m : State Words8)
    (lo hi : Nat → Vector (BitVec 16) 16) (h : InitialMemory s out msg sched m lo hi)
    (num c : Nat) (hn : num ≤ 32) (hc : c < num) :
    readWord? (outputPtr out c) 256
        (accumulatedState s out (out.withOffset 32) cv len flags m lo hi num).mem =
      some (packBits (BatchOutput.sums16 (lo c) (lowerDelta cv len flags m c))) ∧
    readWord? (outputPtr (out.withOffset 32) c) 256
        (accumulatedState s out (out.withOffset 32) cv len flags m lo hi num).mem =
      some (packBits (BatchOutput.sums16 (hi c) (upperDelta cv len flags m c))) := by
  induction num with
  | zero => omega
  | succ k ih =>
    have hk : k < 32 := by omega
    have hc32 : c < 32 := by omega
    have kl := outputPtr_offset out h.outputWrap k hk
    have kh := outputPtr_high_offset out h.outputWrap k hk
    have cl := outputPtr_offset out h.outputWrap c hc32
    have ch := outputPtr_high_offset out h.outputWrap c hc32
    by_cases he : c = k
    · subst c
      have hm := h.iteration s out msg sched cv len flags m lo hi k hk
      constructor
      · simp only [accumulatedState, accumulate]
        rw [readWord?_splice_disjoint _ (Or.inr (by rw [kl, kh]; omega))]
        exact readWord?_splice_self _ hm.lowerFits
      · simp only [accumulatedState, accumulate]
        exact readWord?_splice_self _ (fits_splice hm.upperFits)
    · obtain ⟨ihl, ihh⟩ := ih (by omega) (by omega)
      constructor
      · simp only [accumulatedState, accumulate]
        rw [readWord?_splice_disjoint _ (Or.inr (by rw [kh, cl]; omega)),
          readWord?_splice_disjoint _ (Or.inr (by rw [kl, cl]; omega))]
        exact ihl
      · simp only [accumulatedState, accumulate]
        rw [readWord?_splice_disjoint _ (Or.inr (by rw [kh, ch]; omega)),
          readWord?_splice_disjoint _ (Or.inr (by rw [kl, ch]; omega))]
        exact ihh

/-- The two accumulator halves belonging to an output counter. -/
def lowerSlice (a : Vector (BitVec 16) 1024) (c : Nat) : Vector (BitVec 16) 16 :=
  Vector.ofFn fun i => a[32*(c%32)+i.val]'(by have := i.isLt; omega)
def upperSlice (a : Vector (BitVec 16) 1024) (c : Nat) : Vector (BitVec 16) 16 :=
  Vector.ofFn fun i => a[32*(c%32)+16+i.val]'(by have := i.isLt; omega)

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

/-- One packed accumulator read supplies all initial output-slice reads. -/
theorem InitialMemory.ofPacked (s : GlobalState) (out msg sched : Pointer)
    (m : State Words8) (a : Vector (BitVec 16) 1024)
    (hsi : ∀ r i, Fits s.mem (CompressionRound.schedulePtr sched r i) 64)
    (hsv : ∀ r i, readWord? (CompressionRound.schedulePtr sched r i) 64 s.mem =
      some (BitVec.ofNat 64 (schedule r i).val))
    (hmi : ∀ i, Fits s.mem (CompressionRound.messagePtr8 msg i) 256)
    (hmv : ∀ i, readWord? (CompressionRound.messagePtr8 msg i) 256 s.mem = some (packBits (m i)))
    (hf : Fits s.mem out 16384) (hw : out.offset.toNat + 2048 ≤ 2^64)
    (hr : readWord? out 16384 s.mem = some (packBits a))
    (hs : out.id ≠ sched.id) (hm : out.id ≠ msg.id) :
    InitialMemory s out msg sched m (lowerSlice a) (upperSlice a) := by
  refine ⟨hsi, hsv, hmi, hmv, hf, hw, ?_, ?_, hs, hm⟩
  · intro c hc
    have hoff := outputPtr_offset out hw c hc
    have hread := readWord?_extract (packBits a) hf hr
      (q := outputPtr out c) rfl hoff (show 512*c+256 ≤ 16384 by omega)
    rw [packBits_as_packLanes, show 512*c = 16*(32*c) by omega,
      BitVec.extractLsb'_packLanes_run a 16 (32*c) (by omega)] at hread
    simpa only [lowerSlice, Nat.mod_eq_of_lt hc, packBits_as_packLanes] using hread
  · intro c hc
    have hoff : (outputPtr (out.withOffset 32) c).offsetInBits =
        out.offsetInBits + (512*c+256) := by
      rw [outputPtr_high_offset out hw c hc]
      omega
    have hread := readWord?_extract (packBits a) hf hr
      (q := outputPtr (out.withOffset 32) c) rfl hoff
      (show 512*c+256+256 ≤ 16384 by omega)
    rw [packBits_as_packLanes, show 512*c+256 = 16*(32*c+16) by omega,
      BitVec.extractLsb'_packLanes_run a 16 (32*c+16) (by omega)] at hread
    simpa only [upperSlice, Nat.mod_eq_of_lt hc, packBits_as_packLanes] using hread

/-- Complete root-output execution from initial byte-backed memory alone. -/
theorem xof32_run_initial (B : agave_batch_8.cfgCtx.Valuation)
    (cv : CV Words8) (len flags : Words8) (out msg sched : Pointer)
    (hInit : InitEnv B) (hOut : OutputEnv B out) (s : GlobalState) (m : State Words8)
    (lo hi : Nat → Vector (BitVec 16) 16)
    (hRound : CompressionRound.RoundEnv8
      (sourceVal B (extras cv len flags (out.withOffset 32) 0)) msg sched)
    (hMem : InitialMemory s out msg sched m lo hi) :
    StateT.run (agave_batch_8.blocks.run B (rootTarget cv len flags (out.withOffset 32) 0)) s =
      .value (.nil, accumulatedState s out (out.withOffset 32) cv len flags m lo hi 32) := by
  exact xof32_run_fixedEnv B cv len flags out (out.withOffset 32) msg sched hInit hOut s m lo hi
    hRound (fun c hc => hMem.iteration s out msg sched cv len flags m lo hi c hc)

end AgaveLatticeHash.MLIR.BatchXofLoop
