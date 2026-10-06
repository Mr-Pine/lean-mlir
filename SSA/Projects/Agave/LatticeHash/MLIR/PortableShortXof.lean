/- Released under Apache 2.0 license as described in the file LICENSE. -/
import SSA.Projects.Agave.LatticeHash.MLIR.PortableShortMemory

namespace AgaveLatticeHash.MLIR.PortableShort
open LeanMLIR SLLVM Firedancer AgaveBlake3Reference
set_option maxRecDepth 4096
attribute [local irreducible] agave_portable_compress_xof portableCompressionMemory
  compressXofWords

/-- A Lean-level sequence of actual extracted XOF calls. The counter and output
pointer advance by one 64-byte block. This is not extracted `Hasher` control flow. -/
inductive XofCalls (cvp msg out : Pointer) (len flags : BitVec 8) :
    Nat → GlobalState → GlobalState → Prop
  | nil (s) : XofCalls cvp msg out len flags 0 s s
  | step {n s mid t} : XofCalls cvp msg out len flags n s mid →
      StateT.run (agave_portable_compress_xof.denote (Ctxt.Valuation.ofHVector
        [.value flags, .value (BitVec.ofNat 64 n), .value len, .value msg,
         .value cvp, .value (blockPtr out n)]ₕ)) mid = .value ([]ₕ, t) →
      XofCalls cvp msg out len flags (n+1) s t

/-- All XOF blocks execute in the same memory image, preserving prior bytes.
The input descriptor is tied to the reference only at this intermediate lemma;
the short-message endpoint constructs it through actual in-place calls. -/
theorem xof_calls (m : Message) (hm : m.length ≤ 1024)
    (s : GlobalState) (cvp src out : Pointer) (hl : Layout cvp src out)
    (h : Inputs s cvp src out m (finalChunk m).cv) (n : Nat) (hn : n ≤ 32) :
    ∃ t : GlobalState,
      XofCalls cvp (blockPtr src (finalChunk m).blocksCompressed) out
        (BitVec.ofNat 8 (finalChunk m).bufLen) (rootFlags8 (finalChunk m).blocksCompressed) n s t ∧
      Inputs t cvp src out m (finalChunk m).cv ∧
      ∀ (counter : Fin n) (i : Fin 64),
        readWord? (out.withOffset (BitVec.ofNat 64 (64*counter.val+i.val))) 8 t.mem =
          some (rootOutput (finalChunk m) counter.val i) := by
  induction n with
  | zero => exact ⟨s, .nil s, h, fun counter => Fin.elim0 counter⟩
  | succ n ih =>
    obtain ⟨mid, hc, hi, hr⟩ := ih (by omega)
    let chunk := finalChunk m
    let op := blockPtr out n
    let msg := blockPtr src chunk.blocksCompressed
    let len := BitVec.ofNat 8 chunk.bufLen
    let flags := rootFlags8 chunk.blocksCompressed
    have hj : chunk.blocksCompressed < 16 := AgaveBatchControl.rootIndex_lt16 m.length hm
    have hlen : chunk.bufLen ≤ 64 := (AgaveBatchControl.root_size_bounds m.length).1
    have hext : len.zeroExtend 32 = BitVec.ofNat 32 chunk.bufLen :=
      BitVec.setWidth_ofNat_of_le_of_lt (by decide) (by omega)
    have hw : op.offset.toNat + 64 ≤ 2^64 := by
      rw [blockPtr_offset out hl.out_zero n (by omega)]
      omega
    have hfit : Fits mid.mem op 512 := blockPtr_fits (n := 32) hl.out_zero hi.out_fits n (by omega) (by omega)
    let words := compressXofWords chunk.cv chunk.buf (len.zeroExtend 32)
      (BitVec.ofNat 64 n) (flags.zeroExtend 32)
    let t : GlobalState := {mid with mem := portableCompressionMemory mid.mem op words}
    have hrun := portable_xof_reference_run mid op cvp msg chunk.cv chunk.buf
      (BitVec.ofNat 64 n) len flags hfit hi.cv_fits
      (blockPtr_fits (n := 16) hl.src_zero hi.src_fits chunk.blocksCompressed hj (by omega)) hw
      hi.cv_read (hi.src_read ⟨chunk.blocksCompressed, hj⟩)
    refine ⟨t, .step hc hrun, xof_inputs hl hi ⟨n, by omega⟩ words, ?_⟩
    intro counter i
    by_cases he : counter.val = n
    · have hread := portableCompressionMemory_read_byte mid.mem op words hfit hw i
      have hp : op.withOffset (BitVec.ofNat 64 i.val) =
          out.withOffset (BitVec.ofNat 64 (64*counter.val+i.val)) := by
        rw [he]
        exact offset_add out (64*n) i.val
      rw [hp] at hread
      change readWord? _ 8 (portableCompressionMemory mid.mem op words) = _
      rw [hread]
      simp only [words, hext, flags, rootFlags8_extend, rootOutput, rootWords, he, chunk]
    · have hk : counter.val < n := by omega
      have hoff := offsetInBits_withOffset_nat out (64*counter.val+i.val)
        (by rw [hl.out_zero]; change 0 + _ < _; omega)
      have ho := offsetInBits_withOffset_nat out (64*n)
        (by rw [hl.out_zero]; change 0 + _ < _; omega)
      change readWord? _ 8 (portableCompressionMemory mid.mem op words) = _
      rw [portableMemory_read_before mid.mem op _ words hw]
      · exact hr ⟨counter.val, hk⟩ i
      · change (out.withOffset _).offsetInBits + 8 ≤ (out.withOffset _).offsetInBits
        rw [hoff, ho]
        omega

theorem xof_calls_all_bytes (m : Message) (hm : m.length ≤ 1024)
    (s : GlobalState) (cvp src out : Pointer) (hl : Layout cvp src out)
    (h : Inputs s cvp src out m (finalChunk m).cv) :
    ∃ t : GlobalState,
      XofCalls cvp (blockPtr src (finalChunk m).blocksCompressed) out
        (BitVec.ofNat 8 (finalChunk m).bufLen) (rootFlags8 (finalChunk m).blocksCompressed) 32 s t ∧
      ∀ i : Fin 2048,
        readWord? (out.withOffset (BitVec.ofNat 64 i.val)) 8 t.mem =
          some (readerFill (finalChunk m) i) := by
  obtain ⟨t, hc, _, hr⟩ := xof_calls m hm s cvp src out hl h 32 (by omega)
  refine ⟨t, hc, ?_⟩
  intro i
  have he : 64*(i.val/64)+i.val%64=i.val := by omega
  simpa only [he, readerFill_eq, rootOutput] using
    hr ⟨i.val/64, by omega⟩ ⟨i.val%64, by omega⟩

end AgaveLatticeHash.MLIR.PortableShort
