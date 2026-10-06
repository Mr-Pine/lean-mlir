/- Released under Apache 2.0 license as described in the file LICENSE. -/
import SSA.Projects.Agave.LatticeHash.MLIR.CallerMemory
import SSA.Projects.Agave.LatticeHash.MLIR.PortableXofReference

/-! Constructive memory for a sequence of actual portable compression calls.
The input image contains only IV words, padded message bytes grouped as words,
and a zeroed 2048-byte output. It contains no precomputed compression result. -/
namespace AgaveLatticeHash.MLIR.PortableShort
open LeanMLIR SLLVM Firedancer
open AgaveBlake3Reference
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
attribute [local irreducible] portableCompressionMemory AgaveBlake3Reference.load32
  CompressionExit.outputMem

def block (m : Message) (j : Nat) : AgaveBlake3Reference.Block :=
  AgaveBatchControl.scalarBlock (AgaveConcrete.bytes m) m.length j

def sourceWords (m : Message) : Vector Word 256 :=
  Vector.ofFn fun i => load32 (block m (i.val / 16)) ⟨i.val % 16, by omega⟩

def image (base : GlobalState) (m : Message) : GlobalState :=
  let s := base.withGlobal "portable.short.cv" (packBits (Vector.ofFn iv))
  let s := s.withGlobal "portable.short.message" (packBits (sourceWords m))
  s.withGlobal "portable.short.output" (0#16384)

abbrev ptr := CallerMemory.ptr

def blockPtr (p : Pointer) (j : Nat) : Pointer :=
  p.withOffset (BitVec.ofNat 64 (64*j))

theorem offset_add (p : Pointer) (a b : Nat) :
    (p.withOffset (BitVec.ofNat 64 a)).withOffset (BitVec.ofNat 64 b) =
      p.withOffset (BitVec.ofNat 64 (a+b)) := by
  simp only [Pointer.withOffset, BitVec.add_assoc, BitVec.ofNat_add]

structure Layout (cvp src out : Pointer) : Prop where
  cv_zero : cvp.offset = 0
  src_zero : src.offset = 0
  out_zero : out.offset = 0
  cv_src : cvp.id ≠ src.id
  cv_out : cvp.id ≠ out.id
  src_out : src.id ≠ out.id

structure Inputs (s : GlobalState) (cvp src out : Pointer) (m : Message) (cv : CV) : Prop where
  cv_fits : Fits s.mem cvp 256
  src_fits : Fits s.mem src 8192
  out_fits : Fits s.mem out 16384
  cv_read : ∀ i : Fin 8,
    readWord? (cvp.withOffset (BitVec.ofNat 64 (4*i.val))) 32 s.mem = some (cv i)
  src_read : ∀ (j : Fin 16) (i : Fin 16),
    readWord? ((blockPtr src j.val).withOffset (BitVec.ofNat 64 (4*i.val))) 32 s.mem =
      some (load32 (block m j.val) i)

theorem read_packed_word {s : GlobalState} {p : Pointer} {name : String}
    {n : Nat} {v : Vector Word n} (h : HoldsGlobal s name p (packBits v))
    (hz : p.offset = 0) (i : Fin n) (hi : 4*i.val < 2^64) :
    readWord? (p.withOffset (BitVec.ofNat 64 (4*i.val))) 32 s.mem = some v[i] := by
  have hoff : (p.withOffset (BitVec.ofNat 64 (4*i.val))).offsetInBits =
      p.offsetInBits + i.val*32 := by
    rw [offsetInBits_withOffset_nat p _ (by simpa [hz] using hi)]
    omega
  have hr := readWord?_extract (packBits v) h.2.1 (readWord?_eq_some h.2.1 h.2.2)
    (q := p.withOffset (BitVec.ofNat 64 (4*i.val))) (w' := 32) rfl hoff (by omega)
  rwa [extract_packBits] at hr

theorem image_inputs (base : GlobalState) (hbase : base.WF) (m : Message) :
    (image base m).WF ∧ Layout (ptr base 0) (ptr base 1) (ptr base 2) ∧
      Inputs (image base m) (ptr base 0) (ptr base 1) (ptr base 2) m iv := by
  let s1 := base.withGlobal "portable.short.cv" (packBits (Vector.ofFn iv))
  let s2 := s1.withGlobal "portable.short.message" (packBits (sourceWords m))
  have hs1 : s1.WF := hbase.withGlobal _ _
  have hs2 : s2.WF := hs1.withGlobal _ _
  have hc : HoldsGlobal s1 "portable.short.cv" (ptr base 0) (packBits (Vector.ofFn iv)) :=
    holdsGlobal_withGlobal base _ _
  have hm : HoldsGlobal s2 "portable.short.message" (ptr base 1) (packBits (sourceWords m)) :=
    holdsGlobal_withGlobal s1 _ _
  have ho : HoldsGlobal (image base m) "portable.short.output" (ptr base 2) (0#16384) := by
    simpa only [s2, s1, image, GlobalState.withGlobal_nextFreeBlock, CallerMemory.ptr,
      Nat.add_assoc] using holdsGlobal_withGlobal s2 "portable.short.output" (0#16384)
  have hc := CallerMemory.holdsGlobal_withGlobal_preserved
    (name' := "portable.short.message") hs1 hc (packBits (sourceWords m)) (by decide)
  have hc := CallerMemory.holdsGlobal_withGlobal_preserved
    (name' := "portable.short.output") hs2 hc (0#16384) (by decide)
  have hm := CallerMemory.holdsGlobal_withGlobal_preserved
    (name' := "portable.short.output") hs2 hm (0#16384) (by decide)
  change HoldsGlobal (image base m) "portable.short.cv" (ptr base 0)
    (packBits (Vector.ofFn iv)) at hc
  change HoldsGlobal (image base m) "portable.short.message" (ptr base 1)
    (packBits (sourceWords m)) at hm
  refine ⟨hs2.withGlobal _ _, ?_, hc.2.1, hm.2.1, ho.2.1, ?_, ?_⟩
  · constructor <;> simp [CallerMemory.ptr, BlockId.mk.injEq]
  · intro i
    have hr := read_packed_word hc rfl i (by omega)
    change readWord? _ 32 _ = some ((Vector.ofFn iv)[i.val]) at hr
    simpa only [Vector.getElem_ofFn] using hr
  · intro j i
    have hr := read_packed_word hm rfl (⟨16*j.val+i.val, by omega⟩ : Fin 256) (by omega)
    change readWord? _ 32 _ = some ((sourceWords m)[16*j.val+i.val]'(by omega)) at hr
    have hd : (16*j.val+i.val)/16 = j.val := by omega
    have he : (16*j.val+i.val)%16 = i.val := by omega
    simpa only [blockPtr, offset_add, show 4*(16*j.val+i.val)=64*j.val+4*i.val by omega,
      sourceWords, Vector.getElem_ofFn, hd, he] using hr

theorem blockPtr_offset (p : Pointer) (hz : p.offset = 0) (j : Nat) (hj : j < 32) :
    (blockPtr p j).offset.toNat = 64*j := by
  change (p.offset + BitVec.ofNat 64 (64*j)).toNat = 64*j
  rw [hz]
  simp [BitVec.toNat_ofNat]
  omega

theorem blockPtr_fits {s : GlobalState} {p : Pointer} (hz : p.offset = 0)
    {n : Nat} (h : Fits s.mem p (512*n)) (j : Nat) (hj : j < n) (hn : n ≤ 32) :
    Fits s.mem (blockPtr p j) 512 := by
  obtain ⟨b, hb, hlen⟩ := h
  refine ⟨b, hb, ?_⟩
  have hoff := blockPtr_offset p hz j (by omega)
  simp only [Pointer.offsetInBits, hz] at hlen
  simp only [Pointer.offsetInBits, hoff]
  omega

/-- Later XOF blocks preserve every byte stored by earlier output calls. -/
theorem portableMemory_read_before (m : MemoryState) (out p : Pointer)
    (v : Blake3Compression.State Word) (hwrap : out.offset.toNat + 64 ≤ 2^64)
    (hp : p.offsetInBits + 8 ≤ out.offsetInBits) :
    readWord? p 8 (portableCompressionMemory m out v) = readWord? p 8 m := by
  rw [portableCompressionMemory_eq_outputMem]
  have aux (n : Nat) (hn : n ≤ 16) :
      readWord? p 8 (CompressionExit.outputMem out (fun i => #v[v i]) n m) =
        readWord? p 8 m := by
    induction n with
    | zero => simp only [CompressionExit.outputMem]
    | succ n ih =>
      simp only [CompressionExit.outputMem, packBits_singleton]
      rw [readWord?_splice_disjoint]
      · exact ih (by omega)
      · right
        rw [offsetInBits_withOffset_nat out (4*1*n) (by omega)]
        omega
  exact aux 16 (by omega)

theorem xof_inputs {s : GlobalState} {cvp src out : Pointer} {m : Message} {cv : CV}
    (hl : Layout cvp src out) (h : Inputs s cvp src out m cv)
    (counter : Fin 32) (words : Words) :
    Inputs ({s with mem := portableCompressionMemory s.mem (blockPtr out counter.val) words} : GlobalState)
      cvp src out m cv := by
  have hf (p : Pointer) (hp : out.id ≠ p.id) :
      (portableCompressionMemory s.mem (blockPtr out counter.val) words).live? p.id =
        s.mem.live? p.id := portableCompressionMemory_frame _ _ _ _ hp
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact fits_of_live?_eq (hf cvp hl.cv_out.symm) h.cv_fits
  · exact fits_of_live?_eq (hf src hl.src_out.symm) h.src_fits
  · have ho := CompressionExit.fits_outputMem
      (blockPtr out counter.val) (fun i => #v[words i]) 16 h.out_fits
    rw [← portableCompressionMemory_eq_outputMem] at ho
    exact ho
  · intro i
    rw [readWord?_of_live?_eq (hf (cvp.withOffset _) hl.cv_out.symm)]
    exact h.cv_read i
  · intro j i
    rw [readWord?_of_live?_eq (hf ((blockPtr src j.val).withOffset _) hl.src_out.symm)]
    exact h.src_read j i

end AgaveLatticeHash.MLIR.PortableShort
