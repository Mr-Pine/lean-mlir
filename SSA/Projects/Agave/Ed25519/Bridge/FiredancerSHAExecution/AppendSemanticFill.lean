import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.AppendSemanticDirect

/-! The buffered-prefix fill is compressed exactly once. The newly empty
buffer then hands the untouched input suffix to the direct-block path. -/
namespace Agave.Ed25519.Bridge.FiredancerSHAExecution.Append.Semantic
open LeanMLIR.RIR Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.SHA512 Agave.Ed25519.SHA512.Spec
open Agave.Ed25519.Bridge.Challenge
open Agave.Ed25519.Verifier.Execution.Challenge
set_option maxRecDepth 100000
set_option maxHeartbeats 700000
set_option linter.unusedSimpArgs false

def filledResult (s : GlobalState) (p data : Pointer) (used : Word) : GlobalState :=
  resetState (compressionState (fillState s p data used) (p.add 128#64) p 1) p

theorem filled_writes (s : GlobalState) (p data : Pointer) (used : Word) :
    BlockWrites p.id s.mem (filledResult s p data used).mem :=
  ((fill_writes s p data used).trans (compression_writes (fillState s p data used) p p 1)).trans
    (reset_writes (compressionState (fillState s p data used) (p.add 128#64) p 1) p)

theorem filled_rep (s : GlobalState) (p data : Pointer) (q : StreamSpec.Context)
    (used size : Word) (h : MemRep s.mem p q) (hu : used.toNat = q.buffer.length)
    (hi : SmallRange s.mem data size.toNat) (hfull : 128 - q.buffer.length ≤ size.toNat) :
    MemRep (filledResult s p data used).mem p
      ⟨Spec.compressBlockBytes q.chain
          (StreamSpec.filledBlock q.buffer (readBytes s.mem data size.toNat)),
       [], q.bitCount⟩ := by
  let chunk := readBytes s.mem data size.toNat
  let block := StreamSpec.filledBlock q.buffer chunk
  let n := 128 - q.buffer.length
  let m := bufferCopy s.mem p data q.buffer.length n
  have hused : used = BitVec.ofNat 64 q.buffer.length := by rw [← hu]; simp
  have hn : (128#64 - used).toNat = n := by
    rw [BitVec.toNat_sub_of_le (by change used.toNat ≤ 128; have := h.bound; omega), hu]
    rfl
  have hm : (fillState s p data used).mem = m := by
    simp only [fillState, copyMemory, hused, m, bufferCopy]
    rw [hn]
  have hmLive : SmallRange m p 224 := h.live.storeAt _ _
  have hchain : m.readAt (p.add 128#64) 512 = q.chain :=
    (bufferCopy_chain s.mem p data q.buffer.length n h.live (by have := h.bound; dsimp [n]; omega)).trans h.chain
  have hbits : m.readAt (p.add 216#64) 64 ++ m.readAt (p.add 208#64) 64 = q.bitCount :=
    (bufferCopy_bits s.mem p data q.buffer.length n h.live (by have := h.bound; dsimp [n]; omega)).trans h.bits
  have hblock : readBytes m p 128 = block := by
    have hb : q.buffer.length + n = 128 := by have := h.bound; dsimp [n]; omega
    rw [← hb, bufferCopy_bytes s.mem p data q.buffer.length n h.live
      (smallRange_mono hi hfull) (by omega), h.buffer]
    unfold block StreamSpec.filledBlock
    rw [readBytes_take s.mem data size.toNat (128 - q.buffer.length) hfull]
  have hblocklen : block.length = 128 :=
    StreamSpec.filledBlock_length q.buffer chunk h.bound (by simpa [chunk] using hfull)
  have hash : Spec.run (m.readAt (p.add 128#64) 512) (readBytes m p (128 * 1)) =
      Spec.compressBlockBytes q.chain block := by
    rw [hchain, show 128 * 1 = 128 by decide, hblock, Spec.run_one_block _ _ hblocklen]
  let chain := Spec.compressBlockBytes q.chain block
  let compressed := m.storeAt (p.add 128#64) chain
  have hcompLive : SmallRange compressed p 224 := hmLive.storeAt _ _
  change MemRep (countMemory
    ((fillState s p data used).mem.storeAt (p.add 128#64)
      (Spec.run ((fillState s p data used).mem.readAt (p.add 128#64) 512)
        (readBytes (fillState s p data used).mem p (128 * 1)))) p 0#64) p _
  rw [hm, hash]
  apply set_count_rep compressed p ⟨chain, [], q.bitCount⟩ hcompLive (by simp)
  · simp [readBytes]
  · exact MemoryState.readAt_storeAt_self (hmLive.fits_add (k := 128) (count := 64) (by decide)) chain
  · change compressed.readAt (p.add 216#64) 64 ++ compressed.readAt (p.add 208#64) 64 = q.bitCount
    dsimp only [compressed]
    rw [read_store_offsets m p hmLive 128 64 216 8 (by decide) (by decide) (Or.inl (by decide)),
      read_store_offsets m p hmLive 128 64 208 8 (by decide) (by decide) (Or.inl (by decide))]
    exact hbits

theorem filled_suffix (s : GlobalState) (p data : Pointer) (used size : Word)
    (hne : p.id ≠ data.id)
    (hlong : (128#64 - used).toNat ≤ size.toNat) :
    readBytes (filledResult s p data used).mem (data.add (128#64 - used))
      (size - (128#64 - used)).toNat =
      (readBytes s.mem data size.toNat).drop (128#64 - used).toNat := by
  rw [writes_bytes p.id s.mem _ (filled_writes s p data used)
      (data.add (128#64 - used)) (size - (128#64 - used)).toNat hne,
    BitVec.toNat_sub_of_le (by exact hlong), readBytes_drop _ _ _ _ hlong]
  simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem filled_input_live (s : GlobalState) (p data : Pointer) (used size : Word)
    (hi : SmallRange s.mem data size.toNat) (hlong : (128#64 - used).toNat ≤ size.toNat) :
    SmallRange (filledResult s p data used).mem (data.add (128#64 - used))
      (size - (128#64 - used)).toNat := by
  have hs : (size - (128#64 - used)).toNat = size.toNat - (128#64 - used).toNat :=
    BitVec.toNat_sub_of_le (by exact hlong)
  have hr := smallRange_add ((filled_writes s p data used).live hi)
    (k := (128#64 - used).toNat) (count := (size - (128#64 - used)).toNat) (by omega)
  simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using hr

end Agave.Ed25519.Bridge.FiredancerSHAExecution.Append.Semantic
