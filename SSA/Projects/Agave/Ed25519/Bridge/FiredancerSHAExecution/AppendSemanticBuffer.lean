import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.AppendSemanticMemory

/-! Byte-copy and count-store observations, including a full 128-byte buffer
before compression (which is intentionally outside the stable pending bound). -/
namespace Agave.Ed25519.Bridge.FiredancerSHAExecution.Append.Semantic
open LeanMLIR.RIR Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.SHA512 Agave.Ed25519.SHA512.Spec
open Agave.Ed25519.Bridge.Challenge
open Agave.Ed25519.Verifier.Execution.Challenge
set_option maxRecDepth 100000
set_option maxHeartbeats 700000
set_option linter.unusedSimpArgs false

theorem writes_read (id : BlockId) (m n : MemoryState) (h : BlockWrites id m n)
    (p : Pointer) (width : Nat) (hne : id ≠ p.id) : n.readAt p width = m.readAt p width := by
  induction h with
  | refl => rfl
  | store _ dst v hp ih =>
    rw [MemoryState.readAt_storeAt_disjoint (range_disjoint_of_ne dst p _ width (by simpa [hp] using hne))]
    exact ih

theorem writes_bytes (id : BlockId) (m n : MemoryState) (h : BlockWrites id m n)
    (p : Pointer) (bytes : Nat) (hne : id ≠ p.id) : readBytes n p bytes = readBytes m p bytes := by
  unfold readBytes
  congr 1
  funext i
  exact writes_read id m n h _ 8 hne

theorem set_count_rep (m : MemoryState) (p : Pointer) (q : StreamSpec.Context)
    (hl : SmallRange m p 224) (hb : q.buffer.length < 128)
    (hbytes : readBytes m p q.buffer.length = q.buffer)
    (hc : m.readAt (p.add 128#64) 512 = q.chain)
    (hbits : m.readAt (p.add 216#64) 64 ++ m.readAt (p.add 208#64) 64 = q.bitCount) :
    MemRep (countMemory m p (BitVec.ofNat 64 q.buffer.length)) p q := by
  refine ⟨hl.storeAt _ _, hb, ?_, ?_, ?_, ?_⟩
  · exact MemoryState.readAt_storeAt_self (hl.fits_add (k := 200) (count := 8) (by decide)) _
  · rw [countMemory, bytes_store_after m p hl q.buffer.length 200 8 (by omega) (by decide)]
    exact hbytes
  · rw [countMemory, read_store_offsets m p hl 200 8 128 64 (by decide) (by decide) (Or.inr (by decide))]
    exact hc
  · rw [countMemory,
      read_store_offsets m p hl 200 8 216 8 (by decide) (by decide) (Or.inl (by decide)),
      read_store_offsets m p hl 200 8 208 8 (by decide) (by decide) (Or.inl (by decide))]
    exact hbits

def bufferCopy (m : MemoryState) (p data : Pointer) (old count : Nat) : MemoryState :=
  m.storeAt (p.add (BitVec.ofNat 64 old)) (m.readAt data (8 * count))

theorem bufferCopy_chain (m : MemoryState) (p data : Pointer) (old count : Nat)
    (hl : SmallRange m p 224) (hb : old + count ≤ 128) :
    (bufferCopy m p data old count).readAt (p.add 128#64) 512 = m.readAt (p.add 128#64) 512 :=
  read_store_offsets m p hl old count 128 64 (by omega) (by decide) (Or.inl hb) _

theorem bufferCopy_bits (m : MemoryState) (p data : Pointer) (old count : Nat)
    (hl : SmallRange m p 224) (hb : old + count ≤ 128) :
    (bufferCopy m p data old count).readAt (p.add 216#64) 64 ++
      (bufferCopy m p data old count).readAt (p.add 208#64) 64 =
      m.readAt (p.add 216#64) 64 ++ m.readAt (p.add 208#64) 64 := by
  rw [bufferCopy,
    read_store_offsets m p hl old count 216 8 (by omega) (by decide) (Or.inl (by omega)),
    read_store_offsets m p hl old count 208 8 (by omega) (by decide) (Or.inl (by omega))]

theorem bufferCopy_bytes (m : MemoryState) (p data : Pointer) (old count : Nat)
    (hl : SmallRange m p 224) (hi : SmallRange m data count) (hb : old + count ≤ 128) :
    readBytes (bufferCopy m p data old count) p (old + count) =
      readBytes m p old ++ readBytes m data count :=
  readBytes_copy_append m data p old count hi (smallRange_mono hl (by omega))

theorem short_rep (s : GlobalState) (p data : Pointer) (q : StreamSpec.Context)
    (used size : Word) (h : MemRep s.mem p q) (hu : used.toNat = q.buffer.length)
    (hi : SmallRange s.mem data size.toNat) (hb : q.buffer.length + size.toNat < 128) :
    MemRep (shortState s p data used size).mem p
      ⟨q.chain, q.buffer ++ readBytes s.mem data size.toNat, q.bitCount⟩ := by
  let chunk := readBytes s.mem data size.toNat
  let m := bufferCopy s.mem p data q.buffer.length size.toNat
  have hused : used = BitVec.ofNat 64 q.buffer.length := by rw [← hu]; simp
  have hc : used + size = BitVec.ofNat 64 (q.buffer ++ chunk).length := by
    rw [List.length_append, readBytes_length, ← hu, BitVec.ofNat_add]
    simp
  change MemRep (countMemory (copyMemory s.mem (p.add used) data size) p (used + size)) p _
  rw [hc, hused]
  apply set_count_rep m p ⟨q.chain, q.buffer ++ chunk, q.bitCount⟩ (h.live.storeAt _ _)
  · simpa only [List.length_append, chunk, readBytes_length] using hb
  · change readBytes m p (q.buffer ++ chunk).length = q.buffer ++ chunk
    rw [List.length_append, readBytes_length,
      bufferCopy_bytes s.mem p data q.buffer.length size.toNat h.live hi (by omega), h.buffer]
  · exact (bufferCopy_chain s.mem p data q.buffer.length size.toNat h.live (by omega)).trans h.chain
  · exact (bufferCopy_bits s.mem p data q.buffer.length size.toNat h.live (by omega)).trans h.bits

end Agave.Ed25519.Bridge.FiredancerSHAExecution.Append.Semantic
