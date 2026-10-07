import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.AppendLinked
import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.StreamSpecMachine
import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.StreamSpecAppend

/-! Memory observations for the append refinement. All fields are the actual
context bytes; no hash relation or machine execution is part of the relation. -/
namespace Agave.Ed25519.Bridge.FiredancerSHAExecution.Append.Semantic
open LeanMLIR.RIR Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.SHA512 Agave.Ed25519.SHA512.Spec
open Agave.Ed25519.Bridge.Challenge
open Agave.Ed25519.Verifier.Execution.Challenge
set_option maxRecDepth 100000
set_option maxHeartbeats 700000
set_option linter.unusedSimpArgs false

private theorem state_ext (x y : State)
    (ha : x.a = y.a) (hb : x.b = y.b) (hc : x.c = y.c) (hd : x.d = y.d)
    (he : x.e = y.e) (hf : x.f = y.f) (hg : x.g = y.g) (hh : x.h = y.h) : x = y := by
  cases x; cases y; simp_all

theorem readState_unpack (m : MemoryState) (p : Pointer) (hl : SmallRange m p 224) :
    readState m p = unpack (m.readAt (p.add 128#64) 512) := by
  have hc : SmallRange m (p.add 128#64) 64 := smallRange_add hl (by decide)
  have h := Core.chainMemory_of_packed m (p.add 128#64) hc
    (unpack (m.readAt (p.add 128#64) 512)) (by rw [pack_unpack])
  cases h with
  | mk ha hb hc hd he hf hg hh =>
    apply state_ext
    · exact ha
    · simpa [readState, Pointer.add_add] using hb
    · simpa [readState, Pointer.add_add] using hc
    · simpa [readState, Pointer.add_add] using hd
    · simpa [readState, Pointer.add_add] using he
    · simpa [readState, Pointer.add_add] using hf
    · simpa [readState, Pointer.add_add] using hg
    · simpa [readState, Pointer.add_add] using hh

theorem packed_readState (m : MemoryState) (p : Pointer) (hl : SmallRange m p 224) :
    pack (readState m p) = m.readAt (p.add 128#64) 512 := by
  rw [readState_unpack m p hl, pack_unpack]

structure MemRep (m : MemoryState) (p : Pointer) (q : StreamSpec.Context) : Prop where
  live : SmallRange m p 224
  bound : q.buffer.length < 128
  count : m.readAt (p.add 200#64) 64 = BitVec.ofNat 64 q.buffer.length
  buffer : readBytes m p q.buffer.length = q.buffer
  chain : m.readAt (p.add 128#64) 512 = q.chain
  bits : m.readAt (p.add 216#64) 64 ++ m.readAt (p.add 208#64) 64 = q.bitCount

variable {m : MemoryState} {p : Pointer} {q : StreamSpec.Context}

theorem MemRep.used (h : MemRep m p q) : (m.readAt (p.add 200#64) 64).toNat = q.buffer.length := by
  rw [h.count, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := h.bound; omega)]

theorem MemRep.observe (h : MemRep m p q) : StreamSpec.observe m p = q := by
  cases q with
  | mk chain buffer bits =>
    unfold StreamSpec.observe
    congr 1
    · exact (packed_readState m p h.live).trans h.chain
    · rw [h.used]
      exact h.buffer
    · exact h.bits

theorem of_context (m : MemoryState) (p : Pointer) (completed pending : Bytes)
    (h : ContextRepresents m p completed pending) :
    MemRep m p ⟨Spec.run initialWords completed, pending,
      BitVec.ofNat 128 (8 * (completed.length + pending.length))⟩ := by
  refine ⟨h.live, h.pendingBound, h.pendingCount, h.pendingBytes, ?_, h.bitCount⟩
  rw [← packed_readState m p h.live, h.chaining, pack_unpack]

theorem read_store_offsets (m : MemoryState) (p : Pointer) (hl : SmallRange m p 224)
    (i ni j nj : Nat) (hi : i + ni ≤ 224) (hj : j + nj ≤ 224)
    (hd : i + ni ≤ j ∨ j + nj ≤ i) (v : BitVec (8 * ni)) :
    (m.storeAt (p.add (BitVec.ofNat 64 i)) v).readAt (p.add (BitVec.ofNat 64 j)) (8 * nj) =
      m.readAt (p.add (BitVec.ofNat 64 j)) (8 * nj) :=
  MemoryState.readAt_storeAt_disjoint (smallRange_disjoint_offsets hl hi hj hd) v

theorem bytes_store_after (m : MemoryState) (p : Pointer) (hl : SmallRange m p 224)
    (bytes i count : Nat) (hb : bytes ≤ i) (hi : i + count ≤ 224)
    (v : BitVec (8 * count)) :
    readBytes (m.storeAt (p.add (BitVec.ofNat 64 i)) v) p bytes = readBytes m p bytes := by
  apply readBytes_storeAt_disjoint _ _ _ _ _ (smallRange_mono hl (by omega))
  simpa using smallRange_disjoint_offsets hl (i := i) (countI := count)
    (j := 0) (countJ := bytes) hi (by omega) (Or.inr (by omega))

/-- The two counter stores preserve every earlier context field. -/
theorem start_rep (s : GlobalState) (p : Pointer) (q : StreamSpec.Context) (size : Word)
    (h : MemRep s.mem p q) :
    MemRep (startState s p size).mem p
      ⟨q.chain, q.buffer, q.bitCount + BitVec.ofNat 128 (8 * size.toNat)⟩ := by
  let lo := s.mem.readAt (p.add 208#64) 64
  let hi := s.mem.readAt (p.add 216#64) 64
  let a := appendLow lo size
  let b := appendHigh hi lo size
  let m := s.mem.storeAt (p.add 208#64) a
  have hm : SmallRange m p 224 := h.live.storeAt _ _
  have hlo : (m.storeAt (p.add 216#64) b).readAt (p.add 208#64) 64 = a := by
    rw [read_store_offsets m p hm 216 8 208 8 (by decide) (by decide) (Or.inr (by decide)) b]
    exact MemoryState.readAt_storeAt_self (h.live.fits_add (k := 208) (count := 8) (by decide)) a
  have hhi : (m.storeAt (p.add 216#64) b).readAt (p.add 216#64) 64 = b :=
    MemoryState.readAt_storeAt_self (hm.fits_add (k := 216) (count := 8) (by decide)) b
  change MemRep (m.storeAt (p.add 216#64) b) p _
  refine ⟨hm.storeAt _ _, h.bound, ?_, ?_, ?_, ?_⟩
  · rw [read_store_offsets m p hm 216 8 200 8 (by decide) (by decide) (Or.inr (by decide)) b,
      read_store_offsets s.mem p h.live 208 8 200 8 (by decide) (by decide) (Or.inr (by decide)) a]
    exact h.count
  · rw [bytes_store_after m p hm q.buffer.length 216 8 (by have := h.bound; omega) (by decide) b,
      bytes_store_after s.mem p h.live q.buffer.length 208 8 (by have := h.bound; omega) (by decide) a]
    exact h.buffer
  · rw [read_store_offsets m p hm 216 8 128 64 (by decide) (by decide) (Or.inr (by decide)) b,
      read_store_offsets s.mem p h.live 208 8 128 64 (by decide) (by decide) (Or.inr (by decide)) a]
    exact h.chain
  · change _ = q.bitCount + BitVec.ofNat 128 (8 * size.toNat)
    rw [hhi, hlo]
    exact (append_counter hi lo size).trans (by rw [h.bits, StreamSpec.machine_chunk_bits])

/-- A native chaining-state store preserves the pending bytes, pending count,
and full bit count. -/
theorem chain_rep (m : MemoryState) (p : Pointer) (q : StreamSpec.Context)
    (h : MemRep m p q) (chain : BitVec 512) :
    MemRep (m.storeAt (p.add 128#64) chain) p ⟨chain, q.buffer, q.bitCount⟩ := by
  refine ⟨h.live.storeAt _ _, h.bound, ?_, ?_, ?_, ?_⟩
  · rw [read_store_offsets m p h.live 128 64 200 8 (by decide) (by decide) (Or.inl (by decide)) chain]
    exact h.count
  · rw [bytes_store_after m p h.live q.buffer.length 128 64 (by have := h.bound; omega) (by decide) chain]
    exact h.buffer
  · exact MemoryState.readAt_storeAt_self (h.live.fits_add (k := 128) (count := 64) (by decide)) chain
  · rw [read_store_offsets m p h.live 128 64 216 8 (by decide) (by decide) (Or.inl (by decide)) chain,
      read_store_offsets m p h.live 128 64 208 8 (by decide) (by decide) (Or.inl (by decide)) chain]
    exact h.bits

end Agave.Ed25519.Bridge.FiredancerSHAExecution.Append.Semantic
