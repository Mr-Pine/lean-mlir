import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.AppendSemanticBuffer

/-! Observation of the arbitrary direct-block path and its trailing copy. -/
namespace Agave.Ed25519.Bridge.FiredancerSHAExecution.Append.Semantic
open LeanMLIR.RIR Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.SHA512 Agave.Ed25519.SHA512.Spec
open Agave.Ed25519.Bridge.Challenge
open Agave.Ed25519.Verifier.Execution.Challenge
set_option maxRecDepth 100000
set_option maxHeartbeats 700000
set_option linter.unusedSimpArgs false

theorem aligned_nat (size : Word) :
    (size &&& 18446744073709551488#64).toNat = 128 * (size.toNat / 128) := by
  have hp := aligned_plus_remainder size
  have hr : (size &&& 127#64).toNat = size.toNat % 128 := by simpa using append_remainder size
  omega

theorem tail_rep (s : GlobalState) (p data : Pointer) (q : StreamSpec.Context) (size : Word)
    (h : MemRep s.mem p q) (hbuf : q.buffer = []) (hi : SmallRange s.mem data size.toNat) :
    MemRep (tailState s p data size).mem p
      ⟨q.chain, StreamSpec.pending (readBytes s.mem data size.toNat), q.bitCount⟩ := by
  let chunk := readBytes s.mem data size.toNat
  let rem := size &&& 127#64
  let off := size &&& 18446744073709551488#64
  have hlen : (StreamSpec.pending chunk).length = rem.toNat := by
    rw [StreamSpec.pending_length, readBytes_length]
    exact (show rem.toNat = size.toNat % 128 by simpa [rem] using append_remainder size).symm
  have hrb : rem.toNat < 128 := by simpa [rem] using append_remainder_bound size
  have hoff : off.toNat + rem.toNat = size.toNat := aligned_plus_remainder size
  have hoff_le : off.toNat ≤ size.toNat := by omega
  have hpending : StreamSpec.pending chunk = readBytes s.mem (data.add off) rem.toNat := by
    unfold StreamSpec.pending
    rw [readBytes_length, ← aligned_nat size, readBytes_drop s.mem data size.toNat off.toNat hoff_le]
    rw [show size.toNat - off.toNat = rem.toNat by omega]
    simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  unfold tailState
  split
  · rename_i hz
    have hr0 : rem.toNat = 0 := by rw [show rem = 0#64 from hz]; rfl
    have hp0 : StreamSpec.pending chunk = [] := List.length_eq_zero_iff.mp (hlen.trans hr0)
    change MemRep s.mem p ⟨q.chain, StreamSpec.pending chunk, q.bitCount⟩
    simpa only [hp0, ← hbuf] using h
  · let m := bufferCopy s.mem p (data.add off) 0 rem.toNat
    have hisrc : SmallRange s.mem (data.add off) rem.toNat := by
      simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using
        smallRange_add hi (le_of_eq hoff)
    have hword : rem = BitVec.ofNat 64 (StreamSpec.pending chunk).length := by rw [hlen]; simp
    change MemRep (countMemory (copyMemory s.mem p (data.add off) rem) p rem) p _
    rw [hword]
    have hm : copyMemory s.mem p (data.add off) (BitVec.ofNat 64 (StreamSpec.pending chunk).length) = m := by
      rw [hlen]
      have hnat : (BitVec.ofNat 64 rem.toNat).toNat = rem.toNat := Nat.mod_eq_of_lt rem.isLt
      simp only [m, bufferCopy, copyMemory, Pointer.add_zero]
      rw [hnat]
    rw [hm]
    apply set_count_rep m p ⟨q.chain, StreamSpec.pending chunk, q.bitCount⟩
      (h.live.storeAt _ _) (StreamSpec.pending_bound chunk)
    · rw [hlen, ← Nat.zero_add rem.toNat, bufferCopy_bytes s.mem p (data.add off) 0 rem.toNat
        h.live hisrc (by omega)]
      simpa [readBytes] using hpending.symm
    · exact (bufferCopy_chain s.mem p (data.add off) 0 rem.toNat h.live (by omega)).trans h.chain
    · exact (bufferCopy_bits s.mem p (data.add off) 0 rem.toNat h.live (by omega)).trans h.bits

theorem direct_rep (s : GlobalState) (p data : Pointer) (q : StreamSpec.Context) (size : Word)
    (h : MemRep s.mem p q) (hbuf : q.buffer = []) (hi : SmallRange s.mem data size.toNat)
    (hne : p.id ≠ data.id) :
    MemRep (directState s p data size).mem p
      ⟨Spec.run q.chain (StreamSpec.complete (readBytes s.mem data size.toNat)),
       StreamSpec.pending (readBytes s.mem data size.toNat), q.bitCount⟩ := by
  let chunk := readBytes s.mem data size.toNat
  unfold directState
  split
  · rename_i hshort
    have hc : StreamSpec.complete chunk = [] := by
      simp [StreamSpec.complete, chunk, show size.toNat / 128 = 0 from Nat.div_eq_of_lt hshort]
    change MemRep (tailState s p data size).mem p
      ⟨Spec.run q.chain (StreamSpec.complete chunk), StreamSpec.pending chunk, q.bitCount⟩
    simpa only [hc, Spec.run_empty] using tail_rep s p data q size h hbuf hi
  · let t := compressionState s (p.add 128#64) data (size >>> (7 : Nat)).toNat
    have hb : 128 * (size >>> (7 : Nat)).toNat ≤ size.toNat := by
      simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
      omega
    have hc : readBytes s.mem data (128 * (size >>> (7 : Nat)).toNat) = StreamSpec.complete chunk := by
      unfold StreamSpec.complete
      rw [readBytes_length, readBytes_take s.mem data size.toNat (128 * (size.toNat / 128)) (by omega)]
      simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    have hrep : MemRep t.mem p ⟨Spec.run q.chain (StreamSpec.complete chunk), [], q.bitCount⟩ := by
      have hr := chain_rep s.mem p q h
        (Spec.run (s.mem.readAt (p.add 128#64) 512) (readBytes s.mem data (128 * (size >>> (7 : Nat)).toNat)))
      simpa only [t, compressionState, h.chain, hc, hbuf] using hr
    have hinput : readBytes t.mem data size.toNat = chunk :=
      writes_bytes p.id s.mem t.mem (compression_writes s p data (size >>> (7 : Nat)).toNat) data size.toNat hne
    have ht := tail_rep t p data _ size hrep rfl (hi.storeAt _ _)
    change MemRep (tailState t p data size).mem p
      ⟨Spec.run q.chain (StreamSpec.complete chunk), StreamSpec.pending chunk, q.bitCount⟩
    simpa only [hinput] using ht

end Agave.Ed25519.Bridge.FiredancerSHAExecution.Append.Semantic
