import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionBulkOddEntry
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionBulkStart

namespace Agave.Ed25519.SHA512.Execution.Avx2
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.Verifier.Execution.Challenge

set_option maxRecDepth 100000
set_option maxHeartbeats 1500000

theorem bulk_store_overwrite (mem : MemoryState) (p : Pointer) (x y : BitVec w) :
    (mem.storeAt p x).storeAt p y = mem.storeAt p y := by
  unfold MemoryState.storeAt
  cases hp : mem[p.id]? with
  | none => simp only [hp]
  | some b =>
    simp only [hp, MemoryState.getElem?_eq, Std.ExtHashMap.getElem?_insert_self]
    simp only [Memory.spliceBits_spliceBits_self]
    congr 1
    apply Std.ExtHashMap.ext_getElem?
    intro q
    simp only [Std.ExtHashMap.getElem?_insert]
    split <;> simp_all

theorem bulk_readBytes_store_disjoint (mem : MemoryState) (p q : Pointer)
    (x : BitVec w) (n : Nat) (hq : SmallRange mem q n)
    (hdis : (Range.of p w).Disjoint (Range.of q (8*n))) :
    readBytes (mem.storeAt p x) q n = readBytes mem q n := by
  rw [readBytes_eq_bytesOf _ _ _ (hq.storeAt p x), readBytes_eq_bytesOf _ _ _ hq]
  congr 1
  apply MemoryState.readAt_storeAt_disjoint
  simpa only [Nat.mul_comm] using hdis

theorem ScratchFrame.readBytes_ne {scratch : Pointer} {before after : GlobalState}
    (h : ScratchFrame scratch before after) (p : Pointer) (n : Nat)
    (hs : scratch.id ≠ p.id) : readBytes after.mem p n = readBytes before.mem p n := by
  unfold readBytes
  congr 1
  funext i
  exact h.read _ _ (Range.disjoint_of_id_ne (by simpa using hs))

theorem PairConstants.store_ne {mem : MemoryState} {k p : Pointer}
    (h : PairConstants mem k) (x : BitVec w) (hp : p.id ≠ k.id) :
    PairConstants (mem.storeAt p x) k := by
  refine ⟨h.live.storeAt p x, ?_⟩
  intro r hr
  exact (bulk_read_store_ne mem p _ x _ (by simpa using hp)).trans (h.pairs r hr)

theorem PairConstants.scratchFrame {before after : GlobalState} {scratch k : Pointer}
    (h : PairConstants before.mem k) (hf : ScratchFrame scratch before after)
    (hk : scratch.id ≠ k.id) : PairConstants after.mem k := by
  refine ⟨hf.live h.live, ?_⟩
  intro r hr
  exact (hf.read _ _ (Range.disjoint_of_id_ne (by simpa using hk))).trans (h.pairs r hr)

theorem bulk_range_disjoint_add_right {mem : MemoryState} {p q : Pointer}
    {width bytes off count : Nat} (hq : SmallRange mem q bytes)
    (hbound : off + count ≤ bytes)
    (hd : (Range.of p width).Disjoint (Range.of q (8*bytes))) :
    (Range.of p width).Disjoint
      (Range.of (q.add (BitVec.ofNat 64 off)) (8*count)) := by
  have hoff := Pointer.offsetInBits_add (hq.no_wrap (k := off) (by omega))
  have hsmall : off < 2^64 := by have := hq.offset_lt; norm_num at *; omega
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsmall] at hoff
  simp only [Range.Disjoint, Range.of, Pointer.add_id, hoff] at hd ⊢
  rcases hd with hid | hbefore | hafter
  · exact Or.inl hid
  · exact Or.inr (Or.inl (by omega))
  · exact Or.inr (Or.inr (by omega))

end Agave.Ed25519.SHA512.Execution.Avx2
