import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionPairStore

/-! Concrete memory inputs and frames for repeated execution of bb5.
Disjoint byte ranges suffice even when scratch and constants share an allocation. -/
namespace Agave.Ed25519.SHA512.Execution.Avx2

open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Spec

/-- Precisely the constant pairs loaded by the thirty-two schedule iterations. -/
structure PairConstants (mem : MemoryState) (k : Pointer) : Prop where
  live : SmallRange mem k 640
  pairs : ∀ r, r + 1 < 64 →
    mem.readAt (k.add (BitVec.ofNat 64 (8*(r+16)))) 128 =
      constants.toList.getD (r+17) 0 ++ constants.toList.getD (r+16) 0

private theorem range_disjoint_add_right {mem : MemoryState} {p q : Pointer}
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

/-- The current two-word scratch slot is a live 16-byte subrange. -/
theorem pair_slot_live {mem : MemoryState} {scratch : Pointer}
    (h : SmallRange mem scratch 128) (j : Nat) (hj : j < 8) :
    SmallRange mem (scratch.add (BitVec.ofNat 64 (16*j))) 16 := by
  have hn := h.no_wrap (k := 16*j) (by omega)
  have hsmall : 16*j < 2^64 := by omega
  obtain ⟨block, hb, hsize, hfit⟩ := h
  refine ⟨block, hb, hsize, ?_⟩
  simp only [Pointer.add, BitVec.toNat_add_of_not_uaddOverflow hn,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsmall]
  omega

/-- The two scalar loads consume exactly the current unconsumed pair. -/
theorem PairScratch.read_pair {mem : MemoryState} {scratch : Pointer} {words : List Word}
    {b j : Nat} (h : PairScratch mem scratch words b j) (hj : j < 8) :
    mem.readAt (scratch.add (BitVec.ofNat 64 (16*j))) 64 =
      scheduleKW words (16*b+2*j) ∧
    mem.readAt ((scratch.add (BitVec.ofNat 64 (16*j))).add 8#64) 64 =
      scheduleKW words (16*b+2*j+1) := by
  have hp0 : scratch.add (BitVec.ofNat 64 (16*j)) =
      scratch.add (BitVec.ofNat 64 (8*(2*j))) := by congr 2; omega
  have hp1 : (scratch.add (BitVec.ofNat 64 (16*j))).add 8#64 =
      scratch.add (BitVec.ofNat 64 (8*(2*j+1))) := by
    rw [Pointer.add_add, ← BitVec.ofNat_add]
    congr 2
    omega
  constructor
  · simpa only [hp0, Nat.lt_irrefl, ite_false] using h.slots (2*j) (by omega)
  · rw [hp1]
    simpa only [show ¬2*j+1 < 2*j by omega, ite_false, Nat.add_assoc] using
      h.slots (2*j+1) (by omega)

/-- Every read disjoint from the whole scratch range survives its pair store. -/
theorem pairScratchStore_read_disjoint {mem : MemoryState} {scratch p : Pointer}
    {w : Nat} (hs : SmallRange mem scratch 128) (j : Nat) (hj : j < 8)
    (lo hi : Word) (hd : (Range.of scratch 1024).Disjoint (Range.of p w)) :
    (pairScratchStore mem scratch j lo hi).readAt p w = mem.readAt p w := by
  apply MemoryState.readAt_storeAt_disjoint
  exact (range_disjoint_add_right hs (off := 16*j) (count := 16)
    (by omega) hd.symm).symm

/-- In-place scratch updates preserve the concrete constant-table input. -/
theorem PairConstants.store {mem : MemoryState} {k scratch : Pointer}
    (h : PairConstants mem k) (hs : SmallRange mem scratch 128)
    (j : Nat) (hj : j < 8) (lo hi : Word)
    (hd : (Range.of scratch 1024).Disjoint (Range.of k 5120)) :
    PairConstants (pairScratchStore mem scratch j lo hi) k := by
  refine ⟨h.live.storeAt _ _, ?_⟩
  intro r hr
  have hdp := range_disjoint_add_right h.live (off := 8*(r+16)) (count := 16)
    (by omega) hd
  rw [pairScratchStore_read_disjoint hs j hj lo hi hdp]
  exact h.pairs r hr

/-- The exact pair-store global state preserves every external disjoint read. -/
theorem pairStoreState_read_disjoint (mem : GlobalState) (scratch p : Pointer)
    (j : Nat) (lo hi : Word) (w : Nat) (hs : SmallRange mem.mem scratch 128)
    (hj : j < 8) (hd : (Range.of scratch 1024).Disjoint (Range.of p w)) :
    (pairStoreState mem scratch j lo hi).mem.readAt p w = mem.mem.readAt p w :=
  pairScratchStore_read_disjoint hs j hj lo hi hd

end Agave.Ed25519.SHA512.Execution.Avx2
