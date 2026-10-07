import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2Execution
import SSA.Projects.Agave.Ed25519.Proof.SHA512.WindowSchedule

/-! The scratch-memory invariant for the imported bb5 two-round loop.
A group consumes sixteen rounds in eight pair iterations. Each iteration
replaces precisely its consumed pair with the schedule pair sixteen rounds
later. At the fourth group boundary the invariant is exactly TailSchedule. -/

namespace Agave.Ed25519.SHA512.Execution.Avx2

open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Spec

def scheduleKW (words : List Word) (r : Nat) : Word :=
  constants.toList.getD r 0 + words.getD r 0

/-- After j pairs in group b, slots before 2*j belong to the next group;
remaining slots still contain the current group's unconsumed words. -/
structure PairScratch (mem : MemoryState) (scratch : Pointer)
    (words : List Word) (b j : Nat) : Prop where
  live : SmallRange mem scratch 128
  slots : ∀ t, t < 16 → mem.readAt (scratch.add (BitVec.ofNat 64 (8*t))) 64 =
    if t < 2*j then scheduleKW words (16*(b+1)+t) else scheduleKW words (16*b+t)

/-- The sole bb5 store replaces the current two-word scratch slot. -/
def pairScratchStore (mem : MemoryState) (scratch : Pointer) (j : Nat)
    (lo hi : Word) : MemoryState :=
  mem.storeAt (scratch.add (BitVec.ofNat 64 (16*j))) (hi ++ lo)

private theorem pair_slot_offset (mem : MemoryState) (scratch : Pointer)
    (h : SmallRange mem scratch 128) (t : Nat) (ht : t ≤ 16) :
    (scratch.add (BitVec.ofNat 64 (8*t))).offsetInBits = scratch.offsetInBits + 64*t := by
  have hx := Pointer.offsetInBits_add (h.no_wrap (k := 8*t) (by omega))
  have hsmall : 8*t < 2^64 := by omega
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsmall] at hx
  convert hx using 1
  omega

/-- Readback of the exact 128-bit store, including all untouched scratch words. -/
theorem pairScratchStore_read (mem : MemoryState) (scratch : Pointer)
    (h : SmallRange mem scratch 128) (j t : Nat) (hj : j < 8) (ht : t < 16)
    (lo hi : Word) :
    (pairScratchStore mem scratch j lo hi).readAt
      (scratch.add (BitVec.ofNat 64 (8*t))) 64 =
        if t = 2*j then lo else if t = 2*j+1 then hi
        else mem.readAt (scratch.add (BitVec.ofNat 64 (8*t))) 64 := by
  have hptr : scratch.add (BitVec.ofNat 64 (16*j)) =
      scratch.add (BitVec.ofNat 64 (8*(2*j))) := by congr 2; omega
  have hp := pair_slot_offset mem scratch h (2*j) (by omega)
  have hq := pair_slot_offset mem scratch h t (by omega)
  have hfits : Fits mem (scratch.add (BitVec.ofNat 64 (16*j))) 128 :=
    h.fits_add (k := 16*j) (count := 16) (by omega)
  unfold pairScratchStore
  rw [hptr] at hfits ⊢
  by_cases h0 : t = 2*j
  · subst t
    rw [ite_eq_left rfl]
    have hr := MemoryState.readAt_storeAt_subrange hfits
      (q := scratch.add (BitVec.ofNat 64 (8*(2*j))))
      (w' := 64) rfl (by omega) (by omega) (hi ++ lo)
    simpa only [Nat.sub_self, BitVec.extractLsb'_append_eq_right] using hr
  · rw [ite_eq_right h0]
    by_cases h1 : t = 2*j+1
    · rw [ite_eq_left h1]
      have hoff : (scratch.add (BitVec.ofNat 64 (8*t))).offsetInBits -
          (scratch.add (BitVec.ofNat 64 (8*(2*j)))).offsetInBits = 64 := by
        rw [hp, hq]
        omega
      have hr := MemoryState.readAt_storeAt_subrange hfits
        (q := scratch.add (BitVec.ofNat 64 (8*t)))
        (w' := 64) rfl (by rw [hp, hq]; omega) (by rw [hoff]) (hi ++ lo)
      simpa only [hoff, BitVec.extractLsb'_append_eq_left] using hr
    · rw [ite_eq_right h1]
      apply MemoryState.readAt_storeAt_disjoint
      simp only [Range.Disjoint, Range.of, Pointer.add_id, hp, hq]
      omega

/-- The exact store advances the mixed old/new scratch invariant by two words. -/
theorem PairScratch.advance {mem : MemoryState} {scratch : Pointer} {words : List Word}
    {b j : Nat} (h : PairScratch mem scratch words b j) (hj : j < 8) :
    PairScratch
      (pairScratchStore mem scratch j (scheduleKW words (16*(b+1)+2*j))
        (scheduleKW words (16*(b+1)+2*j+1))) scratch words b (j+1) := by
  refine ⟨h.live.storeAt _ _, ?_⟩
  intro t ht
  rw [pairScratchStore_read mem scratch h.live j t hj ht, h.slots t ht]
  by_cases h0 : t = 2*j
  · subst t
    simp only [show 2*j < 2*(j+1) by omega, ite_true]
  · by_cases h1 : t = 2*j+1
    · subst t
      simp only [h0, ite_false, show 2*j+1 < 2*(j+1) by omega,
        ite_true, Nat.add_assoc]
    · have heq : (t < 2*(j+1)) = (t < 2*j)  := by
        apply propext
        omega
      simp only [h0, h1, ite_false, heq]

/-- The control-only bb3/bb4 boundary resets j after all eight pairs. -/
theorem PairScratch.next_group {mem : MemoryState} {scratch : Pointer} {words : List Word}
    {b : Nat} (h : PairScratch mem scratch words b 8) :
    PairScratch mem scratch words (b+1) 0 := by
  refine ⟨h.live, ?_⟩
  intro t ht
  simpa only [show 2*8 = 16 by decide, ht, ite_true, Nat.mul_zero,
    Nat.not_lt_zero, ite_false] using h.slots t ht

/-- Four complete groups install exactly the final sixteen words read by bb6. -/
theorem PairScratch.tail {mem : MemoryState} {scratch : Pointer} {words : List Word}
    (h : PairScratch mem scratch words 4 0) : TailSchedule mem scratch words := by
  refine ⟨h.live, ?_⟩
  intro r hlo hhi
  have hr := h.slots (r-64) (by omega)
  have hindex : 16*4+(r-64) = r := by omega
  simpa only [Nat.mul_zero, Nat.not_lt_zero, ite_false, hindex, scheduleKW] using hr

end Agave.Ed25519.SHA512.Execution.Avx2
