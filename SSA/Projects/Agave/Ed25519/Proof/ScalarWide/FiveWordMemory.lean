import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.MontgomeryStores
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Fin

/-! Readback and range preservation for the actual five u64 scalar slots. -/
namespace Agave.Ed25519.Verifier.Execution.ScalarMontgomeryMul
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution (SmallRange)

theorem outputStores_smallRange (m : MemoryState) (out q : Pointer)
    (words : Fin 5 → BitVec 64) (bytes : Nat) (h : SmallRange m q bytes) :
    SmallRange (outputStores m out words) q bytes := by
  exact ((((h.storeAt out (words 0)).storeAt (out.add 8#64) (words 1)).storeAt
    (out.add 16#64) (words 2)).storeAt (out.add 24#64) (words 3)).storeAt
    (out.add 32#64) (words 4)

theorem disjoint_word_slots (m : MemoryState) (p : Pointer)
    (h : SmallRange m p 40) (i j : Fin 5) (hne : i ≠ j) :
    (Range.of (p.add (BitVec.ofNat 64 (8 * i.val))) 64).Disjoint
      (Range.of (p.add (BitVec.ofNat 64 (8 * j.val))) 64) := by
  have hi64 : 8 * i.val < 2 ^ 64 := by have := i.isLt; omega
  have hj64 : 8 * j.val < 2 ^ 64 := by have := j.isLt; omega
  have hio := Pointer.offsetInBits_add (h.no_wrap (k := 8 * i.val) (by omega))
  have hjo := Pointer.offsetInBits_add (h.no_wrap (k := 8 * j.val) (by omega))
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi64] at hio
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hj64] at hjo
  have hval : i.val ≠ j.val := fun he => hne (Fin.ext he)
  simp only [Range.Disjoint, Range.of, Pointer.add_id, hio, hjo]
  omega

theorem outputStores_read (m : MemoryState) (dst : Pointer)
    (words : Fin 5 → BitVec 64) (h : SmallRange m dst 40) (k : Fin 5) :
    (outputStores m dst words).readAt (dst.add (BitVec.ofNat 64 (8 * k.val))) 64 = words k := by
  have hf0 := h.fits_add (k := 0) (count := 8) (by decide)
  have hf1 := h.fits_add (k := 8) (count := 8) (by decide)
  have hf2 := h.fits_add (k := 16) (count := 8) (by decide)
  have hf3 := h.fits_add (k := 24) (count := 8) (by decide)
  have hf4 := h.fits_add (k := 32) (count := 8) (by decide)
  have hd10 := disjoint_word_slots m dst h 1 0 (by decide)
  have hd20 := disjoint_word_slots m dst h 2 0 (by decide)
  have hd21 := disjoint_word_slots m dst h 2 1 (by decide)
  have hd30 := disjoint_word_slots m dst h 3 0 (by decide)
  have hd31 := disjoint_word_slots m dst h 3 1 (by decide)
  have hd32 := disjoint_word_slots m dst h 3 2 (by decide)
  have hd40 := disjoint_word_slots m dst h 4 0 (by decide)
  have hd41 := disjoint_word_slots m dst h 4 1 (by decide)
  have hd42 := disjoint_word_slots m dst h 4 2 (by decide)
  have hd43 := disjoint_word_slots m dst h 4 3 (by decide)
  norm_num at hd10 hd20 hd21 hd30 hd31 hd32 hd40 hd41 hd42 hd43
  simp only [Pointer.add_zero] at hf0
  fin_cases k
  · norm_num [outputStores]
    rw [MemoryState.readAt_storeAt_disjoint hd40, MemoryState.readAt_storeAt_disjoint hd30, MemoryState.readAt_storeAt_disjoint hd20, MemoryState.readAt_storeAt_disjoint hd10]
    exact MemoryState.readAt_storeAt_self hf0 _
  · norm_num [outputStores]
    rw [MemoryState.readAt_storeAt_disjoint hd41, MemoryState.readAt_storeAt_disjoint hd31, MemoryState.readAt_storeAt_disjoint hd21]
    exact MemoryState.readAt_storeAt_self hf1.storeAt _
  · norm_num [outputStores]
    rw [MemoryState.readAt_storeAt_disjoint hd42, MemoryState.readAt_storeAt_disjoint hd32]
    exact MemoryState.readAt_storeAt_self hf2.storeAt.storeAt _
  · norm_num [outputStores]
    rw [MemoryState.readAt_storeAt_disjoint hd43]
    exact MemoryState.readAt_storeAt_self hf3.storeAt.storeAt.storeAt _
  · norm_num [outputStores]
    exact MemoryState.readAt_storeAt_self hf4.storeAt.storeAt.storeAt.storeAt _

theorem outputStores_read_other (m : MemoryState) (dst q : Pointer)
    (words : Fin 5 → BitVec 64) (width : Nat) (hne : dst.id ≠ q.id) :
    (outputStores m dst words).readAt q width = m.readAt q width := by
  have h0 : (Range.of dst 64).Disjoint (Range.of q width) := Range.disjoint_of_id_ne hne
  have h1 : (Range.of (dst.add 8#64) 64).Disjoint (Range.of q width) := Range.disjoint_of_id_ne hne
  have h2 : (Range.of (dst.add 16#64) 64).Disjoint (Range.of q width) := Range.disjoint_of_id_ne hne
  have h3 : (Range.of (dst.add 24#64) 64).Disjoint (Range.of q width) := Range.disjoint_of_id_ne hne
  have h4 : (Range.of (dst.add 32#64) 64).Disjoint (Range.of q width) := Range.disjoint_of_id_ne hne
  simp only [outputStores, MemoryState.readAt_storeAt_disjoint h4,
    MemoryState.readAt_storeAt_disjoint h3, MemoryState.readAt_storeAt_disjoint h2,
    MemoryState.readAt_storeAt_disjoint h1, MemoryState.readAt_storeAt_disjoint h0]

end Agave.Ed25519.Verifier.Execution.ScalarMontgomeryMul

namespace Agave.Ed25519.Verifier.Execution.ScalarWide
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution (SmallRange)

def copy40State (state : GlobalState) (dst src : Pointer) : GlobalState :=
  {state with mem := state.mem.storeAt dst (state.mem.readAt src 320)}

/-- A full 40-byte copy transports each source limb exactly. -/
theorem copy40_read (state : GlobalState) (dst src : Pointer)
    (hdst : SmallRange state.mem dst 40) (hsrc : SmallRange state.mem src 40)
    (k : Fin 5) :
    (copy40State state dst src).mem.readAt (dst.add (BitVec.ofNat 64 (8 * k.val))) 64 =
      state.mem.readAt (src.add (BitVec.ofNat 64 (8 * k.val))) 64 := by
  have hk : 8 * k.val < 2 ^ 64 := by have := k.isLt; omega
  have hw : (BitVec.ofNat 64 (8 * k.val)).toNat * 8 + 64 ≤ 320 := by
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk]
    have := k.isLt
    omega
  have hr := MemoryState.readAt_add_of_readAt (off := BitVec.ofNat 64 (8 * k.val))
    hsrc.fits (hsrc.no_wrap (by omega)) (w := 64) hw rfl
  exact (MemoryState.readAt_storeAt_add hdst.fits (hdst.no_wrap (by omega)) hw
    (state.mem.readAt src 320)).trans hr.symm

end Agave.Ed25519.Verifier.Execution.ScalarWide
