import SSA.Projects.Agave.Ed25519.Proof.SerialPoint.CallMemory
import SSA.Projects.Agave.Ed25519.Proof.SerialPoint.PointLayout

namespace Agave.Ed25519.SerialPoint.Execution
open LeanMLIR.RIR
open SerialFieldMul
open Reduce64.Execution (SmallRange)

def readPointWords (s : GlobalState) (p : Pointer) : PointWords :=
  fun i => s.mem.readAt (p.add (BitVec.ofNat 64 (8*i.val))) 64

def storePointWords (m : MemoryState) (p : Pointer) (v : PointWords) : MemoryState :=
  ((((((((((((((((((((m).storeAt p (v 0)).storeAt (p.add 8) (v 1)).storeAt (p.add 16) (v 2)).storeAt (p.add 24) (v 3)).storeAt (p.add 32) (v 4)).storeAt (p.add 40) (v 5)).storeAt (p.add 48) (v 6)).storeAt (p.add 56) (v 7)).storeAt (p.add 64) (v 8)).storeAt (p.add 72) (v 9)).storeAt (p.add 80) (v 10)).storeAt (p.add 88) (v 11)).storeAt (p.add 96) (v 12)).storeAt (p.add 104) (v 13)).storeAt (p.add 112) (v 14)).storeAt (p.add 120) (v 15)).storeAt (p.add 128) (v 16)).storeAt (p.add 136) (v 17)).storeAt (p.add 144) (v 18)).storeAt (p.add 152) (v 19)

/-- Disjoint byte slices of one nonwrapping allocation. The widths are in bytes. -/
theorem subranges_disjoint (h : SmallRange m p bytes)
    (hi : i + ni ≤ bytes) (hj : j + nj ≤ bytes)
    (hd : i + ni ≤ j ∨ j + nj ≤ i) :
    (Range.of (p.add (BitVec.ofNat 64 i)) (8*ni)).Disjoint
      (Range.of (p.add (BitVec.ofNat 64 j)) (8*nj)) := by
  have hi64 : i < 2^64 := by have := h.offset_lt; omega
  have hj64 : j < 2^64 := by have := h.offset_lt; omega
  have hiOff := Pointer.offsetInBits_add (h.no_wrap (k := i) (by omega))
  have hjOff := Pointer.offsetInBits_add (h.no_wrap (k := j) (by omega))
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi64] at hiOff
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hj64] at hjOff
  simp only [Range.Disjoint, Range.of, Pointer.add_id, hiOff, hjOff]
  omega

@[mlir_transport] theorem smallRange_storePointWords (h : SmallRange m q bytes)
    (p : Pointer) (v : PointWords) : SmallRange (storePointWords m p v) q bytes := by
  unfold storePointWords
  exact ((((((((((((((((((((h.storeAt p (v 0)).storeAt (p.add 8) (v 1)).storeAt (p.add 16) (v 2)).storeAt (p.add 24) (v 3)).storeAt (p.add 32) (v 4)).storeAt (p.add 40) (v 5)).storeAt (p.add 48) (v 6)).storeAt (p.add 56) (v 7)).storeAt (p.add 64) (v 8)).storeAt (p.add 72) (v 9)).storeAt (p.add 80) (v 10)).storeAt (p.add 88) (v 11)).storeAt (p.add 96) (v 12)).storeAt (p.add 104) (v 13)).storeAt (p.add 112) (v 14)).storeAt (p.add 120) (v 15)).storeAt (p.add 128) (v 16)).storeAt (p.add 136) (v 17)).storeAt (p.add 144) (v 18)).storeAt (p.add 152) (v 19))

/-- Exact readback of the twenty stores, including the last coordinate. -/
theorem storePointWords_readAt (m : MemoryState) (p : Pointer) (v : PointWords)
    (h : SmallRange m p 160) (k : Fin 20) :
    (storePointWords m p v).readAt (p.add (BitVec.ofNat 64 (8*k.val))) 64 = v k := by
  have hf (i : Fin 20) : Fits m (p.add (BitVec.ofNat 64 (8*i.val))) 64 :=
    h.fits_add (k := 8*i.val) (count := 8) (by omega)
  have hd (i j : Fin 20) (hne : i ≠ j) :
      (Range.of (p.add (BitVec.ofNat 64 (8*i.val))) 64).Disjoint
        (Range.of (p.add (BitVec.ofNat 64 (8*j.val))) 64) := by
    apply subranges_disjoint h (ni := 8) (nj := 8) (by omega) (by omega)
    have : i.val ≠ j.val := fun heq => hne (Fin.ext heq)
    omega
  fin_cases k
  · norm_num only [storePointWords, BitVec.ofNat_eq_ofNat, Pointer.add_zero]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 19 0 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 18 0 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 17 0 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 16 0 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 15 0 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 14 0 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 13 0 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 12 0 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 11 0 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 10 0 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 9 0 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 8 0 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 7 0 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 6 0 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 5 0 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 4 0 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 3 0 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 2 0 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 1 0 (by decide))]
    have hf0 : Fits m p 64 := by simpa using hf 0
    exact MemoryState.readAt_storeAt_self hf0 (v 0)
  · norm_num only [storePointWords, BitVec.ofNat_eq_ofNat, Pointer.add_zero]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 19 1 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 18 1 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 17 1 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 16 1 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 15 1 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 14 1 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 13 1 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 12 1 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 11 1 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 10 1 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 9 1 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 8 1 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 7 1 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 6 1 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 5 1 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 4 1 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 3 1 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 2 1 (by decide))]
    exact MemoryState.readAt_storeAt_self (hf 1).storeAt (v 1)
  · norm_num only [storePointWords, BitVec.ofNat_eq_ofNat, Pointer.add_zero]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 19 2 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 18 2 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 17 2 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 16 2 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 15 2 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 14 2 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 13 2 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 12 2 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 11 2 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 10 2 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 9 2 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 8 2 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 7 2 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 6 2 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 5 2 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 4 2 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 3 2 (by decide))]
    exact MemoryState.readAt_storeAt_self (hf 2).storeAt.storeAt (v 2)
  · norm_num only [storePointWords, BitVec.ofNat_eq_ofNat, Pointer.add_zero]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 19 3 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 18 3 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 17 3 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 16 3 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 15 3 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 14 3 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 13 3 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 12 3 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 11 3 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 10 3 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 9 3 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 8 3 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 7 3 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 6 3 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 5 3 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 4 3 (by decide))]
    exact MemoryState.readAt_storeAt_self (hf 3).storeAt.storeAt.storeAt (v 3)
  · norm_num only [storePointWords, BitVec.ofNat_eq_ofNat, Pointer.add_zero]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 19 4 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 18 4 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 17 4 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 16 4 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 15 4 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 14 4 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 13 4 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 12 4 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 11 4 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 10 4 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 9 4 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 8 4 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 7 4 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 6 4 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 5 4 (by decide))]
    exact MemoryState.readAt_storeAt_self (hf 4).storeAt.storeAt.storeAt.storeAt (v 4)
  · norm_num only [storePointWords, BitVec.ofNat_eq_ofNat, Pointer.add_zero]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 19 5 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 18 5 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 17 5 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 16 5 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 15 5 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 14 5 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 13 5 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 12 5 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 11 5 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 10 5 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 9 5 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 8 5 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 7 5 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 6 5 (by decide))]
    exact MemoryState.readAt_storeAt_self (hf 5).storeAt.storeAt.storeAt.storeAt.storeAt (v 5)
  · norm_num only [storePointWords, BitVec.ofNat_eq_ofNat, Pointer.add_zero]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 19 6 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 18 6 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 17 6 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 16 6 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 15 6 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 14 6 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 13 6 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 12 6 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 11 6 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 10 6 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 9 6 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 8 6 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 7 6 (by decide))]
    exact MemoryState.readAt_storeAt_self (hf 6).storeAt.storeAt.storeAt.storeAt.storeAt.storeAt (v 6)
  · norm_num only [storePointWords, BitVec.ofNat_eq_ofNat, Pointer.add_zero]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 19 7 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 18 7 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 17 7 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 16 7 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 15 7 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 14 7 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 13 7 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 12 7 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 11 7 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 10 7 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 9 7 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 8 7 (by decide))]
    exact MemoryState.readAt_storeAt_self (hf 7).storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt (v 7)
  · norm_num only [storePointWords, BitVec.ofNat_eq_ofNat, Pointer.add_zero]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 19 8 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 18 8 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 17 8 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 16 8 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 15 8 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 14 8 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 13 8 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 12 8 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 11 8 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 10 8 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 9 8 (by decide))]
    exact MemoryState.readAt_storeAt_self (hf 8).storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt (v 8)
  · norm_num only [storePointWords, BitVec.ofNat_eq_ofNat, Pointer.add_zero]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 19 9 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 18 9 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 17 9 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 16 9 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 15 9 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 14 9 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 13 9 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 12 9 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 11 9 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 10 9 (by decide))]
    exact MemoryState.readAt_storeAt_self (hf 9).storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt (v 9)
  · norm_num only [storePointWords, BitVec.ofNat_eq_ofNat, Pointer.add_zero]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 19 10 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 18 10 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 17 10 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 16 10 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 15 10 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 14 10 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 13 10 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 12 10 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 11 10 (by decide))]
    exact MemoryState.readAt_storeAt_self (hf 10).storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt (v 10)
  · norm_num only [storePointWords, BitVec.ofNat_eq_ofNat, Pointer.add_zero]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 19 11 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 18 11 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 17 11 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 16 11 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 15 11 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 14 11 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 13 11 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 12 11 (by decide))]
    exact MemoryState.readAt_storeAt_self (hf 11).storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt (v 11)
  · norm_num only [storePointWords, BitVec.ofNat_eq_ofNat, Pointer.add_zero]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 19 12 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 18 12 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 17 12 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 16 12 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 15 12 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 14 12 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 13 12 (by decide))]
    exact MemoryState.readAt_storeAt_self (hf 12).storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt (v 12)
  · norm_num only [storePointWords, BitVec.ofNat_eq_ofNat, Pointer.add_zero]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 19 13 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 18 13 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 17 13 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 16 13 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 15 13 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 14 13 (by decide))]
    exact MemoryState.readAt_storeAt_self (hf 13).storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt (v 13)
  · norm_num only [storePointWords, BitVec.ofNat_eq_ofNat, Pointer.add_zero]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 19 14 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 18 14 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 17 14 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 16 14 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 15 14 (by decide))]
    exact MemoryState.readAt_storeAt_self (hf 14).storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt (v 14)
  · norm_num only [storePointWords, BitVec.ofNat_eq_ofNat, Pointer.add_zero]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 19 15 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 18 15 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 17 15 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 16 15 (by decide))]
    exact MemoryState.readAt_storeAt_self (hf 15).storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt (v 15)
  · norm_num only [storePointWords, BitVec.ofNat_eq_ofNat, Pointer.add_zero]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 19 16 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 18 16 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 17 16 (by decide))]
    exact MemoryState.readAt_storeAt_self (hf 16).storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt (v 16)
  · norm_num only [storePointWords, BitVec.ofNat_eq_ofNat, Pointer.add_zero]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 19 17 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 18 17 (by decide))]
    exact MemoryState.readAt_storeAt_self (hf 17).storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt (v 17)
  · norm_num only [storePointWords, BitVec.ofNat_eq_ofNat, Pointer.add_zero]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hd 19 18 (by decide))]
    exact MemoryState.readAt_storeAt_self (hf 18).storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt (v 18)
  · norm_num only [storePointWords, BitVec.ofNat_eq_ofNat, Pointer.add_zero]
    exact MemoryState.readAt_storeAt_self (hf 19).storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt (v 19)

/-- A point result may be read with any allocation counter: only memory matters. -/
theorem readPointWords_storePointWords (s : GlobalState) (p : Pointer) (v : PointWords)
    (h : SmallRange s.mem p 160) :
    readPointWords { s with mem := storePointWords s.mem p v } p = v := by
  funext k
  exact storePointWords_readAt s.mem p v h k

/-- A point result preserves every read outside its 160-byte destination. -/
theorem readAt_storePointWords_frame (m : MemoryState) (p q : Pointer)
    (v : PointWords) (bits : Nat) (h : SmallRange m p 160)
    (hd : (Range.of q bits).Disjoint (Range.of p 1280)) :
    (storePointWords m p v).readAt q bits = m.readAt q bits := by
  have hchunk (k : Fin 20) :
      (Range.of (p.add (BitVec.ofNat 64 (8*k.val))) 64).Disjoint (Range.of q bits) := by
    have hk : 8*k.val < 2^64 := by omega
    have hoff := Pointer.offsetInBits_add (h.no_wrap (k := 8*k.val) (by omega))
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk] at hoff
    simp only [Range.Disjoint, Range.of, Pointer.add_id, hoff] at hd ⊢
    rcases hd with hne | hbefore | hafter
    · exact Or.inl (Ne.symm hne)
    · exact Or.inr (Or.inr (by omega))
    · exact Or.inr (Or.inl (by omega))
  unfold storePointWords
  erw [MemoryState.readAt_storeAt_disjoint (by simpa using hchunk 19)]
  erw [MemoryState.readAt_storeAt_disjoint (by simpa using hchunk 18)]
  erw [MemoryState.readAt_storeAt_disjoint (by simpa using hchunk 17)]
  erw [MemoryState.readAt_storeAt_disjoint (by simpa using hchunk 16)]
  erw [MemoryState.readAt_storeAt_disjoint (by simpa using hchunk 15)]
  erw [MemoryState.readAt_storeAt_disjoint (by simpa using hchunk 14)]
  erw [MemoryState.readAt_storeAt_disjoint (by simpa using hchunk 13)]
  erw [MemoryState.readAt_storeAt_disjoint (by simpa using hchunk 12)]
  erw [MemoryState.readAt_storeAt_disjoint (by simpa using hchunk 11)]
  erw [MemoryState.readAt_storeAt_disjoint (by simpa using hchunk 10)]
  erw [MemoryState.readAt_storeAt_disjoint (by simpa using hchunk 9)]
  erw [MemoryState.readAt_storeAt_disjoint (by simpa using hchunk 8)]
  erw [MemoryState.readAt_storeAt_disjoint (by simpa using hchunk 7)]
  erw [MemoryState.readAt_storeAt_disjoint (by simpa using hchunk 6)]
  erw [MemoryState.readAt_storeAt_disjoint (by simpa using hchunk 5)]
  erw [MemoryState.readAt_storeAt_disjoint (by simpa using hchunk 4)]
  erw [MemoryState.readAt_storeAt_disjoint (by simpa using hchunk 3)]
  erw [MemoryState.readAt_storeAt_disjoint (by simpa using hchunk 2)]
  erw [MemoryState.readAt_storeAt_disjoint (by simpa using hchunk 1)]
  erw [MemoryState.readAt_storeAt_disjoint (by simpa using hchunk 0)]

theorem storePointWords_allocationShape (m : MemoryState) (p : Pointer)
    (v : PointWords) (id : BlockId) :
    ((storePointWords m p v)[id]?).map MemoryBlock.length = (m[id]?).map MemoryBlock.length := by
  simp only [storePointWords, storeAt_allocationShape]

theorem wf_storePointWords (s : GlobalState) (hwf : s.WF) (p : Pointer) (v : PointWords) :
    ({ s with mem := storePointWords s.mem p v } : GlobalState).WF := by
  simpa only [storePointWords, GlobalState.WF_storeAt] using hwf

/-- Normal form of a returning point helper: its scratch blocks have been
erased, the allocation counter has advanced, and the point words remain. -/
def pointPost (s : GlobalState) (p : Pointer) (v : PointWords) (blocks : Nat) : GlobalState :=
  { alloc := ⟨s.alloc.nextFreeBlock + blocks⟩, mem := storePointWords s.mem p v }

theorem pointPost_wf (s : GlobalState) (hwf : s.WF) (p : Pointer)
    (v : PointWords) (blocks : Nat) : (pointPost s p v blocks).WF :=
  (wf_storePointWords s hwf p v).add_blocks

theorem pointPost_readback (s : GlobalState) (p : Pointer) (v : PointWords)
    (blocks : Nat) (h : SmallRange s.mem p 160) :
    readPointWords (pointPost s p v blocks) p = v := by
  funext i
  exact storePointWords_readAt s.mem p v h i

end Agave.Ed25519.SerialPoint.Execution
