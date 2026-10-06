import SSA.Projects.Agave.Ed25519.Proof.SerialFieldMul.Execution

namespace Agave.Ed25519.SerialPoint.Execution
open LeanMLIR.RIR
open SerialFieldMul
open Reduce64.Execution (SmallRange)

private theorem disjoint_limb_chunks (h : SmallRange m p bytes)
    (hi : 8 * i + 8 ≤ bytes) (hj : 8 * j + 8 ≤ bytes) (hne : i ≠ j) :
    (Range.of (p.add (BitVec.ofNat 64 (8 * i))) 64).Disjoint
      (Range.of (p.add (BitVec.ofNat 64 (8 * j))) 64) := by
  have hi64 : 8 * i < 2^64 := by have := h.offset_lt; norm_num at *; omega
  have hj64 : 8 * j < 2^64 := by have := h.offset_lt; norm_num at *; omega
  have hiOff := Pointer.offsetInBits_add (h.no_wrap (k := 8 * i) (by omega))
  have hjOff := Pointer.offsetInBits_add (h.no_wrap (k := 8 * j) (by omega))
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi64] at hiOff
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hj64] at hjOff
  simp only [Range.Disjoint, Range.of, Pointer.add_id, hiOff, hjOff]
  omega

/-- Read back all five limbs from the actual five-store memory schedule. -/
theorem storeLimbs_readAt (m : MemoryState) (dst : Pointer) (v : Fin 5 → BitVec 64)
    (h : SmallRange m dst 40) (k : Fin 5) :
    (storeLimbs m dst v).readAt (dst.add (BitVec.ofNat 64 (8 * k.val))) 64 = v k := by
  have hf0 := h.fits_add (k := 0) (count := 8) (by decide)
  have hf1 := h.fits_add (k := 8) (count := 8) (by decide)
  have hf2 := h.fits_add (k := 16) (count := 8) (by decide)
  have hf3 := h.fits_add (k := 24) (count := 8) (by decide)
  have hf4 := h.fits_add (k := 32) (count := 8) (by decide)
  have hd10 := disjoint_limb_chunks h (i := 1) (j := 0) (by decide) (by decide) (by decide)
  have hd20 := disjoint_limb_chunks h (i := 2) (j := 0) (by decide) (by decide) (by decide)
  have hd21 := disjoint_limb_chunks h (i := 2) (j := 1) (by decide) (by decide) (by decide)
  have hd30 := disjoint_limb_chunks h (i := 3) (j := 0) (by decide) (by decide) (by decide)
  have hd31 := disjoint_limb_chunks h (i := 3) (j := 1) (by decide) (by decide) (by decide)
  have hd32 := disjoint_limb_chunks h (i := 3) (j := 2) (by decide) (by decide) (by decide)
  have hd40 := disjoint_limb_chunks h (i := 4) (j := 0) (by decide) (by decide) (by decide)
  have hd41 := disjoint_limb_chunks h (i := 4) (j := 1) (by decide) (by decide) (by decide)
  have hd42 := disjoint_limb_chunks h (i := 4) (j := 2) (by decide) (by decide) (by decide)
  have hd43 := disjoint_limb_chunks h (i := 4) (j := 3) (by decide) (by decide) (by decide)
  norm_num at hf0 hf1 hf2 hf3 hf4 hd10 hd20 hd21 hd30 hd31 hd32 hd40 hd41 hd42 hd43
  fin_cases k
  · norm_num only [storeLimbs, BitVec.ofNat_eq_ofNat, Pointer.add_zero]
    erw [MemoryState.readAt_storeAt_disjoint hd40, MemoryState.readAt_storeAt_disjoint hd30, MemoryState.readAt_storeAt_disjoint hd20, MemoryState.readAt_storeAt_disjoint hd10]
    exact MemoryState.readAt_storeAt_self hf0 _
  · norm_num only [storeLimbs, BitVec.ofNat_eq_ofNat, Pointer.add_zero]
    erw [MemoryState.readAt_storeAt_disjoint hd41, MemoryState.readAt_storeAt_disjoint hd31, MemoryState.readAt_storeAt_disjoint hd21]
    exact MemoryState.readAt_storeAt_self hf1.storeAt _
  · norm_num only [storeLimbs, BitVec.ofNat_eq_ofNat, Pointer.add_zero]
    erw [MemoryState.readAt_storeAt_disjoint hd42, MemoryState.readAt_storeAt_disjoint hd32]
    exact MemoryState.readAt_storeAt_self hf2.storeAt.storeAt _
  · norm_num only [storeLimbs, BitVec.ofNat_eq_ofNat, Pointer.add_zero]
    erw [MemoryState.readAt_storeAt_disjoint hd43]
    exact MemoryState.readAt_storeAt_self hf3.storeAt.storeAt.storeAt _
  · norm_num only [storeLimbs, BitVec.ofNat_eq_ofNat, Pointer.add_zero]
    exact MemoryState.readAt_storeAt_self hf4.storeAt.storeAt.storeAt.storeAt _

theorem readLimbs_storeLimbs (s : GlobalState) (dst : Pointer) (v : Fin 5 → BitVec 64)
    (h : SmallRange s.mem dst 40) :
    readLimbs { s with mem := storeLimbs s.mem dst v } dst = v := by
  funext k
  exact storeLimbs_readAt s.mem dst v h k

end Agave.Ed25519.SerialPoint.Execution
