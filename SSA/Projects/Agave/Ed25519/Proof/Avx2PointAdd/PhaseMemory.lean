import SSA.Projects.Agave.Ed25519.Proof.Avx2FieldMul.ExecutionMemory
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Fin

/-! Packed memory boundaries for point phases. These lemmas concern arbitrary
stored u32 vectors and do not expand or assume a multiplication computation. -/
namespace Agave.Ed25519.Avx2PointAdd.Phases
open LeanMLIR.RIR Avx2FieldMul.Execution Reduce64.Execution

set_option backward.isDefEq.respectTransparency false

/-- Read any one of the five exact packed stores, proving the four other
stores disjoint from that 32-byte slice. -/
theorem storeBlocks_readAt (m : MemoryState) (dst : Pointer) (v : Blocks)
    (h : SmallRange m dst 160) (k : Fin 5) :
    (storeBlocks m dst v).readAt (dst.add (BitVec.ofNat 64 (32 * k.val))) 256 =
      BitVec.packLanes (v k) := by
  have hf0 := h.fits_add (k := 0) (count := 32) (by decide)
  have hf1 := h.fits_add (k := 32) (count := 32) (by decide)
  have hf2 := h.fits_add (k := 64) (count := 32) (by decide)
  have hf3 := h.fits_add (k := 96) (count := 32) (by decide)
  have hf4 := h.fits_add (k := 128) (count := 32) (by decide)
  have hd10 := h.disjoint_chunks (i := 1) (j := 0) (by decide) (by decide) (by decide)
  have hd20 := h.disjoint_chunks (i := 2) (j := 0) (by decide) (by decide) (by decide)
  have hd21 := h.disjoint_chunks (i := 2) (j := 1) (by decide) (by decide) (by decide)
  have hd30 := h.disjoint_chunks (i := 3) (j := 0) (by decide) (by decide) (by decide)
  have hd31 := h.disjoint_chunks (i := 3) (j := 1) (by decide) (by decide) (by decide)
  have hd32 := h.disjoint_chunks (i := 3) (j := 2) (by decide) (by decide) (by decide)
  have hd40 := h.disjoint_chunks (i := 4) (j := 0) (by decide) (by decide) (by decide)
  have hd41 := h.disjoint_chunks (i := 4) (j := 1) (by decide) (by decide) (by decide)
  have hd42 := h.disjoint_chunks (i := 4) (j := 2) (by decide) (by decide) (by decide)
  have hd43 := h.disjoint_chunks (i := 4) (j := 3) (by decide) (by decide) (by decide)
  norm_num [Pointer.add_zero] at hf0 hd10 hd20 hd21 hd30 hd31 hd32 hd40 hd41 hd42 hd43
  fin_cases k
  · norm_num only [storeBlocks, Pointer.add_zero]
    rw (config := { transparency := .default }) [MemoryState.readAt_storeAt_disjoint hd40, MemoryState.readAt_storeAt_disjoint hd30, MemoryState.readAt_storeAt_disjoint hd20, MemoryState.readAt_storeAt_disjoint hd10]
    exact MemoryState.readAt_storeAt_self hf0 _
  · norm_num only [storeBlocks, Pointer.add_zero]
    rw (config := { transparency := .default }) [MemoryState.readAt_storeAt_disjoint hd41, MemoryState.readAt_storeAt_disjoint hd31, MemoryState.readAt_storeAt_disjoint hd21]
    exact MemoryState.readAt_storeAt_self hf1.storeAt _
  · norm_num only [storeBlocks, Pointer.add_zero]
    rw (config := { transparency := .default }) [MemoryState.readAt_storeAt_disjoint hd42, MemoryState.readAt_storeAt_disjoint hd32]
    exact MemoryState.readAt_storeAt_self hf2.storeAt.storeAt _
  · norm_num only [storeBlocks, Pointer.add_zero]
    rw (config := { transparency := .default }) [MemoryState.readAt_storeAt_disjoint hd43]
    exact MemoryState.readAt_storeAt_self hf3.storeAt.storeAt.storeAt _
  · norm_num only [storeBlocks, Pointer.add_zero]
    exact MemoryState.readAt_storeAt_self hf4.storeAt.storeAt.storeAt.storeAt _


theorem readBlocks_storeBlocks (m : MemoryState) (dst : Pointer) (v : Blocks)
    (h : SmallRange m dst 160) : readBlocks (storeBlocks m dst v) dst = v := by
  funext k
  apply Vector.ext
  intro i hi
  simp [readBlocks, storeBlocks_readAt m dst v h, Ty.extractVecElem_packLanes]

theorem storeBlocks_wf (s : GlobalState) (dst : Pointer) (v : Blocks) (h : s.WF) :
    ({s with mem := storeBlocks s.mem dst v} : GlobalState).WF := by
  simpa only [storeBlocks, GlobalState.WF_storeAt] using h

/-- The two multiplication calls and the intervening stores preserve every
previously established small allocation/range witness. -/
theorem storeBlocks_live {m : MemoryState} {p : Pointer} {bytes : Nat}
    (h : SmallRange m p bytes) (dst : Pointer) (v : Blocks) :
    SmallRange (storeBlocks m dst v) p bytes := by
  exact ((((h.storeAt _ _).storeAt _ _).storeAt _ _).storeAt _ _).storeAt _ _

/-- Distinct fresh stack objects and constant tables retain their packed words
when another point object is written. -/
theorem readBlocks_storeBlocks_ne (m : MemoryState) (dst p : Pointer) (v : Blocks)
    (hne : dst.id ≠ p.id) :
    readBlocks (storeBlocks m dst v) p = readBlocks m p := by
  funext k
  apply Vector.ext
  intro i hi
  simp only [readBlocks, Vector.getElem_ofFn]
  have h0 : (Range.of dst 256).Disjoint
      (Range.of (p.add (BitVec.ofNat 64 (32*k.val))) 256) := Or.inl hne
  have h32 : (Range.of (dst.add 32) 256).Disjoint
      (Range.of (p.add (BitVec.ofNat 64 (32*k.val))) 256) := Or.inl hne
  have h64 : (Range.of (dst.add 64) 256).Disjoint
      (Range.of (p.add (BitVec.ofNat 64 (32*k.val))) 256) := Or.inl hne
  have h96 : (Range.of (dst.add 96) 256).Disjoint
      (Range.of (p.add (BitVec.ofNat 64 (32*k.val))) 256) := Or.inl hne
  have h128 : (Range.of (dst.add 128) 256).Disjoint
      (Range.of (p.add (BitVec.ofNat 64 (32*k.val))) 256) := Or.inl hne
  simp only [storeBlocks, MemoryState.readAt_storeAt_disjoint h128,
    MemoryState.readAt_storeAt_disjoint h96, MemoryState.readAt_storeAt_disjoint h64,
    MemoryState.readAt_storeAt_disjoint h32, MemoryState.readAt_storeAt_disjoint h0]

/-- The exact 160-byte copy between the first helper output and the scratch
object reloaded by the difference/sum phase. -/
def copyPointBytes (m : MemoryState) (dst src : Pointer) : MemoryState :=
  m.storeAt dst (m.readAt src 1280)

theorem copyPointBytes_readBlocks (m : MemoryState) (dst src : Pointer)
    (hdst : SmallRange m dst 160) (hsrc : SmallRange m src 160) :
    readBlocks (copyPointBytes m dst src) dst = readBlocks m src := by
  funext k
  have hk : 32 * k.val ≤ 160 := by have := k.isLt; omega
  have hmod : 32 * k.val < 2^64 := by have := k.isLt; norm_num; omega
  have hwidth : (BitVec.ofNat 64 (32 * k.val)).toNat * 8 + 256 ≤ 1280 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hmod]
    have := k.isLt
    omega
  have hs := MemoryState.readAt_add_of_readAt hsrc.fits
    (hsrc.no_wrap hk) hwidth (x := m.readAt src 1280) rfl
  simp only [readBlocks, copyPointBytes]
  rw [MemoryState.readAt_storeAt_add hdst.fits (hdst.no_wrap hk) hwidth, ← hs]

theorem copyPointBytes_wf (s : GlobalState) (dst src : Pointer) (h : s.WF) :
    ({s with mem := copyPointBytes s.mem dst src} : GlobalState).WF := by
  exact h.storeAt

theorem copyPointBytes_live {m : MemoryState} {p : Pointer} {bytes : Nat}
    (h : SmallRange m p bytes) (dst src : Pointer) :
    SmallRange (copyPointBytes m dst src) p bytes :=
  h.storeAt _ _

theorem readAt_storeBlocks_ne (m : MemoryState) (dst ptr : Pointer) (v : Blocks)
    (width : Nat) (hne : dst.id ≠ ptr.id) :
    (storeBlocks m dst v).readAt ptr width = m.readAt ptr width := by
  have hd (off : BitVec 64) : (Range.of (dst.add off) 256).Disjoint
      (Range.of ptr width) := Or.inl hne
  have hd0 : (Range.of dst 256).Disjoint (Range.of ptr width) := Or.inl hne
  rw [storeBlocks, MemoryState.readAt_storeAt_disjoint (hd 128),
    MemoryState.readAt_storeAt_disjoint (hd 96), MemoryState.readAt_storeAt_disjoint (hd 64),
    MemoryState.readAt_storeAt_disjoint (hd 32), MemoryState.readAt_storeAt_disjoint hd0]

theorem readAt_copyPointBytes_ne (m : MemoryState) (dst src ptr : Pointer)
    (width : Nat) (hne : dst.id ≠ ptr.id) :
    (copyPointBytes m dst src).readAt ptr width = m.readAt ptr width :=
  MemoryState.readAt_storeAt_disjoint (Or.inl hne) _

theorem packed_unflatten (m : MemoryState) (src : Pointer) (v : Blocks)
    (h : readBlocks m src = v) (k : Fin 5) :
    (Ty.vec 8 32).unflatten (m.readAt (src.add (BitVec.ofNat 64 (32*k.val))) 256) =
      Ty.wrap (v k) := by
  rw [Ty.unflatten_vec]
  change Ty.wrap (t := .vec 8 32) (readBlocks m src k) = _
  rw [h]

end Agave.Ed25519.Avx2PointAdd.Phases
