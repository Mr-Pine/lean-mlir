import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionAvx2Unpack
import SSA.Projects.Agave.Ed25519.Proof.Avx2PointAdd.PhaseRepresentation
import SSA.Projects.Agave.Ed25519.Proof.Avx2PointAdd.Refinement
import SSA.Projects.Agave.Ed25519.Proof.Conformance.BackendObservation

/-! Read back the eight stores of the actual AVX2 return block. -/
namespace Agave.Ed25519.DoubleBase.ExecutionAvx2
open LeanMLIR.RIR RIR Reduce64.Execution
open PointArithmetic
open Avx2PointAdd.Phases (packPoint)

private theorem unpack_offset_bits (h : SmallRange m r 160) (k : Nat) (hk : k ≤ 160) :
    (r.add (BitVec.ofNat 64 k)).offsetInBits = r.offsetInBits + k * 8 := by
  rw [Pointer.offsetInBits_add (h.no_wrap hk), BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega)]

private theorem unpack_disjoint (h : SmallRange m r 160)
    (start bytes word : Nat) (hs : start + bytes ≤ 160) (hw : word + 8 ≤ 160)
    (hsep : start + bytes ≤ word ∨ word + 8 ≤ start) :
    (Range.of (r.add (BitVec.ofNat 64 start)) (8 * bytes)).Disjoint
      (Range.of (r.add (BitVec.ofNat 64 word)) 64) := by
  simp only [Range.Disjoint, Range.of, Pointer.add_id,
    unpack_offset_bits h start (by omega), unpack_offset_bits h word (by omega)]
  omega

private theorem unpack_read_store (h : SmallRange m r 160)
    (start bytes word : Nat) (hs : start + bytes ≤ 160)
    (hle : start ≤ word) (hw : word + 8 ≤ start + bytes) (x : BitVec (8 * bytes)) :
    (m.storeAt (r.add (BitVec.ofNat 64 start)) x).readAt
      (r.add (BitVec.ofNat 64 word)) 64 = x.extractLsb' ((word - start) * 8) 64 := by
  have hoS := unpack_offset_bits h start (by omega)
  have hoW := unpack_offset_bits h word (by omega)
  rw [MemoryState.readAt_storeAt_subrange (q := r.add (BitVec.ofNat 64 word))
    (w' := 64) (h.fits_add hs) rfl
    (by omega) (by omega)]
  congr 1
  omega


set_option maxHeartbeats 2000000 in
/-- Every one of the twenty caller-visible words is the corresponding radix pair. -/
theorem unpackStore_word (m : MemoryState) (r : Pointer) (v : UnpackBlocks)
    (h : SmallRange m r 160) (coordinate : Fin 4) (limb : Fin 5) :
    (unpackStore m r v).readAt
      (r.add (BitVec.ofNat 64 (40 * coordinate.val + 8 * limb.val))) 64 =
      unpackSerial v coordinate limb := by
  let m1 : MemoryState := m.storeAt r (BitVec.packLanes #v[unpackPair (v 0)[0] (v 0)[2], unpackPair (v 1)[0] (v 1)[2]])
  have hm1 : SmallRange m1 r 160 := h.storeAt _ _
  let m2 : MemoryState := m1.storeAt (r.add 16#64) (BitVec.packLanes #v[unpackPair (v 2)[0] (v 2)[2], unpackPair (v 3)[0] (v 3)[2]])
  have hm2 : SmallRange m2 r 160 := hm1.storeAt _ _
  let m3 : MemoryState := m2.storeAt (r.add 32#64) (BitVec.packLanes #v[unpackPair (v 4)[0] (v 4)[2], unpackPair (v 0)[1] (v 0)[3], unpackPair (v 1)[1] (v 1)[3], unpackPair (v 2)[1] (v 2)[3]])
  have hm3 : SmallRange m3 r 160 := hm2.storeAt _ _
  let m4 : MemoryState := m3.storeAt (r.add 64#64) (unpackPair (v 3)[1] (v 3)[3])
  have hm4 : SmallRange m4 r 160 := hm3.storeAt _ _
  let m5 : MemoryState := m4.storeAt (r.add 72#64) (BitVec.packLanes #v[unpackPair (v 4)[1] (v 4)[3], unpackPair (v 0)[4] (v 0)[6], unpackPair (v 1)[4] (v 1)[6], unpackPair (v 2)[4] (v 2)[6]])
  have hm5 : SmallRange m5 r 160 := hm4.storeAt _ _
  let m6 : MemoryState := m5.storeAt (r.add 104#64) (BitVec.packLanes #v[unpackPair (v 3)[4] (v 3)[6], unpackPair (v 4)[4] (v 4)[6], unpackPair (v 0)[5] (v 0)[7], unpackPair (v 1)[5] (v 1)[7]])
  have hm6 : SmallRange m6 r 160 := hm5.storeAt _ _
  let m7 : MemoryState := m6.storeAt (r.add 136#64) (BitVec.packLanes #v[unpackPair (v 2)[5] (v 2)[7], unpackPair (v 3)[5] (v 3)[7]])
  have hm7 : SmallRange m7 r 160 := hm6.storeAt _ _
  have hf0 : Fits m r 128 := by
    simpa only [Pointer.add_zero] using h.fits_add (k := 0) (count := 16) (by decide)
  fin_cases coordinate <;> fin_cases limb
  · change (unpackStore m r v).readAt (r.add 0#64) 64 =
      unpackPair (v 0)[0] (v 0)[2]
    change (m7.storeAt (r.add 152#64) (unpackPair (v 4)[5] (v 4)[7])).readAt _ 64 = _
    rw [MemoryState.readAt_storeAt_disjoint
      (unpack_disjoint h 152 8 0 (by decide) (by decide) (Or.inr (by decide)))]
    rw [MemoryState.readAt_storeAt_disjoint
      (unpack_disjoint h 136 16 0 (by decide) (by decide) (Or.inr (by decide)))]
    rw [MemoryState.readAt_storeAt_disjoint
      (unpack_disjoint h 104 32 0 (by decide) (by decide) (Or.inr (by decide)))]
    rw [MemoryState.readAt_storeAt_disjoint
      (unpack_disjoint h 72 32 0 (by decide) (by decide) (Or.inr (by decide)))]
    rw [MemoryState.readAt_storeAt_disjoint
      (unpack_disjoint h 64 8 0 (by decide) (by decide) (Or.inr (by decide)))]
    rw [MemoryState.readAt_storeAt_disjoint
      (unpack_disjoint h 32 32 0 (by decide) (by decide) (Or.inr (by decide)))]
    rw [MemoryState.readAt_storeAt_disjoint
      (unpack_disjoint h 16 16 0 (by decide) (by decide) (Or.inr (by decide)))]
    rw [MemoryState.readAt_storeAt_add (off := 0#64) hf0
      (h.no_wrap (k := 0) (by decide)) (by decide)]
    exact BitVec.extractLsb'_packLanes _ 0 (by decide)
  · change (unpackStore m r v).readAt (r.add 8#64) 64 =
      unpackPair (v 1)[0] (v 1)[2]
    change (m7.storeAt (r.add 152#64) (unpackPair (v 4)[5] (v 4)[7])).readAt _ 64 = _
    rw [MemoryState.readAt_storeAt_disjoint
      (unpack_disjoint h 152 8 8 (by decide) (by decide) (Or.inr (by decide)))]
    rw [MemoryState.readAt_storeAt_disjoint
      (unpack_disjoint h 136 16 8 (by decide) (by decide) (Or.inr (by decide)))]
    rw [MemoryState.readAt_storeAt_disjoint
      (unpack_disjoint h 104 32 8 (by decide) (by decide) (Or.inr (by decide)))]
    rw [MemoryState.readAt_storeAt_disjoint
      (unpack_disjoint h 72 32 8 (by decide) (by decide) (Or.inr (by decide)))]
    rw [MemoryState.readAt_storeAt_disjoint
      (unpack_disjoint h 64 8 8 (by decide) (by decide) (Or.inr (by decide)))]
    rw [MemoryState.readAt_storeAt_disjoint
      (unpack_disjoint h 32 32 8 (by decide) (by decide) (Or.inr (by decide)))]
    rw [MemoryState.readAt_storeAt_disjoint
      (unpack_disjoint h 16 16 8 (by decide) (by decide) (Or.inr (by decide)))]
    rw [MemoryState.readAt_storeAt_add (off := 8#64) hf0
      (h.no_wrap (k := 8) (by decide)) (by decide)]
    exact BitVec.extractLsb'_packLanes _ 1 (by decide)
  · change (unpackStore m r v).readAt (r.add 16#64) 64 =
      unpackPair (v 2)[0] (v 2)[2]
    change (m7.storeAt (r.add 152#64) (unpackPair (v 4)[5] (v 4)[7])).readAt _ 64 = _
    rw [MemoryState.readAt_storeAt_disjoint
      (unpack_disjoint h 152 8 16 (by decide) (by decide) (Or.inr (by decide)))]
    rw [MemoryState.readAt_storeAt_disjoint
      (unpack_disjoint h 136 16 16 (by decide) (by decide) (Or.inr (by decide)))]
    rw [MemoryState.readAt_storeAt_disjoint
      (unpack_disjoint h 104 32 16 (by decide) (by decide) (Or.inr (by decide)))]
    rw [MemoryState.readAt_storeAt_disjoint
      (unpack_disjoint h 72 32 16 (by decide) (by decide) (Or.inr (by decide)))]
    rw [MemoryState.readAt_storeAt_disjoint
      (unpack_disjoint h 64 8 16 (by decide) (by decide) (Or.inr (by decide)))]
    rw [MemoryState.readAt_storeAt_disjoint
      (unpack_disjoint h 32 32 16 (by decide) (by decide) (Or.inr (by decide)))]
    rw [unpack_read_store hm1 16 16 16 (by decide) (by decide) (by decide)]
    simp only [Nat.reduceSub, Nat.reduceMul]
    exact BitVec.extractLsb'_packLanes _ 0 (by decide)
  · change (unpackStore m r v).readAt (r.add 24#64) 64 =
      unpackPair (v 3)[0] (v 3)[2]
    change (m7.storeAt (r.add 152#64) (unpackPair (v 4)[5] (v 4)[7])).readAt _ 64 = _
    rw [MemoryState.readAt_storeAt_disjoint
      (unpack_disjoint h 152 8 24 (by decide) (by decide) (Or.inr (by decide)))]
    rw [MemoryState.readAt_storeAt_disjoint
      (unpack_disjoint h 136 16 24 (by decide) (by decide) (Or.inr (by decide)))]
    rw [MemoryState.readAt_storeAt_disjoint
      (unpack_disjoint h 104 32 24 (by decide) (by decide) (Or.inr (by decide)))]
    rw [MemoryState.readAt_storeAt_disjoint
      (unpack_disjoint h 72 32 24 (by decide) (by decide) (Or.inr (by decide)))]
    rw [MemoryState.readAt_storeAt_disjoint
      (unpack_disjoint h 64 8 24 (by decide) (by decide) (Or.inr (by decide)))]
    rw [MemoryState.readAt_storeAt_disjoint
      (unpack_disjoint h 32 32 24 (by decide) (by decide) (Or.inr (by decide)))]
    rw [unpack_read_store hm1 16 16 24 (by decide) (by decide) (by decide)]
    simp only [Nat.reduceSub, Nat.reduceMul]
    exact BitVec.extractLsb'_packLanes _ 1 (by decide)
  · change (unpackStore m r v).readAt (r.add 32#64) 64 =
      unpackPair (v 4)[0] (v 4)[2]
    change (m7.storeAt (r.add 152#64) (unpackPair (v 4)[5] (v 4)[7])).readAt _ 64 = _
    rw [MemoryState.readAt_storeAt_disjoint
      (unpack_disjoint h 152 8 32 (by decide) (by decide) (Or.inr (by decide)))]
    rw [MemoryState.readAt_storeAt_disjoint
      (unpack_disjoint h 136 16 32 (by decide) (by decide) (Or.inr (by decide)))]
    rw [MemoryState.readAt_storeAt_disjoint
      (unpack_disjoint h 104 32 32 (by decide) (by decide) (Or.inr (by decide)))]
    rw [MemoryState.readAt_storeAt_disjoint
      (unpack_disjoint h 72 32 32 (by decide) (by decide) (Or.inr (by decide)))]
    rw [MemoryState.readAt_storeAt_disjoint
      (unpack_disjoint h 64 8 32 (by decide) (by decide) (Or.inr (by decide)))]
    rw [unpack_read_store hm2 32 32 32 (by decide) (by decide) (by decide)]
    simp only [Nat.reduceSub, Nat.reduceMul]
    exact BitVec.extractLsb'_packLanes _ 0 (by decide)
  · change (unpackStore m r v).readAt (r.add 40#64) 64 =
      unpackPair (v 0)[1] (v 0)[3]
    change (m7.storeAt (r.add 152#64) (unpackPair (v 4)[5] (v 4)[7])).readAt _ 64 = _
    rw [MemoryState.readAt_storeAt_disjoint
      (unpack_disjoint h 152 8 40 (by decide) (by decide) (Or.inr (by decide)))]
    rw [MemoryState.readAt_storeAt_disjoint
      (unpack_disjoint h 136 16 40 (by decide) (by decide) (Or.inr (by decide)))]
    rw [MemoryState.readAt_storeAt_disjoint
      (unpack_disjoint h 104 32 40 (by decide) (by decide) (Or.inr (by decide)))]
    rw [MemoryState.readAt_storeAt_disjoint
      (unpack_disjoint h 72 32 40 (by decide) (by decide) (Or.inr (by decide)))]
    rw [MemoryState.readAt_storeAt_disjoint
      (unpack_disjoint h 64 8 40 (by decide) (by decide) (Or.inr (by decide)))]
    rw [unpack_read_store hm2 32 32 40 (by decide) (by decide) (by decide)]
    simp only [Nat.reduceSub, Nat.reduceMul]
    exact BitVec.extractLsb'_packLanes _ 1 (by decide)
  · change (unpackStore m r v).readAt (r.add 48#64) 64 =
      unpackPair (v 1)[1] (v 1)[3]
    change (m7.storeAt (r.add 152#64) (unpackPair (v 4)[5] (v 4)[7])).readAt _ 64 = _
    rw [MemoryState.readAt_storeAt_disjoint
      (unpack_disjoint h 152 8 48 (by decide) (by decide) (Or.inr (by decide)))]
    rw [MemoryState.readAt_storeAt_disjoint
      (unpack_disjoint h 136 16 48 (by decide) (by decide) (Or.inr (by decide)))]
    rw [MemoryState.readAt_storeAt_disjoint
      (unpack_disjoint h 104 32 48 (by decide) (by decide) (Or.inr (by decide)))]
    rw [MemoryState.readAt_storeAt_disjoint
      (unpack_disjoint h 72 32 48 (by decide) (by decide) (Or.inr (by decide)))]
    rw [MemoryState.readAt_storeAt_disjoint
      (unpack_disjoint h 64 8 48 (by decide) (by decide) (Or.inr (by decide)))]
    rw [unpack_read_store hm2 32 32 48 (by decide) (by decide) (by decide)]
    simp only [Nat.reduceSub, Nat.reduceMul]
    exact BitVec.extractLsb'_packLanes _ 2 (by decide)
  · change (unpackStore m r v).readAt (r.add 56#64) 64 =
      unpackPair (v 2)[1] (v 2)[3]
    change (m7.storeAt (r.add 152#64) (unpackPair (v 4)[5] (v 4)[7])).readAt _ 64 = _
    rw [MemoryState.readAt_storeAt_disjoint
      (unpack_disjoint h 152 8 56 (by decide) (by decide) (Or.inr (by decide)))]
    rw [MemoryState.readAt_storeAt_disjoint
      (unpack_disjoint h 136 16 56 (by decide) (by decide) (Or.inr (by decide)))]
    rw [MemoryState.readAt_storeAt_disjoint
      (unpack_disjoint h 104 32 56 (by decide) (by decide) (Or.inr (by decide)))]
    rw [MemoryState.readAt_storeAt_disjoint
      (unpack_disjoint h 72 32 56 (by decide) (by decide) (Or.inr (by decide)))]
    rw [MemoryState.readAt_storeAt_disjoint
      (unpack_disjoint h 64 8 56 (by decide) (by decide) (Or.inr (by decide)))]
    rw [unpack_read_store hm2 32 32 56 (by decide) (by decide) (by decide)]
    simp only [Nat.reduceSub, Nat.reduceMul]
    exact BitVec.extractLsb'_packLanes _ 3 (by decide)
  · change (unpackStore m r v).readAt (r.add 64#64) 64 =
      unpackPair (v 3)[1] (v 3)[3]
    change (m7.storeAt (r.add 152#64) (unpackPair (v 4)[5] (v 4)[7])).readAt _ 64 = _
    rw [MemoryState.readAt_storeAt_disjoint
      (unpack_disjoint h 152 8 64 (by decide) (by decide) (Or.inr (by decide)))]
    rw [MemoryState.readAt_storeAt_disjoint
      (unpack_disjoint h 136 16 64 (by decide) (by decide) (Or.inr (by decide)))]
    rw [MemoryState.readAt_storeAt_disjoint
      (unpack_disjoint h 104 32 64 (by decide) (by decide) (Or.inr (by decide)))]
    rw [MemoryState.readAt_storeAt_disjoint
      (unpack_disjoint h 72 32 64 (by decide) (by decide) (Or.inr (by decide)))]
    rw [unpack_read_store hm3 64 8 64 (by decide) (by decide) (by decide)]
    simp only [Nat.reduceSub, Nat.reduceMul]
    simp
  · change (unpackStore m r v).readAt (r.add 72#64) 64 =
      unpackPair (v 4)[1] (v 4)[3]
    change (m7.storeAt (r.add 152#64) (unpackPair (v 4)[5] (v 4)[7])).readAt _ 64 = _
    rw [MemoryState.readAt_storeAt_disjoint
      (unpack_disjoint h 152 8 72 (by decide) (by decide) (Or.inr (by decide)))]
    rw [MemoryState.readAt_storeAt_disjoint
      (unpack_disjoint h 136 16 72 (by decide) (by decide) (Or.inr (by decide)))]
    rw [MemoryState.readAt_storeAt_disjoint
      (unpack_disjoint h 104 32 72 (by decide) (by decide) (Or.inr (by decide)))]
    rw [unpack_read_store hm4 72 32 72 (by decide) (by decide) (by decide)]
    simp only [Nat.reduceSub, Nat.reduceMul]
    exact BitVec.extractLsb'_packLanes _ 0 (by decide)
  · change (unpackStore m r v).readAt (r.add 80#64) 64 =
      unpackPair (v 0)[4] (v 0)[6]
    change (m7.storeAt (r.add 152#64) (unpackPair (v 4)[5] (v 4)[7])).readAt _ 64 = _
    rw [MemoryState.readAt_storeAt_disjoint
      (unpack_disjoint h 152 8 80 (by decide) (by decide) (Or.inr (by decide)))]
    rw [MemoryState.readAt_storeAt_disjoint
      (unpack_disjoint h 136 16 80 (by decide) (by decide) (Or.inr (by decide)))]
    rw [MemoryState.readAt_storeAt_disjoint
      (unpack_disjoint h 104 32 80 (by decide) (by decide) (Or.inr (by decide)))]
    rw [unpack_read_store hm4 72 32 80 (by decide) (by decide) (by decide)]
    simp only [Nat.reduceSub, Nat.reduceMul]
    exact BitVec.extractLsb'_packLanes _ 1 (by decide)
  · change (unpackStore m r v).readAt (r.add 88#64) 64 =
      unpackPair (v 1)[4] (v 1)[6]
    change (m7.storeAt (r.add 152#64) (unpackPair (v 4)[5] (v 4)[7])).readAt _ 64 = _
    rw [MemoryState.readAt_storeAt_disjoint
      (unpack_disjoint h 152 8 88 (by decide) (by decide) (Or.inr (by decide)))]
    rw [MemoryState.readAt_storeAt_disjoint
      (unpack_disjoint h 136 16 88 (by decide) (by decide) (Or.inr (by decide)))]
    rw [MemoryState.readAt_storeAt_disjoint
      (unpack_disjoint h 104 32 88 (by decide) (by decide) (Or.inr (by decide)))]
    rw [unpack_read_store hm4 72 32 88 (by decide) (by decide) (by decide)]
    simp only [Nat.reduceSub, Nat.reduceMul]
    exact BitVec.extractLsb'_packLanes _ 2 (by decide)
  · change (unpackStore m r v).readAt (r.add 96#64) 64 =
      unpackPair (v 2)[4] (v 2)[6]
    change (m7.storeAt (r.add 152#64) (unpackPair (v 4)[5] (v 4)[7])).readAt _ 64 = _
    rw [MemoryState.readAt_storeAt_disjoint
      (unpack_disjoint h 152 8 96 (by decide) (by decide) (Or.inr (by decide)))]
    rw [MemoryState.readAt_storeAt_disjoint
      (unpack_disjoint h 136 16 96 (by decide) (by decide) (Or.inr (by decide)))]
    rw [MemoryState.readAt_storeAt_disjoint
      (unpack_disjoint h 104 32 96 (by decide) (by decide) (Or.inr (by decide)))]
    rw [unpack_read_store hm4 72 32 96 (by decide) (by decide) (by decide)]
    simp only [Nat.reduceSub, Nat.reduceMul]
    exact BitVec.extractLsb'_packLanes _ 3 (by decide)
  · change (unpackStore m r v).readAt (r.add 104#64) 64 =
      unpackPair (v 3)[4] (v 3)[6]
    change (m7.storeAt (r.add 152#64) (unpackPair (v 4)[5] (v 4)[7])).readAt _ 64 = _
    rw [MemoryState.readAt_storeAt_disjoint
      (unpack_disjoint h 152 8 104 (by decide) (by decide) (Or.inr (by decide)))]
    rw [MemoryState.readAt_storeAt_disjoint
      (unpack_disjoint h 136 16 104 (by decide) (by decide) (Or.inr (by decide)))]
    rw [unpack_read_store hm5 104 32 104 (by decide) (by decide) (by decide)]
    simp only [Nat.reduceSub, Nat.reduceMul]
    exact BitVec.extractLsb'_packLanes _ 0 (by decide)
  · change (unpackStore m r v).readAt (r.add 112#64) 64 =
      unpackPair (v 4)[4] (v 4)[6]
    change (m7.storeAt (r.add 152#64) (unpackPair (v 4)[5] (v 4)[7])).readAt _ 64 = _
    rw [MemoryState.readAt_storeAt_disjoint
      (unpack_disjoint h 152 8 112 (by decide) (by decide) (Or.inr (by decide)))]
    rw [MemoryState.readAt_storeAt_disjoint
      (unpack_disjoint h 136 16 112 (by decide) (by decide) (Or.inr (by decide)))]
    rw [unpack_read_store hm5 104 32 112 (by decide) (by decide) (by decide)]
    simp only [Nat.reduceSub, Nat.reduceMul]
    exact BitVec.extractLsb'_packLanes _ 1 (by decide)
  · change (unpackStore m r v).readAt (r.add 120#64) 64 =
      unpackPair (v 0)[5] (v 0)[7]
    change (m7.storeAt (r.add 152#64) (unpackPair (v 4)[5] (v 4)[7])).readAt _ 64 = _
    rw [MemoryState.readAt_storeAt_disjoint
      (unpack_disjoint h 152 8 120 (by decide) (by decide) (Or.inr (by decide)))]
    rw [MemoryState.readAt_storeAt_disjoint
      (unpack_disjoint h 136 16 120 (by decide) (by decide) (Or.inr (by decide)))]
    rw [unpack_read_store hm5 104 32 120 (by decide) (by decide) (by decide)]
    simp only [Nat.reduceSub, Nat.reduceMul]
    exact BitVec.extractLsb'_packLanes _ 2 (by decide)
  · change (unpackStore m r v).readAt (r.add 128#64) 64 =
      unpackPair (v 1)[5] (v 1)[7]
    change (m7.storeAt (r.add 152#64) (unpackPair (v 4)[5] (v 4)[7])).readAt _ 64 = _
    rw [MemoryState.readAt_storeAt_disjoint
      (unpack_disjoint h 152 8 128 (by decide) (by decide) (Or.inr (by decide)))]
    rw [MemoryState.readAt_storeAt_disjoint
      (unpack_disjoint h 136 16 128 (by decide) (by decide) (Or.inr (by decide)))]
    rw [unpack_read_store hm5 104 32 128 (by decide) (by decide) (by decide)]
    simp only [Nat.reduceSub, Nat.reduceMul]
    exact BitVec.extractLsb'_packLanes _ 3 (by decide)
  · change (unpackStore m r v).readAt (r.add 136#64) 64 =
      unpackPair (v 2)[5] (v 2)[7]
    change (m7.storeAt (r.add 152#64) (unpackPair (v 4)[5] (v 4)[7])).readAt _ 64 = _
    rw [MemoryState.readAt_storeAt_disjoint
      (unpack_disjoint h 152 8 136 (by decide) (by decide) (Or.inr (by decide)))]
    rw [unpack_read_store hm6 136 16 136 (by decide) (by decide) (by decide)]
    simp only [Nat.reduceSub, Nat.reduceMul]
    exact BitVec.extractLsb'_packLanes _ 0 (by decide)
  · change (unpackStore m r v).readAt (r.add 144#64) 64 =
      unpackPair (v 3)[5] (v 3)[7]
    change (m7.storeAt (r.add 152#64) (unpackPair (v 4)[5] (v 4)[7])).readAt _ 64 = _
    rw [MemoryState.readAt_storeAt_disjoint
      (unpack_disjoint h 152 8 144 (by decide) (by decide) (Or.inr (by decide)))]
    rw [unpack_read_store hm6 136 16 144 (by decide) (by decide) (by decide)]
    simp only [Nat.reduceSub, Nat.reduceMul]
    exact BitVec.extractLsb'_packLanes _ 1 (by decide)
  · change (unpackStore m r v).readAt (r.add 152#64) 64 =
      unpackPair (v 4)[5] (v 4)[7]
    change (m7.storeAt (r.add 152#64) (unpackPair (v 4)[5] (v 4)[7])).readAt _ 64 = _
    rw [unpack_read_store hm7 152 8 152 (by decide) (by decide) (by decide)]
    simp only [Nat.reduceSub, Nat.reduceMul]
    simp

private theorem unpack_word_toNat {a : Avx2FieldMul.Limbs}
    (ha : Avx2PointAdd.reduced a) (i : Fin 10) :
    (Avx2PointAdd.word (a i)).toNat = a i := by
  have hi := (Avx2PointAdd.wide_input_safety (Avx2PointAdd.reduced_wide ha) i).1
  simp only [Avx2PointAdd.word, BitVec.toNat_ofNat]
  apply Nat.mod_eq_of_lt
  omega

private theorem unpack_decode_even_odd (a : Avx2FieldMul.Limbs) :
    Field.decode2625 (fun k => a (Avx2PointAdd.Phases.evenIndex k))
      (fun k => a (Avx2PointAdd.Phases.oddIndex k)) = Field.decode10 a := by
  rw [← Field.decode_flatten]
  congr 1
  funext i
  fin_cases i <;> rfl

/-- The packed register representation retains the exact integer coordinates. -/
theorem packedValue_packPoint {P : Avx2PointAdd.Point}
    (hP : Avx2PointAdd.pointReduced P) (coordinate : Fin 4) :
    Field.packedValue (fun k j => (packPoint P k)[j]) coordinate =
      Field.decode10 (![P.X, P.Y, P.Z, P.T] coordinate) := by
  fin_cases coordinate
  · change Field.decode2625
        (fun k => (Avx2PointAdd.word (P.X (Avx2PointAdd.Phases.evenIndex k))).toNat)
        (fun k => (Avx2PointAdd.word (P.X (Avx2PointAdd.Phases.oddIndex k))).toNat) =
      Field.decode10 P.X
    simp only [unpack_word_toNat hP.1]
    exact unpack_decode_even_odd _
  · change Field.decode2625
        (fun k => (Avx2PointAdd.word (P.Y (Avx2PointAdd.Phases.evenIndex k))).toNat)
        (fun k => (Avx2PointAdd.word (P.Y (Avx2PointAdd.Phases.oddIndex k))).toNat) =
      Field.decode10 P.Y
    simp only [unpack_word_toNat hP.2.1]
    exact unpack_decode_even_odd _
  · change Field.decode2625
        (fun k => (Avx2PointAdd.word (P.Z (Avx2PointAdd.Phases.evenIndex k))).toNat)
        (fun k => (Avx2PointAdd.word (P.Z (Avx2PointAdd.Phases.oddIndex k))).toNat) =
      Field.decode10 P.Z
    simp only [unpack_word_toNat hP.2.2.1]
    exact unpack_decode_even_odd _
  · change Field.decode2625
        (fun k => (Avx2PointAdd.word (P.T (Avx2PointAdd.Phases.evenIndex k))).toNat)
        (fun k => (Avx2PointAdd.word (P.T (Avx2PointAdd.Phases.oddIndex k))).toNat) =
      Field.decode10 P.T
    simp only [unpack_word_toNat hP.2.2.2]
    exact unpack_decode_even_odd _

/-- The actual store trace returns the field point represented by its five SIMD registers. -/
theorem unpackStore_readPoint (s : GlobalState) (r : Pointer) (P : Avx2PointAdd.Point)
    (h : SmallRange s.mem r 160) (hP : Avx2PointAdd.pointReduced P) :
    Conformance.BackendExecution.readPoint
        {s with mem := unpackStore s.mem r (packPoint P)} r =
      Avx2PointAdd.pointValue P := by
  have hc (c : Fin 4) :
      Conformance.BackendExecution.readCoordinate
          {s with mem := unpackStore s.mem r (packPoint P)} r c =
        Avx2PointAdd.value (![P.X, P.Y, P.Z, P.T] c) := by
    unfold Conformance.BackendExecution.readCoordinate
    simp only [unpackStore_word s.mem r (packPoint P) h,
      unpackSerial_value, packedValue_packPoint hP, Avx2PointAdd.value]
    rfl
  ext <;> exact hc _

end Agave.Ed25519.DoubleBase.ExecutionAvx2
