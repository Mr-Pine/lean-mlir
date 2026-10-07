import SSA.Projects.RIR.Run.Tactic
import Mathlib.Tactic.NormNum

namespace Agave.Ed25519.Reduce64.Execution
open LeanMLIR.RIR

section

/-- A live, small allocation containing the complete byte range. The small-allocation
condition is required by the emitted `inbounds nusw nuw` GEP semantics. -/
def SmallRange (m : MemoryState) (p : Pointer) (bytes : Nat) : Prop :=
  ∃ b, m[p.id]? = some b ∧ b.length < 2^63 ∧ p.offset.toNat + bytes ≤ b.length

theorem SmallRange.fits (h : SmallRange m p bytes) : Fits m p (8 * bytes) := by
  obtain ⟨b, hb, _, hsz⟩ := h
  exact ⟨b, hb, by simpa [Pointer.offsetInBits, MemoryBlock.lengthInBits, Nat.mul_add] using
    (Nat.mul_le_mul_left 8 hsz)⟩

theorem SmallRange.offset_lt (h : SmallRange m p bytes) : p.offset.toNat + bytes < 2^63 := by
  obtain ⟨b, _, hsmall, hsz⟩ := h
  omega

theorem SmallRange.no_wrap (h : SmallRange m p bytes) (hk : k ≤ bytes) :
    ¬p.offset.uaddOverflow (BitVec.ofNat 64 k) := by
  have hr := h.offset_lt
  have hk64 : k < 2^64 := by norm_num at hr ⊢; omega
  simp only [BitVec.uaddOverflow, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk64]
  norm_num at hr ⊢
  omega

theorem SmallRange.fits_add (h : SmallRange m p bytes) (hk : k + count ≤ bytes) :
    Fits m (p.add (BitVec.ofNat 64 k)) (8 * count) := by
  have hk64 : k < 2^64 := by have := h.offset_lt; norm_num at *; omega
  apply Fits.add_of_le (h.no_wrap (by omega)) _ h.fits
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk64]
  omega

theorem SmallRange.gep (h : SmallRange m p bytes) (hk : k ≤ bytes) :
    Operation.gepInboundsLive m (.value p) [.value (k : Int)] =
      .value (p.add (BitVec.ofNat 64 k)) := by
  obtain ⟨b, hb, hsmall, hsz⟩ := h
  have hwithin : (p.offset.toNat : Int) + (k : Int) ≤ b.length := by omega
  have hoff := Operation.gepInboundsOffsets_singleton hsmall (Int.ofNat_nonneg k) hwithin
  simpa using (Operation.gepInboundsLive_eq (offsets := [(k : Int)]) hb hsmall hoff)

/-- Stores preserve allocation identity and size, even when source and destination alias. -/
@[mlir_mem, mlir_transport]
theorem SmallRange.storeAt (h : SmallRange m p bytes) (q : Pointer) (x : BitVec w) :
    SmallRange (m.storeAt q x) p bytes := by
  obtain ⟨b, hb, hsmall, hsz⟩ := h
  by_cases heq : p.id = q.id
  · have hbq : m[q.id]? = some b := heq ▸ hb
    refine ⟨{ b with bytes := Memory.spliceBits b.bytes q.offsetInBits x }, ?_, hsmall, hsz⟩
    simpa only [heq] using MemoryState.getElem?_storeAt_self (x := x) hbq
  · exact ⟨b, by rw [MemoryState.getElem?_storeAt_ne heq]; exact hb, hsmall, hsz⟩

/-- The five output registers occupy separate 32-byte slices of the destination. -/
theorem SmallRange.disjoint_chunks (h : SmallRange m p bytes)
    (hi : 32 * i + 32 ≤ bytes) (hj : 32 * j + 32 ≤ bytes) (hne : i ≠ j) :
    (Range.of (p.add (BitVec.ofNat 64 (32 * i))) 256).Disjoint
      (Range.of (p.add (BitVec.ofNat 64 (32 * j))) 256) := by
  have hi64 : 32 * i < 2^64 := by have := h.offset_lt; norm_num at *; omega
  have hj64 : 32 * j < 2^64 := by have := h.offset_lt; norm_num at *; omega
  have hiOff := Pointer.offsetInBits_add (h.no_wrap (k := 32 * i) (by omega))
  have hjOff := Pointer.offsetInBits_add (h.no_wrap (k := 32 * j) (by omega))
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi64] at hiOff
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hj64] at hjOff
  simp only [Range.Disjoint, Range.of, Pointer.add_id, hiOff, hjOff]
  omega

end
end Agave.Ed25519.Reduce64.Execution
