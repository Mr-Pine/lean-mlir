import SSA.Projects.Agave.Ed25519.Proof.SerialPoint.CallMemory
import SSA.Projects.RIR.Run.Vector

namespace Agave.Ed25519.SerialPoint.Execution
open LeanMLIR.RIR
open Reduce64.Execution (SmallRange)

attribute [local implicit_reducible] Ty.width

/-- The serial double's two-lane loads select the same two little-endian words
as scalar loads. The allocation premise discharges both reads and pointer wrap. -/
@[mlir_read] theorem load_two_words (m : MemoryState) (p : Pointer)
    (h : SmallRange m p 16) :
    (Ty.vec 2 64).unflatten (m.readAt p 128) =
      #v[.value (m.readAt p 64), .value (m.readAt (p.add 8) 64)] := by
  have h0 : m.readAt p 64 = (m.readAt p 128).extractLsb' 0 64 := by
    simpa using (MemoryState.readAt_add_of_readAt (off := 0#64) (w := 64)
      h.fits (h.no_wrap (k := 0) (by decide)) (by decide) rfl)
  have h1 : m.readAt (p.add 8) 64 = (m.readAt p 128).extractLsb' 64 64 := by
    simpa using (MemoryState.readAt_add_of_readAt (off := 8#64) (w := 64)
      h.fits (h.no_wrap (k := 8) (by decide)) (by decide) rfl)
  apply Vector.ext
  intro i hi
  interval_cases i <;> simp [Ty.unflatten, Ty.extractVecElem, h0]
  exact h1.symm

@[simp, mlir_read] theorem packed_two_low (a b : BitVec 64) :
    (BitVec.packLanes #v[a, b]).extractLsb' 0 64 = a := by
  simpa using BitVec.extractLsb'_packLanes #v[a, b] 0 (by decide)

@[simp, mlir_read] theorem packed_two_high (a b : BitVec 64) :
    (BitVec.packLanes #v[a, b]).extractLsb' 64 64 = b := by
  simpa using BitVec.extractLsb'_packLanes #v[a, b] 1 (by decide)

end Agave.Ed25519.SerialPoint.Execution
