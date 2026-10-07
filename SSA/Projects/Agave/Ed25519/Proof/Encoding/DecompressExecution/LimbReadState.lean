import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.LimbMemory
import SSA.Projects.Agave.Ed25519.Proof.SerialPoint.CallMemory

/-! Whole-field read rules for the state-sealing tactics. The memory argument is
explicit so `mlir_read` can index writes and preserve complete word vectors.
Arithmetic functions in the stored values remain opaque.

For traces ending in a whole-field memcpy, use
`attribute [local mlir_read] storeLimbs_read320`: the scalar read-frame rules
then preserve its 320-bit read across disjoint stores. -/
namespace Agave.Ed25519.Encoding.Decompress.Execution
open LeanMLIR.RIR
open SerialFieldMul
open Reduce64.Execution (SmallRange)

/-- The five field limbs as a read with an explicit memory argument. -/
def readLimbMemory (m : MemoryState) (p : Pointer) : Fin 5 → BitVec 64 :=
  fun i => m.readAt (p.add (BitVec.ofNat 64 (8 * i.val))) 64

@[mlir_state] theorem readLimbs_memory (s : GlobalState) (p : Pointer) :
    readLimbs s p = readLimbMemory s.mem p := rfl

@[mlir_read] theorem readLimbMemory_storeLimbs (m : MemoryState) (p : Pointer)
    (v : Fin 5 → BitVec 64) (h : SmallRange m p 40) :
    readLimbMemory (storeLimbs m p v) p = v := by
  exact SerialPoint.Execution.readLimbs_storeLimbs ⟨⟨0⟩, m⟩ p v h

@[mlir_read] theorem readLimbMemory_storeLimbs_ne (m : MemoryState) (p q : Pointer)
    (v : Fin 5 → BitVec 64) (h : p.id ≠ q.id) :
    readLimbMemory (storeLimbs m p v) q = readLimbMemory m q := by
  exact SerialPoint.Execution.readLimbs_storeLimbs_ne ⟨⟨0⟩, m⟩ p q v h

@[mlir_read] theorem readLimbMemory_alloca {s : GlobalState} (hwf : s.WF)
    (h : SmallRange s.mem p 40) (bytes : Nat) :
    readLimbMemory (s.alloca bytes).mem p = readLimbMemory s.mem p := by
  funext i
  exact MemoryState.readAt_alloca hwf
    (h.fits_add (k := 8 * i.val) (count := 8) (by omega))

/-- A store to another object preserves the complete five-limb read. -/
@[mlir_read] theorem readLimbMemory_storeAt_ne (m : MemoryState) (p q : Pointer)
    (x : BitVec bits) (h : p.id ≠ q.id) :
    readLimbMemory (m.storeAt p x) q = readLimbMemory m q := by
  funext i
  exact MemoryState.readAt_storeAt_disjoint
    (show (Range.of p bits).Disjoint (Range.of (q.add (BitVec.ofNat 64 (8*i.val))) 64)
      from Or.inl h) x

/-- Erasure commutes with all five stores, leaving the stored arithmetic opaque. -/
theorem eraseFrom_storeLimbs (m : MemoryState) (p : Pointer)
    (v : Fin 5 → BitVec 64) (n : Nat) :
    (storeLimbs m p v).eraseFrom n = storeLimbs (m.eraseFrom n) p v := by
  simp only [storeLimbs, MemoryState.eraseFrom_storeAt]

/-- A complete field store in the erased frame disappears in one rewrite. -/
theorem eraseFrom_storeLimbs_fresh (m : MemoryState) (p : Pointer)
    (v : Fin 5 → BitVec 64) (n : Nat) (h : n ≤ p.id.id) :
    (storeLimbs m p v).eraseFrom n = m.eraseFrom n := by
  have ha (off : BitVec 64) : n ≤ (p.add off).id.id := h
  rw [eraseFrom_storeLimbs]
  simp only [storeLimbs,
    MemoryState.storeAt_eraseFrom_of_le h,
    MemoryState.storeAt_eraseFrom_of_le (ha 8),
    MemoryState.storeAt_eraseFrom_of_le (ha 16),
    MemoryState.storeAt_eraseFrom_of_le (ha 24),
    MemoryState.storeAt_eraseFrom_of_le (ha 32)]

end Agave.Ed25519.Encoding.Decompress.Execution
