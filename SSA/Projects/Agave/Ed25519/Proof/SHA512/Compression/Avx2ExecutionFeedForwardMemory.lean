import SSA.Projects.Agave.Ed25519.Proof.Reduce64.Execution.Memory

/-! Adjacent vector accesses implement one complete SHA-512 chaining-state access. -/
set_option maxRecDepth 5000

namespace Agave.Ed25519.SHA512.Execution.Avx2

open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution

private theorem splice_adjacent {n : Nat} (bytes : BitVec n) (off : Nat)
    (lo hi : BitVec 256) :
    Memory.spliceBits (Memory.spliceBits bytes off lo) (off + 256) hi =
      Memory.spliceBits bytes off (hi ++ lo) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi'
  simp only [Memory.getLsbD_spliceBits, BitVec.getLsbD_append]
  grind

/-- The emitted low and high vector stores equal the full chaining-state store. -/
theorem store_pair (m : MemoryState) (chain : Pointer)
    (h : SmallRange m chain 64) (lo hi : BitVec 256) :
    (m.storeAt chain lo).storeAt (chain.add 32#64) hi =
      m.storeAt chain (hi ++ lo) := by
  have hoff : (chain.add 32#64).offsetInBits = chain.offsetInBits + 256 := by
    simpa using Pointer.offsetInBits_add (h.no_wrap (k := 32) (by decide))
  obtain ⟨block, hb, _, _⟩ := h
  unfold MemoryState.storeAt
  simp only [Pointer.add_id, hb, hoff]
  simp only [MemoryState.getElem?_eq, Std.ExtHashMap.getElem?_insert_self]
  simp only [splice_adjacent, MemoryState.mk.injEq]
  apply Std.ExtHashMap.ext_getElem?
  intro k
  by_cases hk : chain.id = k <;> simp [Std.ExtHashMap.getElem?_insert, hk]

/-- The first vector load reads the low half of the complete chaining state. -/
theorem read_low256 (m : MemoryState) (chain : Pointer)
    (h : SmallRange m chain 64) :
    m.readAt chain 256 = (m.readAt chain 512).extractLsb' 0 256 := by
  have hh := MemoryState.readAt_add_of_readAt (off := 0#64) (w := 256)
    h.fits (h.no_wrap (k := 0) (by decide)) (by decide) rfl
  simpa [Pointer.add] using hh

/-- The second vector load reads the high half of the complete chaining state. -/
theorem read_high256 (m : MemoryState) (chain : Pointer)
    (h : SmallRange m chain 64) :
    m.readAt (chain.add 32#64) 256 = (m.readAt chain 512).extractLsb' 256 256 := by
  simpa using MemoryState.readAt_add_of_readAt (off := 32#64) (w := 256)
    h.fits (h.no_wrap (k := 32) (by decide)) (by decide) rfl

end Agave.Ed25519.SHA512.Execution.Avx2
