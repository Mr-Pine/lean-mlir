import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullBase

/-! Eight emitted scalar stores assemble the complete native chaining state. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 1800000

namespace Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Spec

private theorem splice_adjacent {n low high : Nat} (bytes : BitVec n) (off : Nat)
    (lo : BitVec low) (hi : BitVec high) :
    Memory.spliceBits (Memory.spliceBits bytes off lo) (off + low) hi =
      Memory.spliceBits bytes off (hi ++ lo) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi'
  simp only [Memory.getLsbD_spliceBits, BitVec.getLsbD_append]
  grind

private theorem splice_leading {n low high : Nat} (bytes : BitVec n) (off : Nat)
    (lo : BitVec low) (hi : BitVec high) :
    Memory.spliceBits (Memory.spliceBits bytes (off + low) hi) off lo =
      Memory.spliceBits bytes off (hi ++ lo) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi'
  simp only [Memory.getLsbD_spliceBits, BitVec.getLsbD_append]
  grind

def storeMem (mem : MemoryState) (chain : Pointer) (s : Spec.State) : MemoryState :=
  let m1 := mem.storeAt (chain.add 8#64) s.b
  let m2 := m1.storeAt (chain.add 16#64) s.c
  let m3 := m2.storeAt (chain.add 24#64) s.d
  let m4 := m3.storeAt (chain.add 32#64) s.e
  let m5 := m4.storeAt (chain.add 40#64) s.f
  let m6 := m5.storeAt (chain.add 48#64) s.g
  let m7 := m6.storeAt (chain.add 56#64) s.h
  m7.storeAt chain s.a

private theorem pack_reassoc (s : Spec.State) :
    s.h ++ (s.g ++ (s.f ++ (s.e ++ (s.d ++ (s.c ++ s.b))))) ++ s.a = Spec.pack s := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [Spec.pack, BitVec.getLsbD_append]
  grind

theorem storeMem_eq (mem : MemoryState) (chain : Pointer)
    (hc : SmallRange mem chain 64) (s : Spec.State) :
    storeMem mem chain s = mem.storeAt chain (Spec.pack s) := by
  have h8 : (chain.add 8#64).offsetInBits = chain.offsetInBits + 64 := by
    simpa using Pointer.offsetInBits_add (hc.no_wrap (k := 8) (by decide))
  have h16 : (chain.add 16#64).offsetInBits = (chain.offsetInBits + 64) + 64 := by
    simpa [Nat.add_assoc] using Pointer.offsetInBits_add (hc.no_wrap (k := 16) (by decide))
  have h24 : (chain.add 24#64).offsetInBits = (chain.offsetInBits + 64) + 128 := by
    simpa [Nat.add_assoc] using Pointer.offsetInBits_add (hc.no_wrap (k := 24) (by decide))
  have h32 : (chain.add 32#64).offsetInBits = (chain.offsetInBits + 64) + 192 := by
    simpa [Nat.add_assoc] using Pointer.offsetInBits_add (hc.no_wrap (k := 32) (by decide))
  have h40 : (chain.add 40#64).offsetInBits = (chain.offsetInBits + 64) + 256 := by
    simpa [Nat.add_assoc] using Pointer.offsetInBits_add (hc.no_wrap (k := 40) (by decide))
  have h48 : (chain.add 48#64).offsetInBits = (chain.offsetInBits + 64) + 320 := by
    simpa [Nat.add_assoc] using Pointer.offsetInBits_add (hc.no_wrap (k := 48) (by decide))
  have h56 : (chain.add 56#64).offsetInBits = (chain.offsetInBits + 64) + 384 := by
    simpa [Nat.add_assoc] using Pointer.offsetInBits_add (hc.no_wrap (k := 56) (by decide))
  obtain ⟨block, hb, _, _⟩ := hc
  unfold storeMem MemoryState.storeAt
  simp only [Pointer.add_id, hb, h8, h16, h24, h32, h40, h48, h56]
  simp only [MemoryState.getElem?_eq, Std.ExtHashMap.getElem?_insert_self]
  simp only [splice_adjacent, splice_leading, pack_reassoc, MemoryState.mk.injEq]
  apply Std.ExtHashMap.ext_getElem?
  intro k
  by_cases hk : chain.id = k <;> simp [Std.ExtHashMap.getElem?_insert, hk]

end Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
