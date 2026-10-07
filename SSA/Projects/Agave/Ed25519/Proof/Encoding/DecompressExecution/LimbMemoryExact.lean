import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.LimbMemory

/-! Equality of the actual five scalar stores and their packed field copy,
including all untouched bits and all other allocations. -/
namespace Agave.Ed25519.Encoding.Decompress.Execution
open LeanMLIR.RIR
open SerialFieldMul
open Reduce64.Execution (SmallRange)

theorem limbBytes_splices_at (old : BitVec width) (off : Nat)
    (a : Fin 5 → BitVec 64) :
    Memory.spliceBits (Memory.spliceBits (Memory.spliceBits
      (Memory.spliceBits (Memory.spliceBits old off (a 0)) (off + 64) (a 1))
        (off + 128) (a 2)) (off + 192) (a 3)) (off + 256) (a 4) =
      Memory.spliceBits old off (limbBytes a) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [Memory.getLsbD_spliceBits, limbBytes, BitVec.getLsbD_append]
  grind

set_option maxHeartbeats 2000000 in
/-- Exact equality is stronger than the whole-field readback theorem: in
particular it permits replacing the helper's final memcpy with five stores. -/
theorem storeLimbs_exact (m : MemoryState) (p : Pointer)
    (a : Fin 5 → BitVec 64) (h : SmallRange m p 40) :
    storeLimbs m p a = m.storeAt p (limbBytes a) := by
  obtain ⟨block, hb, hsmall, hfits⟩ := h
  have h : SmallRange m p 40 := ⟨block, hb, hsmall, hfits⟩
  have hoff (k : Nat) (hk : k ≤ 40) :
      (p.add (BitVec.ofNat 64 k)).offsetInBits = p.offsetInBits + k * 8 := by
    have hn : k < 2 ^ 64 := by omega
    simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn] using
      Pointer.offsetInBits_add (h.no_wrap (k := k) hk)
  apply MemoryState.ext
  apply Std.ExtHashMap.ext_getElem?
  intro q
  change (storeLimbs m p a)[q]? = (m.storeAt p (limbBytes a))[q]?
  by_cases hq : q = p.id
  · subst q
    have h0 := MemoryState.getElem?_storeAt_self (x := a 0) hb
    have h1 := MemoryState.getElem?_storeAt_self (p := p.add 8) (x := a 1) h0
    have h2 := MemoryState.getElem?_storeAt_self (p := p.add 16) (x := a 2) h1
    have h3 := MemoryState.getElem?_storeAt_self (p := p.add 24) (x := a 3) h2
    have h4 := MemoryState.getElem?_storeAt_self (p := p.add 32) (x := a 4) h3
    simp only [Pointer.add_id] at h1 h2 h3 h4
    simp only [storeLimbs, h4, MemoryState.getElem?_storeAt_self hb]
    congr 2
    have h8 := hoff 8 (by decide)
    have h16 := hoff 16 (by decide)
    have h24 := hoff 24 (by decide)
    have h32 := hoff 32 (by decide)
    norm_num only [Nat.reduceMul] at h8 h16 h24 h32
    erw [h8, h16, h24, h32]
    exact limbBytes_splices_at block.bytes p.offsetInBits a
  · have hn (k : BitVec 64) : (⟨q, 0⟩ : Pointer).id ≠ (p.add k).id := hq
    simp only [storeLimbs, MemoryState.getElem?_storeAt_ne (q := ⟨q, 0⟩) (hn 32),
      MemoryState.getElem?_storeAt_ne (q := ⟨q, 0⟩) (hn 24),
      MemoryState.getElem?_storeAt_ne (q := ⟨q, 0⟩) (hn 16),
      MemoryState.getElem?_storeAt_ne (q := ⟨q, 0⟩) (hn 8),
      MemoryState.getElem?_storeAt_ne (q := ⟨q, 0⟩) hq]

end Agave.Ed25519.Encoding.Decompress.Execution
