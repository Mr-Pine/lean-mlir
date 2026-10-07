import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.CoreEntry

/-! Exact native chaining-state byte observation after the core's eight stores. -/
namespace Agave.Ed25519.Bridge.FiredancerSHAExecution.Core
open LeanMLIR.RIR Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.SHA512 Agave.Ed25519.SHA512.Spec
open Agave.Ed25519.Verifier.Execution.Challenge
open Agave.Ed25519.Bridge.Challenge
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

private theorem splice_adjacent {n low high : Nat} (bytes : BitVec n) (off : Nat)
    (lo : BitVec low) (hi : BitVec high) :
    Memory.spliceBits (Memory.spliceBits bytes off lo) (off + low) hi =
      Memory.spliceBits bytes off (hi ++ lo) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi'
  simp only [Memory.getLsbD_spliceBits, BitVec.getLsbD_append]
  grind

private theorem pack_reassoc (s : State) :
    s.h ++ (s.g ++ (s.f ++ (s.e ++ (s.d ++ (s.c ++ (s.b ++ s.a)))))) = pack s := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [pack, BitVec.getLsbD_append]
  grind

theorem feedforwardMemory_eq (mem : MemoryState) (chain : Pointer)
    (hc : SmallRange mem chain 64) (s : State) :
    feedforwardMemory mem chain s = mem.storeAt chain (pack s) := by
  have h8 : (chain.add 8#64).offsetInBits = chain.offsetInBits + 64 := by
    simpa using Pointer.offsetInBits_add (hc.no_wrap (k := 8) (by decide))
  have h16 : (chain.add 16#64).offsetInBits = chain.offsetInBits + 128 := by
    simpa using Pointer.offsetInBits_add (hc.no_wrap (k := 16) (by decide))
  have h24 : (chain.add 24#64).offsetInBits = chain.offsetInBits + 192 := by
    simpa using Pointer.offsetInBits_add (hc.no_wrap (k := 24) (by decide))
  have h32 : (chain.add 32#64).offsetInBits = chain.offsetInBits + 256 := by
    simpa using Pointer.offsetInBits_add (hc.no_wrap (k := 32) (by decide))
  have h40 : (chain.add 40#64).offsetInBits = chain.offsetInBits + 320 := by
    simpa using Pointer.offsetInBits_add (hc.no_wrap (k := 40) (by decide))
  have h48 : (chain.add 48#64).offsetInBits = chain.offsetInBits + 384 := by
    simpa using Pointer.offsetInBits_add (hc.no_wrap (k := 48) (by decide))
  have h56 : (chain.add 56#64).offsetInBits = chain.offsetInBits + 448 := by
    simpa using Pointer.offsetInBits_add (hc.no_wrap (k := 56) (by decide))
  obtain ⟨block, hb, _, _⟩ := hc
  unfold feedforwardMemory MemoryState.storeAt
  simp only [Pointer.add_id, hb, h8, h16, h24, h32, h40, h48, h56]
  simp only [MemoryState.getElem?_eq, Std.ExtHashMap.getElem?_insert_self]
  simp only [splice_adjacent, pack_reassoc, MemoryState.mk.injEq]
  apply Std.ExtHashMap.ext_getElem?
  intro k
  by_cases hk : chain.id = k <;> simp [Std.ExtHashMap.getElem?_insert, hk]

theorem feedforwardMemory_read (mem : MemoryState) (chain : Pointer)
    (hc : SmallRange mem chain 64) (s : State) :
    (feedforwardMemory mem chain s).readAt chain 512 = pack s := by
  rw [feedforwardMemory_eq mem chain hc s]
  exact MemoryState.readAt_storeAt_self hc.fits _

theorem feedforwardMemory_bytes (mem : MemoryState) (chain : Pointer)
    (hc : SmallRange mem chain 64) (s : State) :
    readBytes (feedforwardMemory mem chain s) chain 64 = bytesOf (n := 64) (pack s) := by
  rw [feedforwardMemory_eq mem chain hc s]
  exact readBytes_storeAt_self mem chain 64 hc _

theorem chainMemory_of_packed (mem : MemoryState) (chain : Pointer)
    (hc : SmallRange mem chain 64) (s : State) (hread : mem.readAt chain 512 = pack s) :
    ChainMemory mem chain s := by
  have h0 := MemoryState.readAt_add_of_readAt (off := 0#64) hc.fits
    (hc.no_wrap (k := 0) (by decide)) (by decide : (0#64).toNat * 8 + 64 ≤ 512) hread
  have h8 := MemoryState.readAt_add_of_readAt (off := 8#64) hc.fits
    (hc.no_wrap (k := 8) (by decide)) (by decide : (8#64).toNat * 8 + 64 ≤ 512) hread
  have h16 := MemoryState.readAt_add_of_readAt (off := 16#64) hc.fits
    (hc.no_wrap (k := 16) (by decide)) (by decide : (16#64).toNat * 8 + 64 ≤ 512) hread
  have h24 := MemoryState.readAt_add_of_readAt (off := 24#64) hc.fits
    (hc.no_wrap (k := 24) (by decide)) (by decide : (24#64).toNat * 8 + 64 ≤ 512) hread
  have h32 := MemoryState.readAt_add_of_readAt (off := 32#64) hc.fits
    (hc.no_wrap (k := 32) (by decide)) (by decide : (32#64).toNat * 8 + 64 ≤ 512) hread
  have h40 := MemoryState.readAt_add_of_readAt (off := 40#64) hc.fits
    (hc.no_wrap (k := 40) (by decide)) (by decide : (40#64).toNat * 8 + 64 ≤ 512) hread
  have h48 := MemoryState.readAt_add_of_readAt (off := 48#64) hc.fits
    (hc.no_wrap (k := 48) (by decide)) (by decide : (48#64).toNat * 8 + 64 ≤ 512) hread
  have h56 := MemoryState.readAt_add_of_readAt (off := 56#64) hc.fits
    (hc.no_wrap (k := 56) (by decide)) (by decide : (56#64).toNat * 8 + 64 ≤ 512) hread
  constructor
  · exact (show mem.readAt chain 64 = (unpack (pack s)).a by
      simpa [unpack] using h0).trans (congrArg State.a (unpack_pack s))
  · exact (show mem.readAt (chain.add 8#64) 64 = (unpack (pack s)).b by
      simpa [unpack] using h8).trans (congrArg State.b (unpack_pack s))
  · exact (show mem.readAt (chain.add 16#64) 64 = (unpack (pack s)).c by
      simpa [unpack] using h16).trans (congrArg State.c (unpack_pack s))
  · exact (show mem.readAt (chain.add 24#64) 64 = (unpack (pack s)).d by
      simpa [unpack] using h24).trans (congrArg State.d (unpack_pack s))
  · exact (show mem.readAt (chain.add 32#64) 64 = (unpack (pack s)).e by
      simpa [unpack] using h32).trans (congrArg State.e (unpack_pack s))
  · exact (show mem.readAt (chain.add 40#64) 64 = (unpack (pack s)).f by
      simpa [unpack] using h40).trans (congrArg State.f (unpack_pack s))
  · exact (show mem.readAt (chain.add 48#64) 64 = (unpack (pack s)).g by
      simpa [unpack] using h48).trans (congrArg State.g (unpack_pack s))
  · exact (show mem.readAt (chain.add 56#64) 64 = (unpack (pack s)).h by
      simpa [unpack] using h56).trans (congrArg State.h (unpack_pack s))

theorem feedforwardMemory_chain (mem : MemoryState) (chain : Pointer)
    (hc : SmallRange mem chain 64) (s : State) :
    ChainMemory (feedforwardMemory mem chain s) chain s :=
  chainMemory_of_packed _ _ (feedforwardMemory_live s hc) s (feedforwardMemory_read mem chain hc s)

end Agave.Ed25519.Bridge.FiredancerSHAExecution.Core
