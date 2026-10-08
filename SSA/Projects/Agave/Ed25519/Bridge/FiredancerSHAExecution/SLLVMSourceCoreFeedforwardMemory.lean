import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSourceCoreMemory

namespace Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.Core
open LeanMLIR SLLVM Firedancer
open Agave.Ed25519.SHA512.Spec
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def feedforwardMemory (m : MemoryState) (p : Pointer) (s : State) : MemoryState :=
  let m := m.splice p s.a
  let m := m.splice (p.withOffset 8#64) s.b
  let m := m.splice (p.withOffset 16#64) s.c
  let m := m.splice (p.withOffset 24#64) s.d
  let m := m.splice (p.withOffset 32#64) s.e
  let m := m.splice (p.withOffset 40#64) s.f
  let m := m.splice (p.withOffset 48#64) s.g
  m.splice (p.withOffset 56#64) s.h

theorem feedforward_offset {m : MemoryState} {p : Pointer} {bytes k : Nat} (h : SmallRange m p bytes) (hk : k ≤ bytes) :
    (p.withOffset (BitVec.ofNat 64 k)).offsetInBits = p.offsetInBits + 8*k := by
  have hb := h.offset_lt
  have hk64 : k < 2^64 := by omega
  have hsum : p.offset.toNat + k < 2^64 := by omega
  simp only [Pointer.offsetInBits, Pointer.withOffset, BitVec.toNat_add,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk64, Nat.mod_eq_of_lt hsum, Nat.mul_add]

theorem feedforward_data_no_wrap {m : MemoryState} {data : Pointer} (h : SmallRange m data 128) :
    (data.withOffset 128#64).offset.toNat = data.offset.toNat + 128 := by
  have hb := h.offset_lt
  have hsum : data.offset.toNat + 128 < 2^64 := by omega
  simpa only [Pointer.withOffset, BitVec.toNat_add, BitVec.toNat_ofNat] using
    Nat.mod_eq_of_lt hsum

private theorem pack_reassoc (s : State) :
    s.h ++ (s.g ++ (s.f ++ (s.e ++ (s.d ++ (s.c ++ (s.b ++ s.a)))))) = pack s := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [pack, BitVec.getLsbD_append]
  grind

theorem feedforwardMemory_live (m : MemoryState) (chain : Pointer)
    (hc : SmallRange m chain 64) (s : State) (q : BlockId) :
    (feedforwardMemory m chain s).live? q = (m.splice chain (pack s)).live? q := by
  have h8 := feedforward_offset hc (k := 8) (by decide)
  have h16 := feedforward_offset hc (k := 16) (by decide)
  have h24 := feedforward_offset hc (k := 24) (by decide)
  have h32 := feedforward_offset hc (k := 32) (by decide)
  have h40 := feedforward_offset hc (k := 40) (by decide)
  have h48 := feedforward_offset hc (k := 48) (by decide)
  have h56 := feedforward_offset hc (k := 56) (by decide)
  obtain ⟨b, hb, _, _⟩ := hc
  unfold feedforwardMemory
  by_cases hq : chain.id = q
  · subst q
    have h0 := splicedLive m chain b hb s.a
    have h1 := splicedLive _ (chain.withOffset 8#64) _ h0 s.b
    have h2 := splicedLive _ (chain.withOffset 16#64) _ h1 s.c
    have h3 := splicedLive _ (chain.withOffset 24#64) _ h2 s.d
    have h4 := splicedLive _ (chain.withOffset 32#64) _ h3 s.e
    have h5 := splicedLive _ (chain.withOffset 40#64) _ h4 s.f
    have h6 := splicedLive _ (chain.withOffset 48#64) _ h5 s.g
    have h7 := splicedLive _ (chain.withOffset 56#64) _ h6 s.h
    refine h7.trans ?_
    rw [splicedLive m chain b hb (pack s)]
    simp only [h8, h16, h24, h32, h40, h48, h56, spliceBits_append, pack_reassoc]
  · simp only [live?_splice_ne (p := chain) hq,
      live?_splice_ne (p := chain.withOffset 8#64) hq,
      live?_splice_ne (p := chain.withOffset 16#64) hq,
      live?_splice_ne (p := chain.withOffset 24#64) hq,
      live?_splice_ne (p := chain.withOffset 32#64) hq,
      live?_splice_ne (p := chain.withOffset 40#64) hq,
      live?_splice_ne (p := chain.withOffset 48#64) hq,
      live?_splice_ne (p := chain.withOffset 56#64) hq]


end Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.Core
