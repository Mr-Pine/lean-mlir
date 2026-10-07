import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.FinishOutput

/-! The actual finalizer's eight stores produce the common SHA digest bytes. -/
namespace Agave.Ed25519.Bridge.FiredancerSHAExecution.Finish
open LeanMLIR.RIR Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.SHA512 Agave.Ed25519.SHA512.Spec
open Agave.Ed25519.Verifier.Execution.Challenge
open Agave.Ed25519.Bridge.Challenge
open Agave.Ed25519.Verifier.Execution.SHA512Finalization (swapBytes)
set_option maxRecDepth 100000
set_option maxHeartbeats 2400000

private theorem splice_adjacent {n low high : Nat} (bytes : BitVec n) (off : Nat)
    (lo : BitVec low) (hi : BitVec high) :
    Memory.spliceBits (Memory.spliceBits bytes off lo) (off + low) hi =
      Memory.spliceBits bytes off (hi ++ lo) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi'
  simp only [Memory.getLsbD_spliceBits, BitVec.getLsbD_append]
  grind

def swappedState (s : State) : State :=
  ⟨swapBytes s.a, swapBytes s.b, swapBytes s.c, swapBytes s.d,
   swapBytes s.e, swapBytes s.f, swapBytes s.g, swapBytes s.h⟩

private theorem state_ext (x y : State)
    (ha : x.a = y.a)
    (hb : x.b = y.b)
    (hc : x.c = y.c)
    (hd : x.d = y.d)
    (he : x.e = y.e)
    (hf : x.f = y.f)
    (hg : x.g = y.g)
    (hh : x.h = y.h) : x = y := by
  cases x; cases y; simp_all

theorem pack_swappedState (s : State) : pack (swappedState s) = serialize (pack s) := by
  have h0 := serialize_word (pack s) 0 (by decide)
  have h1 := serialize_word (pack s) 1 (by decide)
  have h2 := serialize_word (pack s) 2 (by decide)
  have h3 := serialize_word (pack s) 3 (by decide)
  have h4 := serialize_word (pack s) 4 (by decide)
  have h5 := serialize_word (pack s) 5 (by decide)
  have h6 := serialize_word (pack s) 6 (by decide)
  have h7 := serialize_word (pack s) 7 (by decide)
  have hu : unpack (serialize (pack s)) = swappedState s := by
    apply state_ext
    · exact h0.trans (congrArg swapBytes (congrArg State.a (unpack_pack s)))
    · exact h1.trans (congrArg swapBytes (congrArg State.b (unpack_pack s)))
    · exact h2.trans (congrArg swapBytes (congrArg State.c (unpack_pack s)))
    · exact h3.trans (congrArg swapBytes (congrArg State.d (unpack_pack s)))
    · exact h4.trans (congrArg swapBytes (congrArg State.e (unpack_pack s)))
    · exact h5.trans (congrArg swapBytes (congrArg State.f (unpack_pack s)))
    · exact h6.trans (congrArg swapBytes (congrArg State.g (unpack_pack s)))
    · exact h7.trans (congrArg swapBytes (congrArg State.h (unpack_pack s)))
  rw [← hu, pack_unpack]

private theorem swapped_reassoc (s : State) :
    swapBytes s.h ++ (swapBytes s.g ++ (swapBytes s.f ++ (swapBytes s.e ++
      (swapBytes s.d ++ (swapBytes s.c ++ (swapBytes s.b ++ swapBytes s.a)))))) =
      pack (swappedState s) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [pack, swappedState, BitVec.getLsbD_append]
  grind

theorem outputMemory_eq (mem : MemoryState) (output : Pointer)
    (ho : SmallRange mem output 64) (s : State) :
    outputMemory mem output s = mem.storeAt output (serialize (pack s)) := by
  have h8 : (output.add 8#64).offsetInBits = output.offsetInBits + 64 := by
    simpa using Pointer.offsetInBits_add (ho.no_wrap (k := 8) (by decide))
  have h16 : (output.add 16#64).offsetInBits = output.offsetInBits + 128 := by
    simpa using Pointer.offsetInBits_add (ho.no_wrap (k := 16) (by decide))
  have h24 : (output.add 24#64).offsetInBits = output.offsetInBits + 192 := by
    simpa using Pointer.offsetInBits_add (ho.no_wrap (k := 24) (by decide))
  have h32 : (output.add 32#64).offsetInBits = output.offsetInBits + 256 := by
    simpa using Pointer.offsetInBits_add (ho.no_wrap (k := 32) (by decide))
  have h40 : (output.add 40#64).offsetInBits = output.offsetInBits + 320 := by
    simpa using Pointer.offsetInBits_add (ho.no_wrap (k := 40) (by decide))
  have h48 : (output.add 48#64).offsetInBits = output.offsetInBits + 384 := by
    simpa using Pointer.offsetInBits_add (ho.no_wrap (k := 48) (by decide))
  have h56 : (output.add 56#64).offsetInBits = output.offsetInBits + 448 := by
    simpa using Pointer.offsetInBits_add (ho.no_wrap (k := 56) (by decide))
  rw [← pack_swappedState]
  obtain ⟨block, hb, _, _⟩ := ho
  unfold outputMemory MemoryState.storeAt
  simp only [Pointer.add_id, hb, h8, h16, h24, h32, h40, h48, h56]
  simp only [MemoryState.getElem?_eq, Std.ExtHashMap.getElem?_insert_self]
  simp only [splice_adjacent, swapped_reassoc, MemoryState.mk.injEq]
  apply Std.ExtHashMap.ext_getElem?
  intro k
  by_cases hk : output.id = k <;> simp [Std.ExtHashMap.getElem?_insert, hk]

theorem outputMemory_bytes (mem : MemoryState) (output : Pointer)
    (ho : SmallRange mem output 64) (s : State) :
    readBytes (outputMemory mem output s) output 64 = bytesOf (n := 64) (serialize (pack s)) := by
  rw [outputMemory_eq mem output ho s]
  exact readBytes_storeAt_self mem output 64 ho _

end Agave.Ed25519.Bridge.FiredancerSHAExecution.Finish
