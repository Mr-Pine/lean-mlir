import SSA.Projects.Agave.Ed25519.Proof.SerialPoint.ExecutionMemory
import SSA.Projects.Agave.Ed25519.Proof.Verifier.DalekIdentityMemory

/-! Whole-field readback of the exact five scalar stores. This module concerns
the in-memory five-u64 representation, before canonical byte serialization. -/
namespace Agave.Ed25519.Encoding.Decompress.Execution
open LeanMLIR.RIR
open SerialFieldMul
open Reduce64.Execution (SmallRange)

def limbBytes (a : Fin 5 → BitVec 64) : BitVec 320 :=
  a 4 ++ a 3 ++ a 2 ++ a 1 ++ a 0

theorem limbBytes_extract (a : Fin 5 → BitVec 64) (i : Fin 5) :
    (limbBytes a).extractLsb' (64 * i.val) 64 = a i := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  fin_cases i <;>
    simp only [limbBytes, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append]
  all_goals grind

/-- A whole-field byte read determines every scalar field-kernel input. -/
theorem readLimbs_of_limbBytes (s : GlobalState) (p : Pointer)
    (a : Fin 5 → BitVec 64) (h : SmallRange s.mem p 40)
    (hread : s.mem.readAt p 320 = limbBytes a) : readLimbs s p = a := by
  funext i
  have hi : 8 * i.val < 18446744073709551616 := by omega
  have hp := MemoryState.readAt_add_of_readAt (off := BitVec.ofNat 64 (8 * i.val))
    (w := 64) h.fits (h.no_wrap (k := 8 * i.val) (by omega))
    (by simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi]; omega) hread
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi] at hp
  have heq : readLimbs s p i = (limbBytes a).extractLsb' (64 * i.val) 64 := by
    simpa only [readLimbs,
      Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hp
  exact heq.trans (limbBytes_extract a i)

theorem limbBytes_splices (old : BitVec 320) (a : Fin 5 → BitVec 64) :
    Memory.spliceBits (Memory.spliceBits (Memory.spliceBits
      (Memory.spliceBits (Memory.spliceBits old 0 (a 0)) 64 (a 1))
        128 (a 2)) 192 (a 3)) 256 (a 4) = limbBytes a := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [Memory.getLsbD_spliceBits, limbBytes, BitVec.getLsbD_append]
  grind

/-- A single 320-bit memcpy sees exactly the five field-kernel result stores. -/
theorem storeLimbs_read320 (m : MemoryState) (p : Pointer)
    (a : Fin 5 → BitVec 64) (h : SmallRange m p 40) :
    (storeLimbs m p a).readAt p 320 = limbBytes a := by
  have h0 := MemoryState.readAt_add_storeAt (p := p) (off := 0#64)
    (v := 320) h.fits (h.no_wrap (k := 0) (by decide)) (by decide) (a 0)
  have h8 := MemoryState.readAt_add_storeAt (p := p) (off := 8#64)
    (v := 320) (m := m.storeAt p (a 0)) h.fits.storeAt
    (h.no_wrap (k := 8) (by decide)) (by decide) (a 1)
  have h16 := MemoryState.readAt_add_storeAt (p := p) (off := 16#64)
    (v := 320) (m := (m.storeAt p (a 0)).storeAt (p.add 8) (a 1))
    h.fits.storeAt.storeAt (h.no_wrap (k := 16) (by decide)) (by decide) (a 2)
  have h24 := MemoryState.readAt_add_storeAt (p := p) (off := 24#64)
    (v := 320) (m := ((m.storeAt p (a 0)).storeAt (p.add 8) (a 1)).storeAt
      (p.add 16) (a 2)) h.fits.storeAt.storeAt.storeAt
    (h.no_wrap (k := 24) (by decide)) (by decide) (a 3)
  have h32 := MemoryState.readAt_add_storeAt (p := p) (off := 32#64)
    (v := 320) (m := (((m.storeAt p (a 0)).storeAt (p.add 8) (a 1)).storeAt
      (p.add 16) (a 2)).storeAt (p.add 24) (a 3))
    h.fits.storeAt.storeAt.storeAt.storeAt
    (h.no_wrap (k := 32) (by decide)) (by decide) (a 4)
  simp only [Pointer.add_zero, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod,
    Nat.zero_mul, Nat.reduceMul] at h0 h8 h16 h24 h32
  unfold storeLimbs
  erw [h32, h24, h16, h8, h0]
  exact limbBytes_splices _ a

theorem storeLimbs_readBytes (s : GlobalState) (p : Pointer)
    (a : Fin 5 → BitVec 64) (h : SmallRange s.mem p 40) :
    Verifier.Execution.Dalek.ReadBytes
      {s with mem := storeLimbs s.mem p a} p 40 (limbBytes a) :=
  ⟨((((h.storeAt p (a 0)).storeAt (p.add 8) (a 1)).storeAt
      (p.add 16) (a 2)).storeAt (p.add 24) (a 3)).storeAt (p.add 32) (a 4),
    storeLimbs_read320 s.mem p a h⟩

/-- The decoder's vector carry/sign blocks store limbs1/2, then limb0, then3/4. -/
def storeVectorLimbs (m : MemoryState) (p : Pointer) (a : Fin 5 → BitVec 64) : MemoryState :=
  ((m.storeAt (p.add 8#64) (a 2 ++ a 1)).storeAt p (a 0)).storeAt
    (p.add 24#64) (a 4 ++ a 3)

theorem vectorLimb_splices (old : BitVec 320) (a : Fin 5 → BitVec 64) :
    Memory.spliceBits (Memory.spliceBits (Memory.spliceBits old 64 (a 2 ++ a 1))
      0 (a 0)) 192 (a 4 ++ a 3) = limbBytes a := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [Memory.getLsbD_spliceBits, limbBytes, BitVec.getLsbD_append]
  grind

theorem storeVectorLimbs_read320 (m : MemoryState) (p : Pointer)
    (a : Fin 5 → BitVec 64) (h : SmallRange m p 40) :
    (storeVectorLimbs m p a).readAt p 320 = limbBytes a := by
  have h8 := MemoryState.readAt_add_storeAt (p := p) (off := 8#64)
    (v := 320) h.fits (h.no_wrap (k := 8) (by decide)) (by decide) (a 2 ++ a 1)
  have h0 := MemoryState.readAt_add_storeAt (p := p) (off := 0#64)
    (v := 320) (m := m.storeAt (p.add 8#64) (a 2 ++ a 1))
    h.fits.storeAt (h.no_wrap (k := 0) (by decide)) (by decide) (a 0)
  have h24 := MemoryState.readAt_add_storeAt (p := p) (off := 24#64)
    (v := 320) (m := (m.storeAt (p.add 8#64) (a 2 ++ a 1)).storeAt p (a 0))
    h.fits.storeAt.storeAt (h.no_wrap (k := 24) (by decide)) (by decide) (a 4 ++ a 3)
  simp only [Pointer.add_zero, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod,
    Nat.zero_mul, Nat.reduceMul] at h8 h0 h24
  simp only [storeVectorLimbs, h24, h0, h8, vectorLimb_splices]

theorem storeVectorLimbs_readLimbs (s : GlobalState) (p : Pointer)
    (a : Fin 5 → BitVec 64) (h : SmallRange s.mem p 40) :
    readLimbs {s with mem := storeVectorLimbs s.mem p a} p = a :=
  readLimbs_of_limbBytes _ p a (((h.storeAt _ _).storeAt _ _).storeAt _ _)
    (storeVectorLimbs_read320 s.mem p a h)

end Agave.Ed25519.Encoding.Decompress.Execution
