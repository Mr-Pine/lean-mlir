import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.Memory

/-! Exact memory equality for 32 ascending byte stores. This strengthens byte
readback to equality of all blocks, their lengths, and every untouched bit. -/
namespace Agave.Ed25519.Verifier.Execution.ScalarWide
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution (SmallRange)
open Agave.Ed25519.ScalarReduce32.Execution (storePrefix storeBytes)

/-- Bit-level version of the actual ascending store prefix. -/
def spliceBytePrefix (old : BitVec width) (off : Nat) (bits : BitVec 256) : Nat → BitVec width
  | 0 => old
  | n + 1 => Memory.spliceBits (spliceBytePrefix old off bits n) (off + n * 8)
      (bits.extractLsb' (8 * n) 8)

theorem spliceBytePrefix_bit (old : BitVec width) (off : Nat) (bits : BitVec 256)
    (n : Nat) (hn : n ≤ 32) (i : Nat) :
    (spliceBytePrefix old off bits n).getLsbD i =
      if off ≤ i ∧ i < off + n * 8 ∧ i < width
      then bits.getLsbD (i - off) else old.getLsbD i := by
  induction n with
  | zero => simp only [spliceBytePrefix, Nat.zero_mul, Nat.add_zero]; split <;> simp_all <;> omega
  | succ n ih =>
    rw [spliceBytePrefix, Memory.getLsbD_spliceBits, ih (by omega)]
    by_cases hnew : off + n * 8 ≤ i ∧ i < off + n * 8 + 8 ∧ i < width
    · have hwhole : off ≤ i ∧ i < off + (n + 1) * 8 ∧ i < width := by omega
      have hsmall : i - (off + n * 8) < 8 := by omega
      have heq : 8 * n + (i - (off + n * 8)) = i - off := by omega
      simp [hnew, hwhole, BitVec.getLsbD_extractLsb', hsmall, heq]
    · have heq : (off ≤ i ∧ i < off + n * 8 ∧ i < width) ↔
          (off ≤ i ∧ i < off + (n + 1) * 8 ∧ i < width) := by omega
      simp only [hnew, ↓reduceIte, heq]

theorem spliceBytePrefix_full (old : BitVec width) (off : Nat) (bits : BitVec 256) :
    spliceBytePrefix old off bits 32 = Memory.spliceBits old off bits := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [spliceBytePrefix_bit old off bits 32 (by decide), Memory.getLsbD_spliceBits]

/-- The prefix alters only the addressed block and preserves its length. -/
theorem storePrefix_block (m : MemoryState) (out : Pointer) (bits : BitVec 256)
    (hr : SmallRange m out 32) (block : MemoryBlock) (hb : m[out.id]? = some block)
    (n : Nat) (hn : n ≤ 32) :
    (storePrefix m out bits n)[out.id]? =
      some {block with bytes := spliceBytePrefix block.bytes out.offsetInBits bits n} := by
  induction n with
  | zero => exact hb
  | succ n ih =>
    have hprev := ih (by omega)
    have hoff := Pointer.offsetInBits_add (hr.no_wrap (k := n) (by omega))
    have hn64 : n < 2 ^ 64 := by omega
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn64] at hoff
    have hs := MemoryState.getElem?_storeAt_self
      (p := out.add (BitVec.ofNat 64 n))
      (x := bits.extractLsb' (8 * n) 8) hprev
    simpa only [storePrefix, Pointer.add_id, hoff, spliceBytePrefix] using hs

theorem storePrefix_other (m : MemoryState) (out : Pointer) (bits : BitVec 256)
    (q : BlockId) (hne : q ≠ out.id) (n : Nat) :
    (storePrefix m out bits n)[q]? = m[q]? := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [storePrefix, MemoryState.getElem?_storeAt_ne (q := ⟨q, 0⟩) (by simpa using hne), ih]

/-- Exact whole-memory equation required by the SHA finalizer's StoreEffect. -/
theorem storeBytes_exact (m : MemoryState) (out : Pointer) (bits : BitVec 256)
    (hr : SmallRange m out 32) :
    storeBytes m out (fun i => bits.extractLsb' (8 * i.val) 8) = m.storeAt out bits := by
  have heq : storeBytes m out (fun i => bits.extractLsb' (8 * i.val) 8) =
      storePrefix m out bits 32 := by
    simp only [storeBytes, storePrefix, Pointer.add_zero]
    rfl
  rw [heq]
  obtain ⟨block, hb, hsmall, hfits⟩ := hr
  have hr : SmallRange m out 32 := ⟨block, hb, hsmall, hfits⟩
  apply MemoryState.ext
  apply Std.ExtHashMap.ext_getElem?
  intro q
  change (storePrefix m out bits 32)[q]? = (m.storeAt out bits)[q]?
  by_cases hq : q = out.id
  · subst q
    rw [storePrefix_block m out bits hr block hb 32 (by decide),
      MemoryState.getElem?_storeAt_self hb, spliceBytePrefix_full]
  · rw [storePrefix_other m out bits q hq, MemoryState.getElem?_storeAt_ne (q := ⟨q, 0⟩) hq]

end Agave.Ed25519.Verifier.Execution.ScalarWide
