import SSA.Projects.Agave.Ed25519.Proof.Reduce64.Execution.Memory

namespace Agave.Ed25519.ScalarReduce32.Execution
open LeanMLIR.RIR
open Reduce64.Execution (SmallRange)

abbrev Bytes := Fin 32 → BitVec 8

def storeBytes (m : MemoryState) (out : Pointer) (bytes : Bytes) : MemoryState :=
  (((((((((((((((((((((((((((((((m.storeAt out (bytes 0)).storeAt (out.add 1) (bytes 1)).storeAt (out.add 2) (bytes 2)).storeAt (out.add 3) (bytes 3)).storeAt (out.add 4) (bytes 4)).storeAt (out.add 5) (bytes 5)).storeAt (out.add 6) (bytes 6)).storeAt (out.add 7) (bytes 7)).storeAt (out.add 8) (bytes 8)).storeAt (out.add 9) (bytes 9)).storeAt (out.add 10) (bytes 10)).storeAt (out.add 11) (bytes 11)).storeAt (out.add 12) (bytes 12)).storeAt (out.add 13) (bytes 13)).storeAt (out.add 14) (bytes 14)).storeAt (out.add 15) (bytes 15)).storeAt (out.add 16) (bytes 16)).storeAt (out.add 17) (bytes 17)).storeAt (out.add 18) (bytes 18)).storeAt (out.add 19) (bytes 19)).storeAt (out.add 20) (bytes 20)).storeAt (out.add 21) (bytes 21)).storeAt (out.add 22) (bytes 22)).storeAt (out.add 23) (bytes 23)).storeAt (out.add 24) (bytes 24)).storeAt (out.add 25) (bytes 25)).storeAt (out.add 26) (bytes 26)).storeAt (out.add 27) (bytes 27)).storeAt (out.add 28) (bytes 28)).storeAt (out.add 29) (bytes 29)).storeAt (out.add 30) (bytes 30)).storeAt (out.add 31) (bytes 31)


/-- Auxiliary prefix of the same ascending byte-store sequence. -/
def storePrefix (m : MemoryState) (out : Pointer) (bits : BitVec 256) : Nat → MemoryState
  | 0 => m
  | n + 1 => (storePrefix m out bits n).storeAt (out.add (BitVec.ofNat 64 n))
      (bits.extractLsb' (8*n) 8)

theorem storePrefix_fits (m : MemoryState) (out : Pointer) (bits : BitVec 256)
    (q : Pointer) (width n : Nat) (h : Fits m q width) :
    Fits (storePrefix m out bits n) q width := by
  induction n with
  | zero => exact h
  | succ n ih => exact ih.storeAt

theorem storePrefix_read_bit (m : MemoryState) (out : Pointer) (bits : BitVec 256)
    (hr : SmallRange m out 32) (n : Nat) (hn : n ≤ 32) (i : Nat) (hi : i < 8*n) :
    ((storePrefix m out bits n).readAt out 256).getLsbD i = bits.getLsbD i := by
  induction n with
  | zero => omega
  | succ n ih =>
    have hn64 : n < 2^64 := by omega
    have hr' := storePrefix_fits m out bits out 256 n hr.fits
    have hw : (BitVec.ofNat 64 n).toNat * 8 + 8 ≤ 256 := by
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn64]
      omega
    rw [storePrefix, MemoryState.readAt_add_storeAt hr' (hr.no_wrap (by omega)) hw]
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn64, Memory.getLsbD_spliceBits]
    by_cases h : n*8 ≤ i
    · have hwithin : i < n*8+8 ∧ i < 256 := by omega
      simp only [h, hwithin.1, hwithin.2, and_self, ↓reduceIte,
        BitVec.getLsbD_extractLsb']
      have hoff : 8*n+(i-n*8) = i := by omega
      have hsmall : i-n*8 < 8 := by omega
      simp [hoff, hsmall]
    · simp only [h, false_and, ↓reduceIte]
      exact ih (by omega) (by omega)

/-- Readback is proved by a prefix invariant, without 256 separate bit cases. -/
theorem storeBytes_read (m : MemoryState) (out : Pointer) (bits : BitVec 256)
    (hr : SmallRange m out 32) :
    (storeBytes m out (fun i => bits.extractLsb' (8*i.val) 8)).readAt out 256 = bits := by
  have heq : storeBytes m out (fun i => bits.extractLsb' (8*i.val) 8) =
      storePrefix m out bits 32 := by
    simp only [storeBytes, storePrefix, Pointer.add_zero]
    rfl
  rw [heq]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  exact storePrefix_read_bit m out bits hr 32 (by decide) i hi

end Agave.Ed25519.ScalarReduce32.Execution
