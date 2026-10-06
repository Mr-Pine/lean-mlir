import SSA.Projects.Agave.Ed25519.Proof.Encoding.FieldBytes
import Mathlib.Tactic

namespace Agave.Ed25519.Encoding
section

/-- The four little-endian u64 words formed by serializing five tight limbs.
The limb boundaries fall at bit positions 51, 102, 153, and 204. -/
def packWords (a : Fin 5 → BitVec 51) : Fin 4 → BitVec 64 := ![
  (a 0).setWidth 64 ||| ((a 1).setWidth 64) <<< 51,
  ((a 1).setWidth 64) >>> 13 ||| ((a 2).setWidth 64) <<< 38,
  ((a 2).setWidth 64) >>> 26 ||| ((a 3).setWidth 64) <<< 25,
  ((a 3).setWidth 64) >>> 39 ||| ((a 4).setWidth 64) <<< 12]

def packedBytes (a : Fin 5 → BitVec 51) : BitVec 256 :=
  packWords a 3 ++ packWords a 2 ++ packWords a 1 ++ packWords a 0

theorem packedBytes_eq (a : Fin 5 → BitVec 51) :
    packedBytes a = 0#1 ++ a 4 ++ a 3 ++ a 2 ++ a 1 ++ a 0 := by
  simp only [packedBytes, packWords, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_append]
  interval_cases i <;>
    simp [← BitVec.getLsbD_eq_getElem, BitVec.getLsbD_append, BitVec.getLsbD_setWidth,
      BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight,
      BitVec.getLsbD_of_ge]

theorem append_toNat (x : BitVec m) (y : BitVec n) :
    (x ++ y).toNat = x.toNat * 2^n + y.toNat := by
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt y.isLt,
    Nat.shiftLeft_eq]

theorem packedBytes_toNat (a : Fin 5 → BitVec 51) :
    (packedBytes a).toNat = value (fun i => (a i).toNat) := by
  rw [packedBytes_eq]
  simp only [append_toNat, BitVec.toNat_ofNat]
  norm_num [value, radix]
  ring

/-- The tight limbs computed by canonicalization serialize exactly to the
canonical field integer, not just an equal residue class. -/
theorem packedCanonical_toNat (a : Limbs) (ha : ∀ i, a i < 2^64) :
    (packedBytes (fun i => BitVec.ofNat 51 (canonicalLimbs a i))).toNat =
      value a % modulus := by
  rw [packedBytes_toNat]
  have ht := canonicalLimbs_tight a
  have hl (i : Fin 5) : (BitVec.ofNat 51 (canonicalLimbs a i)).toNat =
      canonicalLimbs a i := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (ht i)]
  simp only [hl]
  exact canonicalLimbs_value a ha

end
end Agave.Ed25519.Encoding
