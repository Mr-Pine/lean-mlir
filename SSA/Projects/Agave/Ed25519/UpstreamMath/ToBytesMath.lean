import SSA.Projects.Agave.Ed25519.Spec.Field
import Mathlib

/-!
Independent arithmetic proofs for the current radix-51 serializer.
The upstream audit suggested the mathematical obligations; no upstream source
or proof script is incorporated. See PROVENANCE.md for scope and correspondence.
-/
namespace Agave.Ed25519.UpstreamMath.ToBytes

/-- Carry produced when 19 is added to a 255-bit field representative. -/
def correction (value : Nat) : Nat := (value + 19) / 2^255

/-- Integer-level result of adding the correction and discarding the top carry. -/
def canonicalize (value : Nat) : Nat :=
  (value + 19 * correction value) % 2^255

/-- Under the serializer's weak-reduction bound, the correction is a bit. -/
theorem correction_le_one (value : Nat) (h : value < 2 * Field.p) :
    correction value ≤ 1 := by
  unfold correction Field.p at *
  omega

/-- The carry identifies precisely the noncanonical half of the input range. -/
theorem correction_fires (value : Nat) (h : value < 2 * Field.p) :
    correction value = 1 ↔ Field.p ≤ value := by
  unfold correction Field.p at *
  omega

/-- Correctness of the add-19 and discard-bit-255 reduction formula. -/
theorem canonicalize_eq_mod (value : Nat) (h : value < 2 * Field.p) :
    canonicalize value = value % Field.p := by
  unfold canonicalize correction
  -- Same two quotient cases as Encoding.FieldBytes.canonical_remainder.
  by_cases small : value < Field.p
  · have quotientZero : (value + 19) / 2^255 = 0 := by
      apply Nat.div_eq_of_lt
      norm_num [Field.p] at small ⊢
      omega
    have belowTop : value < 2^255 := by
      norm_num [Field.p] at small ⊢
      omega
    rw [quotientZero, Nat.mul_zero, Nat.add_zero, Nat.mod_eq_of_lt belowTop,
      Nat.mod_eq_of_lt small]
  · have large : Field.p ≤ value := Nat.le_of_not_gt small
    have quotientOne : (value + 19) / 2^255 = 1 := by
      norm_num [Field.p] at h large ⊢
      omega
    have reducedBound : value - Field.p < Field.p := by omega
    have truncatedBound : value + 19 - 2^255 < 2^255 := by
      norm_num [Field.p] at h large ⊢
      omega
    have carry : 2^255 ≤ value + 19 := by
      norm_num [Field.p] at large ⊢
      omega
    have subtractEq : value + 19 - 2^255 = value - Field.p := by
      norm_num [Field.p]
    rw [quotientOne, Nat.mul_one, Nat.mod_eq_sub_mod carry,
      Nat.mod_eq_of_lt truncatedBound, subtractEq, Nat.mod_eq_sub_mod large,
      Nat.mod_eq_of_lt reducedBound]

theorem canonicalize_lt (value : Nat) (h : value < 2 * Field.p) :
    canonicalize value < Field.p := by
  rw [canonicalize_eq_mod value h]
  exact Nat.mod_lt _ Field.p_pos

/-- Natural-number counterpart of five serial carry steps. This theorem
has no limb bound because it performs unbounded arithmetic. -/
theorem five_carries (a b c d e : Nat) :
    (e + (d + (c + (b + a / 2^51) / 2^51) / 2^51) / 2^51) / 2^51 =
      (a + b * 2^51 + c * 2^102 + d * 2^153 + e * 2^204) / 2^255 := by
  omega

/-- A bound sufficient to connect weak radix-51 reduction to canonicalization.
It is stated on the assembled integer, not on a generated machine type. -/
theorem weak_limbs_lt_two_p (a b c d e : Nat)
    (ha : a < 2^51 + 19 * 2^13) (hb : b < 2^51 + 19 * 2^13)
    (hc : c < 2^51 + 19 * 2^13) (hd : d < 2^51 + 19 * 2^13)
    (he : e < 2^51 + 19 * 2^13) :
    a + b * 2^51 + c * 2^102 + d * 2^153 + e * 2^204 < 2 * Field.p := by
  unfold Field.p
  omega

end Agave.Ed25519.UpstreamMath.ToBytes
