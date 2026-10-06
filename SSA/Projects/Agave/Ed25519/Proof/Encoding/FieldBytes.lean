import SSA.Projects.Agave.Ed25519.Spec.Field
import Mathlib.Tactic

/-!
Integer arithmetic of `FieldElement51::{from_bytes,to_bytes}` in the pinned
solana-ed25519 0.2.4. The weak reduction, quotient carry chain, and final
carry chain are the schedules in `backend/serial/u64/field.rs:289–451`.
These theorems concern those arithmetic schedules; they do not assert that
an extracted RIR program executes them. That connection is a separate layer.
-/

namespace Agave.Ed25519.Encoding

abbrev Limbs := Fin 5 → Nat
abbrev radix : Nat := 2 ^ 51
abbrev top : Nat := 2 ^ 255
abbrev modulus : Nat := top - 19

def value (a : Limbs) : Nat :=
  a 0 + radix * a 1 + radix^2 * a 2 + radix^3 * a 3 + radix^4 * a 4

theorem value_eq_decode51 (a : Limbs) : value a = Field.decode51 a := by
  simp [value, Field.decode51, Fin.sum_univ_succ, radix]
  ring

/-- Five low-to-high 51-bit slices. The top input bit is discarded. -/
def fromBytes (n : Nat) : Limbs := ![
  n % radix, n / radix % radix, n / radix^2 % radix,
  n / radix^3 % radix, n / radix^4 % radix]

theorem fromBytes_value (n : Nat) : value (fromBytes n) = n % top := by
  norm_num [fromBytes, value, radix, top]
  omega

theorem fromBytes_tight (n : Nat) : Field.Tight51 (fromBytes n) := by
  intro i
  fin_cases i <;> simp [fromBytes, Field.Tight51, radix, Nat.mod_lt]

/-- The source weak reduction computes all five carries before adding them. -/
def weakReduce (a : Limbs) : Limbs := ![
  a 0 % radix + 19 * (a 4 / radix),
  a 1 % radix + a 0 / radix,
  a 2 % radix + a 1 / radix,
  a 3 % radix + a 2 / radix,
  a 4 % radix + a 3 / radix]

theorem weakReduce_identity (a : Limbs) :
    value (weakReduce a) + modulus * (a 4 / radix) = value a := by
  have h0 := Nat.mod_add_div (a 0) radix
  have h1 := Nat.mod_add_div (a 1) radix
  have h2 := Nat.mod_add_div (a 2) radix
  have h3 := Nat.mod_add_div (a 3) radix
  have h4 := Nat.mod_add_div (a 4) radix
  norm_num [value, weakReduce, radix, modulus, top] at *
  omega

theorem weakReduce_mod (a : Limbs) :
    value (weakReduce a) % modulus = value a % modulus := by
  have h := congrArg (· % modulus) (weakReduce_identity a)
  simpa [Nat.add_mod] using h

/-- All u64 inputs suffice: no cryptographic caller invariant is needed. -/
theorem weakReduce_lt_twice_modulus (a : Limbs)
    (ha : ∀ i, a i < 2 ^ 64) : value (weakReduce a) < 2 * modulus := by
  have h0 := ha 0; have h1 := ha 1; have h2 := ha 2
  have h3 := ha 3; have h4 := ha 4
  norm_num [value, weakReduce, radix, modulus, top] at *
  omega

/-- Uniform bound for every weakly reduced limb; the low limb's 19-fold
wraparound carry dominates the other four. -/
theorem weakReduce_limb_bound (a : Limbs) (ha : ∀ i, a i < 2 ^ 64)
    (i : Fin 5) : weakReduce a i < radix + 19 * 2^13 := by
  have h0 := ha 0; have h1 := ha 1; have h2 := ha 2
  have h3 := ha 3; have h4 := ha 4
  fin_cases i <;> norm_num [weakReduce, radix] at * <;> omega

/-- The five sequential carries, with an initial low-limb increment. -/
def carried (a : Limbs) (extra : Nat) : Limbs :=
  let t0 := a 0 + extra
  let t1 := a 1 + t0 / radix
  let t2 := a 2 + t1 / radix
  let t3 := a 3 + t2 / radix
  let t4 := a 4 + t3 / radix
  ![t0, t1, t2, t3, t4]

def masked (a : Limbs) : Limbs := fun i => a i % radix

theorem masked_lt_top (a : Limbs) : value (masked a) < top := by
  norm_num [value, masked, radix, top]
  omega

theorem carried_identity (a : Limbs) (extra : Nat) :
    value (masked (carried a extra)) + top * (carried a extra 4 / radix) =
      value a + extra := by
  have h0 := Nat.mod_add_div (carried a extra 0) radix
  have h1 := Nat.mod_add_div (carried a extra 1) radix
  have h2 := Nat.mod_add_div (carried a extra 2) radix
  have h3 := Nat.mod_add_div (carried a extra 3) radix
  have h4 := Nat.mod_add_div (carried a extra 4) radix
  norm_num [value, masked, carried, radix, top] at *
  omega

theorem carried_quotient (a : Limbs) (extra : Nat) :
    carried a extra 4 / radix = (value a + extra) / top := by
  have hi := carried_identity a extra
  have hb := masked_lt_top (carried a extra)
  norm_num [top] at *
  omega

theorem carried_remainder (a : Limbs) (extra : Nat) :
    value (masked (carried a extra)) = (value a + extra) % top := by
  have hi := carried_identity a extra
  have hb := masked_lt_top (carried a extra)
  norm_num [top] at *
  omega

/-- The source computes this quotient by propagating the carry of `h+19`. -/
def quotient (a : Limbs) : Nat := carried a 19 4 / radix

theorem quotient_eq (a : Limbs) : quotient a = (value a + 19) / top :=
  carried_quotient a 19

theorem quotient_weakReduce_le_one (a : Limbs) (ha : ∀ i, a i < 2 ^ 64) :
    quotient (weakReduce a) ≤ 1 := by
  rw [quotient_eq]
  have h := weakReduce_lt_twice_modulus a ha
  norm_num [modulus, top] at *
  omega

/-- Both source carry chains and their additions fit below 2^52. This is
strong enough for unsigned/signed u64 flags and subsequent shifts by ≤6. -/
theorem carried_weakReduce_bound (a : Limbs) (ha : ∀ i, a i < 2 ^ 64)
    (extra : Nat) (hextra : extra ≤ 19) (i : Fin 5) :
    carried (weakReduce a) extra i < 2^52 := by
  have h0 := weakReduce_limb_bound a ha 0
  have h1 := weakReduce_limb_bound a ha 1
  have h2 := weakReduce_limb_bound a ha 2
  have h3 := weakReduce_limb_bound a ha 3
  have h4 := weakReduce_limb_bound a ha 4
  fin_cases i <;> norm_num [carried, radix] at * <;> omega

theorem canonical_remainder (h : Nat) (hh : h < 2 * modulus) :
    (h + 19 * ((h + 19) / top)) % top = h % modulus := by
  by_cases hsmall : h < modulus
  · have hq : (h + 19) / top = 0 := by
      apply Nat.div_eq_of_lt
      norm_num [modulus, top] at hsmall ⊢
      omega
    have ht : h < top := by
      norm_num [modulus, top] at hsmall ⊢
      omega
    simp [hq, Nat.mod_eq_of_lt ht, Nat.mod_eq_of_lt hsmall]
  · have hlarge : modulus ≤ h := Nat.le_of_not_gt hsmall
    have hq : (h + 19) / top = 1 := by
      norm_num [modulus, top] at hh hlarge ⊢
      omega
    have hb : h - modulus < modulus := by omega
    have ht : h + 19 - top < top := by
      norm_num [modulus, top] at hh hlarge ⊢
      omega
    have hge : top ≤ h + 19 := by
      norm_num [modulus, top] at hlarge ⊢
      omega
    have he : h + 19 - top = h - modulus := by
      norm_num [modulus, top]
    rw [hq, Nat.mul_one, Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt ht,
      he, Nat.mod_eq_sub_mod hlarge, Nat.mod_eq_of_lt hb]

/-- The canonicalization schedule after weak reduction. -/
def canonicalLimbs (a : Limbs) : Limbs :=
  let w := weakReduce a
  masked (carried w (19 * quotient w))

theorem canonicalLimbs_value (a : Limbs) (ha : ∀ i, a i < 2 ^ 64) :
    value (canonicalLimbs a) = value a % modulus := by
  unfold canonicalLimbs
  rw [carried_remainder, quotient_eq,
    canonical_remainder _ (weakReduce_lt_twice_modulus a ha), weakReduce_mod]

theorem canonicalLimbs_tight (a : Limbs) : Field.Tight51 (canonicalLimbs a) := by
  intro i
  exact Nat.mod_lt _ (by decide)

/-- The 32-byte result viewed as a single little-endian 256-bit word. -/
def toBytes (a : Limbs) : BitVec 256 := BitVec.ofNat 256 (value (canonicalLimbs a))

theorem toBytes_toNat (a : Limbs) (ha : ∀ i, a i < 2 ^ 64) :
    (toBytes a).toNat = value a % modulus := by
  rw [toBytes, BitVec.toNat_ofNat, canonicalLimbs_value a ha]
  apply Nat.mod_eq_of_lt
  have := Nat.mod_lt (value a) (show 0 < modulus by decide)
  norm_num [modulus, top] at *
  omega

theorem toBytes_canonical (a : Limbs) (ha : ∀ i, a i < 2 ^ 64) :
    (toBytes a).toNat < modulus := by
  rw [toBytes_toNat a ha]
  exact Nat.mod_lt _ (by decide)

theorem toBytes_fromBytes (n : Nat) :
    (toBytes (fromBytes n)).toNat = (n % top) % modulus := by
  rw [toBytes_toNat, fromBytes_value]
  intro i
  have h := fromBytes_tight n i
  norm_num at h ⊢
  omega

/-- Inputs `p` through `2^255-1` are accepted as noncanonical field values. -/
theorem toBytes_fromBytes_noncanonical (k : Nat) (hk : k < 19) :
    (toBytes (fromBytes (modulus + k))).toNat = k := by
  rw [toBytes_fromBytes]
  norm_num [modulus, top] at *
  omega

/-- AVX2 splitting and serial canonical serialization preserve the same field
value for arbitrary physical u32 lanes, including loose coefficients. -/
theorem split_toBytes (v : Field.Packed) (e : Field.Element) :
    (toBytes (fun i => (Field.split v e i).toNat)).toNat =
      Field.packedValue v e % modulus := by
  rw [toBytes_toNat _ (fun i => (Field.split v e i).isLt), value_eq_decode51]
  change Field.serialValue (Field.split v e) % modulus = _
  rw [Field.split_value]

end Agave.Ed25519.Encoding
