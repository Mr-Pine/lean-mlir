import SSA.Projects.Agave.Ed25519.Bridge.Challenge
import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.ExecutionGlobals
import Mathlib.Data.Nat.ModEq

/-! Subgroup-order arithmetic for the exact wide-reduction boundary.
These lemmas do not assert an execution result for the imported program. -/

namespace Agave.Ed25519.Verifier.Execution.ScalarWide

open Agave.Ed25519.Bridge Agave.Ed25519.Bridge.Challenge

/-- Decode five native u64 slots as radix-2^52 limbs. This differs from
interpreting the entire 40-byte allocation as one integer. -/
def decode52 (slots : BitVec 320) : Nat :=
  (slots.extractLsb' 0 64).toNat +
  2 ^ 52 * (slots.extractLsb' 64 64).toNat +
  2 ^ 104 * (slots.extractLsb' 128 64).toNat +
  2 ^ 156 * (slots.extractLsb' 192 64).toNat +
  2 ^ 208 * (slots.extractLsb' 256 64).toNat

/-- The first extracted constant is the Montgomery radix modulo L. -/
theorem montgomeryR_value :
    decode52 montgomeryR.bytes = 2 ^ 260 % subgroupOrder := by
  decide +kernel

/-- The second extracted constant is the squared Montgomery radix modulo L. -/
theorem montgomeryRR_value :
    decode52 montgomeryRR.bytes = 2 ^ 520 % subgroupOrder := by
  decide +kernel

/-- The Montgomery radix is coprime to the subgroup order. -/
theorem radix_coprime : Nat.gcd subgroupOrder (2 ^ 260) = 1 := by
  decide +kernel

/-- Range certificate for either of the two Montgomery calls: the input is
below the radix, the constant below L, and the accumulated cancellation digits
below the radix. These are arithmetic premises, not machine postconditions. -/
theorem montgomery_quotient_bound (a b digits quotient : Nat)
    (ha : a < 2 ^ 260) (hb : b < subgroupOrder)
    (hdigits : digits < 2 ^ 260)
    (hcarry : quotient * 2 ^ 260 = a * b + digits * subgroupOrder) :
    quotient < 2 * subgroupOrder := by
  have horder : 0 < subgroupOrder := by norm_num [subgroupOrder]
  have hab : a * b < 2 ^ 260 * subgroupOrder :=
    lt_of_le_of_lt (Nat.mul_le_mul_right b (Nat.le_of_lt ha))
      (Nat.mul_lt_mul_of_pos_left hb (by decide))
  have hdigitsL : digits * subgroupOrder < 2 ^ 260 * subgroupOrder :=
    Nat.mul_lt_mul_of_pos_right hdigits horder
  have hq : quotient * 2 ^ 260 < (2 * subgroupOrder) * 2 ^ 260 := by
    rw [hcarry]
    omega
  exact (Nat.mul_lt_mul_right (by decide : 0 < 2 ^ 260)).mp hq

/-- Montgomery cancellation, parameterized by the factor represented by the
constant. R represents one; RR represents the radix. -/
theorem montgomery_quotient_mod (a b digits quotient factor : Nat)
    (hconstant : b % subgroupOrder = (factor * 2 ^ 260) % subgroupOrder)
    (hcarry : quotient * 2 ^ 260 = a * b + digits * subgroupOrder) :
    quotient % subgroupOrder = (a * factor) % subgroupOrder := by
  apply Nat.ModEq.cancel_right_of_coprime radix_coprime
  change (quotient * 2 ^ 260) % subgroupOrder =
    ((a * factor) * 2 ^ 260) % subgroupOrder
  rw [hcarry]
  calc
    (a * b + digits * subgroupOrder) % subgroupOrder =
        (a % subgroupOrder * (b % subgroupOrder)) % subgroupOrder := by
      simp [Nat.add_mod, Nat.mul_mod]
    _ = (a % subgroupOrder * ((factor * 2 ^ 260) % subgroupOrder)) %
        subgroupOrder := by rw [hconstant]
    _ = ((a * factor) * 2 ^ 260) % subgroupOrder := by
      simp [Nat.mul_mod, Nat.mul_assoc]

/-- A future execution proof can use congruence of the two Montgomery calls
and the final canonical addition. The split is at bit 260, not bit 256. -/
theorem exact_of_split_reductions (input : BitVec 512) (lo hi out : Nat)
    (hlo : lo % subgroupOrder = (input.toNat % 2 ^ 260) % subgroupOrder)
    (hhi : hi % subgroupOrder = (2 ^ 260 * (input.toNat / 2 ^ 260)) % subgroupOrder)
    (hout : out % subgroupOrder = (lo + hi) % subgroupOrder)
    (hcanonical : out < subgroupOrder) :
    out = input.toNat % subgroupOrder := by
  apply hashToScalar_eq_of_canonical_congruent input out hcanonical
  rw [Nat.add_mod, hlo, hhi, ← Nat.add_mod] at hout
  rw [hashToScalar_split260]
  exact hout

/-- Canonicality of the existing shared output encoding. -/
theorem reducedBytes_canonical (input : BitVec 512) :
    (reducedBytes input).toNat < subgroupOrder := by
  rw [reducedBytes_toNat]
  exact hashToScalar_lt_order input

/-- Uniqueness of the exact 32-byte little-endian canonical output. -/
theorem output_eq_reducedBytes (input : BitVec 512) (output : BitVec 256)
    (hcanonical : output.toNat < subgroupOrder)
    (hcongruent : output.toNat % subgroupOrder = input.toNat % subgroupOrder) :
    output = reducedBytes input := by
  apply BitVec.eq_of_toNat_eq
  rw [reducedBytes_toNat]
  exact hashToScalar_eq_of_canonical_congruent input output.toNat hcanonical hcongruent

end Agave.Ed25519.Verifier.Execution.ScalarWide
