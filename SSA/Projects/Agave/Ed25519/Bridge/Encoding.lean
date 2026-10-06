import SSA.Projects.Firedancer.Common.Spec.Group
import SSA.Projects.Firedancer.Common.Spec.fd_ed25519_affine_is_small_order

/-!
The shared curve and the byte-encoding boundary between Agave strict verification
and Firedancer verification. This module imports Firedancer's existing curve/group
proofs, but deliberately does not import its memory semantics or SHA contracts.

`Encodes` is definitionally the predicate in
`Firedancer.Common.Encodes` (Common/Spec/fd_ed25519_verify.lean). It is repeated
here because that file also imports the legacy SLLVM memory and SHA semantics.
No claim about execution follows from these encoding lemmas alone.
-/

namespace Agave.Ed25519.Bridge

open _root_.Ed25519

abbrev CurvePoint := Edwards.Point curve

/-- Firedancer's permissive point-decoding relation: reduce y modulo p,
and ignore the sign bit when x = 0. -/
def Encodes (bytes : BitVec 256) (P : CurvePoint) : Prop :=
  P.y = ((bytes.extractLsb' 0 255).toNat : ZMod p) ∧
    (P.x ≠ 0 → (P.x.val % 2 = 0 ↔ bytes[255] = false))

/-- Canonical Edwards compression: canonical y and the parity of canonical x. -/
def compress (P : CurvePoint) : BitVec 256 :=
  BitVec.ofNat 1 (P.x.val % 2) ++ BitVec.ofNat 255 P.y.val

/-- The y-coordinate has its canonical representative. The x = 0 sign-bit
ambiguity is irrelevant to accepted signatures, since x = 0 is small order. -/
def CanonicalY (bytes : BitVec 256) : Prop :=
  (bytes.extractLsb' 0 255).toNat < p

theorem y_lt_two_pow (P : CurvePoint) : P.y.val < 2 ^ 255 := by
  have := ZMod.val_lt P.y
  have hp : p < 2 ^ 255 := by decide
  omega

@[simp] theorem compress_y (P : CurvePoint) :
    ((compress P).extractLsb' 0 255).toNat = P.y.val := by
  unfold compress
  rw [BitVec.extractLsb'_append_eq_right, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (y_lt_two_pow P)]

@[simp] theorem compress_sign (P : CurvePoint) :
    (compress P)[255] = false ↔ P.x.val % 2 = 0 := by
  change ((BitVec.ofNat 1 (P.x.val % 2) ++ BitVec.ofNat 255 P.y.val) :
    BitVec (1 + 255))[255] = false ↔ _
  rw [BitVec.getElem_append]
  simp [BitVec.getElem_eq_testBit_toNat, Nat.testBit_zero]

theorem compress_encodes (P : CurvePoint) : Encodes (compress P) P := by
  constructor
  · rw [compress_y]; exact (ZMod.natCast_zmod_val P.y).symm
  · intro _; exact (compress_sign P).symm

theorem compress_canonical (P : CurvePoint) : CanonicalY (compress P) := by
  unfold CanonicalY
  rw [compress_y]
  exact ZMod.val_lt P.y

theorem sq_mul_den (P : CurvePoint) : P.x ^ 2 * (d * P.y ^ 2 + 1) = P.y ^ 2 - 1 := by
  have h : -P.x ^ 2 + P.y ^ 2 = 1 + d * P.x ^ 2 * P.y ^ 2 := P.on
  linear_combination -h

theorem den_ne_zero (P : CurvePoint) : d * P.y ^ 2 + 1 ≠ 0 := fun h0 => by
  have h := sq_mul_den P
  rw [h0, mul_zero] at h
  have hy : P.y ^ 2 = 1 := by linear_combination -h
  rw [hy, mul_one] at h0
  exact absurd (by linear_combination h0 : d = -1) (by decide)

/-- This is the existing Firedancer `encodes_unique` argument, independent of
the legacy memory semantics imported by its original module. -/
theorem encodes_unique {b : BitVec 256} {P Q : CurvePoint}
    (hP : Encodes b P) (hQ : Encodes b Q) : P = Q := by
  have hy : P.y = Q.y := hP.1.trans hQ.1.symm
  have hx2 : P.x ^ 2 = Q.x ^ 2 := by
    apply mul_right_cancel₀ (den_ne_zero P)
    rw [sq_mul_den, hy, sq_mul_den]
  refine Edwards.Point.ext ?_ hy
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hx2 with h | h
  · exact h
  by_cases h0 : Q.x = 0
  · rw [h, h0, neg_zero]
  have hP0 : P.x ≠ 0 := by rw [h]; exact neg_ne_zero.mpr h0
  have hpar := (hP.2 hP0).trans (hQ.2 h0).symm
  rw [h, ZMod.neg_val, if_neg h0] at hpar
  have hlt := ZMod.val_lt Q.x
  have hpos : Q.x.val ≠ 0 := (ZMod.val_ne_zero Q.x).mpr h0
  have hp : p % 2 = 1 := by decide
  omega

/-- The 255 y bits and the sign bit determine a compressed encoding. -/
theorem bytes_eq_of_parts {a b : BitVec 256}
    (hy : a.extractLsb' 0 255 = b.extractLsb' 0 255)
    (hs : a[255] = b[255]) : a = b := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  by_cases h : i < 255
  · have he := congrArg (fun v : BitVec 255 => v[i]) hy
    simpa only [BitVec.getElem_extractLsb', Nat.zero_add,
      BitVec.getLsbD_eq_getElem hi] using he
  · have : i = 255 := by omega
    subst i; exact hs

/-- On points with nonzero x, a permissive encoding is exactly the canonical
compression iff its y field is canonical. -/
theorem compress_eq_iff {b : BitVec 256} {P : CurvePoint} (hx : P.x ≠ 0) :
    compress P = b ↔ Encodes b P ∧ CanonicalY b := by
  constructor
  · rintro rfl; exact ⟨compress_encodes P, compress_canonical P⟩
  · rintro ⟨henc, hcanonical⟩
    apply bytes_eq_of_parts
    · apply BitVec.eq_of_toNat_eq
      rw [compress_y]
      have hv := congrArg ZMod.val henc.1
      simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt hcanonical] using hv
    · have hs := (compress_sign P).trans (henc.2 hx)
      cases h₁ : (compress P)[255] <;> cases h₂ : b[255] <;> simp_all

/-- Points with x = 0 are explicitly present in Firedancer's low-order list. -/
theorem mem_lowOrder_of_x_zero {P : CurvePoint} (hx : P.x = 0) :
    (P.x, P.y) ∈ lowOrder := by
  have hy : P.y ^ 2 = (1 : ZMod p) ^ 2 := by
    have hon := P.on
    change -P.x ^ 2 + P.y ^ 2 = 1 + d * P.x ^ 2 * P.y ^ 2 at hon
    simpa [hx] using hon
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hy with h | h
  · simp [lowOrder, hx, h]
  · simp [lowOrder, hx, h]

theorem x_ne_zero_of_not_lowOrder {P : CurvePoint}
    (h : (P.x, P.y) ∉ lowOrder) : P.x ≠ 0 :=
  fun hx => h (mem_lowOrder_of_x_zero hx)

end Agave.Ed25519.Bridge
