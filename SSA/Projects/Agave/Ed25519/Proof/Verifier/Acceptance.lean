import SSA.Projects.Agave.Ed25519.Proof.Verifier.ControlFlow
import SSA.Projects.Agave.Ed25519.Bridge.Acceptance
import SSA.Projects.Agave.Ed25519.Bridge.SmallOrder

/-!
# From strict verification control flow to the shared curve specification

All remaining arithmetic/execution obligations are explicit fields or theorem
arguments. These declarations do not assert those obligations. In particular,
`SharedCorrect` must be established for decompression, negation, the cofactor
test and canonical scalar parsing before this theorem applies to machine code.

The result feeds the existing Firedancer acceptance bridge. It is at a shared
challenge scalar and does not identify the clients' SHA-512 implementations.
-/

namespace Agave.Ed25519.Verifier

open Bridge

/-- Exact contracts for the shared helpers, independent of verification and of
either double-scalar backend. The scalar parser returns the unsigned encoded
integer precisely when it is less than the prime subgroup order. -/
structure SharedCorrect (shared : Shared CurvePoint Nat) : Prop where
  decompress : ∀ bytes P, shared.decompress bytes = some P ↔ Encodes bytes P
  negate : ∀ P, shared.negate P = -P
  smallOrder : ∀ P, shared.smallOrder P = false ↔ (8 : Nat) • P ≠ 0
  scalar : ∀ bytes s, shared.parseScalar bytes = some s ↔
    s = bytes.toNat ∧ bytes.toNat < subgroupOrder

/-- Canonical signature scalars meet the double-scalar routine's input bound. -/
theorem subgroupOrder_lt_two_pow_255 : subgroupOrder < 2 ^ 255 := by
  decide

/-- Under exact helper contracts and an affine double-scalar refinement,
successful control flow is exactly Agave's strict acceptance predicate.
The challenge bound is supplied by challenge construction; the signature
scalar bound is derived from successful canonical parsing. No refinement for
out-of-range natural-number arguments to the backend is required. -/
theorem verify_iff_strict_accept {Result : Type}
    (shared : Shared CurvePoint Nat) (hshared : SharedCorrect shared)
    (doubleBase : Nat → CurvePoint → Nat → Result)
    (affine : Result → CurvePoint) (compressResult : Result → Bytes32)
    (hdouble : ∀ h minusA s, h < 2 ^ 255 → s < 2 ^ 255 →
      affine (doubleBase h minusA s) = h • minusA + s • base)
    (hcompress : ∀ result, compressResult result = compress (affine result))
    (a r s : Bytes32) (h : Nat) (hh : h < 2 ^ 255) :
    verify shared doubleBase compressResult a r s h = true ↔
      AgaveStrictAccept a r s.toNat h := by
  have hc (A : CurvePoint) (scalar : Nat) (hsBound : scalar < subgroupOrder) :
      compressResult (doubleBase h (shared.negate A) scalar) =
        compress (expectedR A scalar h) := by
    calc
      _ = compress (affine (doubleBase h (shared.negate A) scalar)) := hcompress _
      _ = compress (h • shared.negate A + scalar • base) :=
        congrArg compress (hdouble h (shared.negate A) scalar hh
          (lt_trans hsBound subgroupOrder_lt_two_pow_255))
      _ = compress (expectedR A scalar h) :=
        congrArg compress (congrArg (fun P : CurvePoint => h • P + scalar • base)
          (hshared.negate A))
  constructor
  · intro hv
    obtain ⟨A, R, scalar, ha, hA, hr, hR, hs, hout⟩ :=
      (verify_eq_true_iff shared doubleBase compressResult a r s h).mp hv
    obtain ⟨hscalar, hsBound⟩ := (hshared.scalar s scalar).mp hs
    subst scalar
    have hA' := (hshared.smallOrder (shared.negate A)).mp hA
    rw [hshared.negate A] at hA'
    refine ⟨hsBound, A, R, (hshared.decompress a A).mp ha,
      (hshared.decompress r R).mp hr, ?_,
      (hshared.smallOrder R).mp hR, ?_⟩
    · simpa using hA'
    · exact (hc A s.toNat hsBound).symm.trans hout
  · rintro ⟨hsBound, A, R, ha, hr, hA, hR, hout⟩
    apply (verify_eq_true_iff shared doubleBase compressResult a r s h).mpr
    refine ⟨A, R, s.toNat, (hshared.decompress a A).mpr ha, ?_,
      (hshared.decompress r R).mpr hr, (hshared.smallOrder R).mpr hR,
      (hshared.scalar s s.toNat).mpr ⟨rfl, hsBound⟩, ?_⟩
    · apply (hshared.smallOrder (shared.negate A)).mpr
      rw [hshared.negate A]
      simpa using hA
    · exact (hc A s.toNat hsBound).trans hout

/-- The exact cross-client policy bridge exposed to execution-conformance
proofs. Canonical R is a conclusion of strict acceptance, not a hidden input
assumption. The small-order correspondence is discharged by its curve proof. -/
theorem verify_iff_firedancer_and_canonical {Result : Type}
    (shared : Shared CurvePoint Nat) (hshared : SharedCorrect shared)
    (doubleBase : Nat → CurvePoint → Nat → Result)
    (affine : Result → CurvePoint) (compressResult : Result → Bytes32)
    (hdouble : ∀ h minusA s, h < 2 ^ 255 → s < 2 ^ 255 →
      affine (doubleBase h minusA s) = h • minusA + s • base)
    (hcompress : ∀ result, compressResult result = compress (affine result))
    (a r s : Bytes32) (h : Nat) (hh : h < 2 ^ 255) :
    verify shared doubleBase compressResult a r s h = true ↔
      FiredancerAccept a r s.toNat h ∧ CanonicalY r := by
  have hsmall : SmallOrderAgreement a r :=
    fun P _ => eight_nsmul_eq_zero_iff_mem_lowOrder P
  exact (verify_iff_strict_accept shared hshared doubleBase affine compressResult hdouble hcompress
    a r s h hh).trans (strict_iff_firedancer_and_canonical hsmall)

end Agave.Ed25519.Verifier
