import SSA.Projects.Agave.Ed25519.Proof.Verifier.Acceptance

/-!
# Acceptance through represented points and scalars

Point values may be nonunique machine limb representatives. Scalar values
need only carry canonical integers; they need not be unrestricted naturals.
Decompression completeness is existential up to the curve interpretation,
so this interface does not demand a unique projective representation.
-/

namespace Agave.Ed25519.Verifier
open Bridge

structure RepresentedSharedCorrect (shared : Shared Point Scalar)
    (toCurve : Point → CurvePoint) (toNat : Scalar → Nat) : Prop where
  decompress : ∀ bytes P, shared.decompress bytes = some P → Encodes bytes (toCurve P)
  decompressComplete : ∀ bytes P, Encodes bytes P →
    ∃ p, shared.decompress bytes = some p ∧ toCurve p = P
  negate : ∀ P, toCurve (shared.negate P) = -toCurve P
  smallOrder : ∀ P, shared.smallOrder P = false ↔ (8 : Nat) • toCurve P ≠ 0
  scalar : ∀ bytes s, shared.parseScalar bytes = some s ↔
    toNat s = bytes.toNat ∧ bytes.toNat < subgroupOrder
  scalarComplete : ∀ n, n < subgroupOrder → ∃ s, toNat s = n

theorem verify_iff_strict_accept_represented {Point Scalar Result : Type}
    (shared : Shared Point Scalar) (toCurve : Point → CurvePoint) (toNat : Scalar → Nat)
    (hshared : RepresentedSharedCorrect shared toCurve toNat)
    (doubleBase : Scalar → Point → Scalar → Result)
    (affine : Result → CurvePoint) (compressResult : Result → Bytes32)
    (hdouble : ∀ h minusA s, toNat h < 2 ^ 255 → toNat s < 2 ^ 255 →
      affine (doubleBase h minusA s) = toNat h • toCurve minusA + toNat s • base)
    (hcompress : ∀ result, compressResult result = compress (affine result))
    (a r s : Bytes32) (h : Scalar) (hh : toNat h < 2 ^ 255) :
    verify shared doubleBase compressResult a r s h = true ↔
      AgaveStrictAccept a r s.toNat (toNat h) := by
  have hc (A : Point) (scalar : Scalar) (hsBound : toNat scalar < subgroupOrder) :
      compressResult (doubleBase h (shared.negate A) scalar) =
        compress (expectedR (toCurve A) (toNat scalar) (toNat h)) := by
    rw [hcompress, hdouble h (shared.negate A) scalar hh
      (lt_trans hsBound subgroupOrder_lt_two_pow_255), hshared.negate]
    rfl
  constructor
  · intro hv
    obtain ⟨A, R, scalar, ha, hA, hr, hR, hs, hout⟩ :=
      (verify_eq_true_iff shared doubleBase compressResult a r s h).mp hv
    obtain ⟨hscalar, hsBound⟩ := (hshared.scalar s scalar).mp hs
    have hA' := (hshared.smallOrder (shared.negate A)).mp hA
    rw [hshared.negate A] at hA'
    refine ⟨hsBound, toCurve A, toCurve R, hshared.decompress a A ha,
      hshared.decompress r R hr, ?_, (hshared.smallOrder R).mp hR, ?_⟩
    · simpa using hA'
    · have he := (hc A scalar (by simpa only [hscalar] using hsBound)).symm.trans hout
      simpa only [hscalar] using he
  · rintro ⟨hsBound, A, R, ha, hr, hA, hR, hout⟩
    obtain ⟨aRep, haRep, haCurve⟩ := hshared.decompressComplete a A ha
    obtain ⟨rRep, hrRep, hrCurve⟩ := hshared.decompressComplete r R hr
    obtain ⟨scalar, hscalar⟩ := hshared.scalarComplete s.toNat hsBound
    apply (verify_eq_true_iff shared doubleBase compressResult a r s h).mpr
    refine ⟨aRep, rRep, scalar, haRep, ?_, hrRep, ?_,
      (hshared.scalar s scalar).mpr ⟨hscalar, hsBound⟩, ?_⟩
    · apply (hshared.smallOrder (shared.negate aRep)).mpr
      rw [hshared.negate, haCurve]
      simpa using hA
    · exact (hshared.smallOrder rRep).mpr (by simpa only [hrCurve] using hR)
    · have he := hc aRep scalar (by simpa only [hscalar] using hsBound)
      rw [haCurve, hscalar] at he
      exact he.trans hout

theorem verify_iff_firedancer_and_canonical_represented {Point Scalar Result : Type}
    (shared : Shared Point Scalar) (toCurve : Point → CurvePoint) (toNat : Scalar → Nat)
    (hshared : RepresentedSharedCorrect shared toCurve toNat)
    (doubleBase : Scalar → Point → Scalar → Result)
    (affine : Result → CurvePoint) (compressResult : Result → Bytes32)
    (hdouble : ∀ h minusA s, toNat h < 2 ^ 255 → toNat s < 2 ^ 255 →
      affine (doubleBase h minusA s) = toNat h • toCurve minusA + toNat s • base)
    (hcompress : ∀ result, compressResult result = compress (affine result))
    (a r s : Bytes32) (h : Scalar) (hh : toNat h < 2 ^ 255) :
    verify shared doubleBase compressResult a r s h = true ↔
      FiredancerAccept a r s.toNat (toNat h) ∧ CanonicalY r := by
  have hsmall : SmallOrderAgreement a r :=
    fun P _ => eight_nsmul_eq_zero_iff_mem_lowOrder P
  exact (verify_iff_strict_accept_represented shared toCurve toNat hshared
    doubleBase affine compressResult hdouble hcompress a r s h hh).trans
      (strict_iff_firedancer_and_canonical hsmall)

end Agave.Ed25519.Verifier
