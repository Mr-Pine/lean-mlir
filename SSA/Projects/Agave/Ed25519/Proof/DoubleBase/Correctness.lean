import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.Avx2Group
import SSA.Projects.Agave.Ed25519.Bridge.Acceptance
import SSA.Projects.Agave.Ed25519.UpstreamMath.Canonicality

/-!
The mathematical double-base endpoint with the verifier's scalar bounds and
canonical encoding. These theorems apply to every represented curve point,
so decoded non-small-order points are covered without an extra hypothesis.
No input-point prime-subgroup assumption is used. In particular reduction of
an arbitrary challenge is explicit; it is not silently identified with an
unreduced challenge acting on a point that might have a torsion component.

This module proves algebraic/encoding correctness, not compiler execution or
correctness of machine decoding, reduction, and field operations.
-/
namespace Agave.Ed25519.DoubleBase
open PointArithmetic Tables

/-- Reduction modulo the subgroup order derives the exact NAF input bound. -/
theorem reduced_scalar_bound (n : Nat) :
    n % UpstreamMath.Canonicality.ell < 2 ^ 255 := by
  have h := Nat.mod_lt n UpstreamMath.Canonicality.ell_pos
  have hb := UpstreamMath.Canonicality.ell_lt_253
  omega

/-- A canonical signature scalar satisfies the same NAF input bound. -/
theorem canonical_scalar_bound {s : Nat} (hs : s < Bridge.subgroupOrder) :
    s < 2 ^ 255 := by
  have hb := UpstreamMath.Canonicality.ell_lt_253
  change s < UpstreamMath.Canonicality.ell at hs
  omega

/-- Coordinates returned by either ladder retain nonzero Z, the extended T
relation, and exactly the advertised affine point. -/
theorem represents_coordinates {P : Extended F} {V : GroupPoint}
    (hP : Represents P V) :
    P.Z ≠ 0 ∧ P.X * P.Y = P.T * P.Z ∧ affine P = (V.x, V.y) := by
  obtain ⟨hw, rfl⟩ := hP
  refine ⟨hw.isUnit_Z.ne_zero, hw.t_spec, ?_⟩
  rfl

/-- The standard Z=1 decoded-coordinate representation of a curve point. -/
def decodedExtended (A : GroupPoint) : Extended F := ⟨A.x, A.y, 1, A.x * A.y⟩

theorem decodedExtended_represents (A : GroupPoint) :
    Represents (decodedExtended A) A := by
  have hw : (toFD (decodedExtended A)).WellFormed := {
    isUnit_Z := isUnit_one
    onCurve := by
      simpa [toFD, decodedExtended, _root_.Ed25519.Point.x,
        _root_.Ed25519.Point.y, _root_.Ed25519.OnCurve,
        Edwards.Curve.OnCurve, _root_.Ed25519.curve] using A.on
    t_spec := by simp [toFD, decodedExtended] }
  refine ⟨hw, ?_⟩
  apply Edwards.Point.ext <;>
    simp [toFD, decodedExtended, _root_.Ed25519.Point.toAffine,
      _root_.Ed25519.Point.x, _root_.Ed25519.Point.y]

/-- Serial correctness for a reduced challenge and canonical signature scalar. -/
theorem serialMath_reduced_represents {A : Extended F} {V : GroupPoint}
    (hA : Represents A V) (challenge s : Nat) (hs : s < Bridge.subgroupOrder) :
    Represents (serialMath (challenge % UpstreamMath.Canonicality.ell) A s)
      ((challenge % UpstreamMath.Canonicality.ell) • V + s • baseGroup) := by
  simpa only [natCast_zsmul] using
    serialMath_represents hA _ s (reduced_scalar_bound challenge) (canonical_scalar_bound hs)

/-- AVX2 correctness through its own loop invariant and the same scalar bounds. -/
theorem avx2Math_reduced_represents {A : Extended F} {V : GroupPoint}
    (hA : Represents A V) (challenge s : Nat) (hs : s < Bridge.subgroupOrder) :
    Represents (avx2Math (challenge % UpstreamMath.Canonicality.ell) A s)
      ((challenge % UpstreamMath.Canonicality.ell) • V + s • baseGroup) := by
  simpa only [natCast_zsmul] using
    avx2Math_represents_direct hA _ s (reduced_scalar_bound challenge) (canonical_scalar_bound hs)

/-- Canonical compression applied to the computed affine coordinates. -/
def canonicalEncodeAffine (xy : F × F) : BitVec 256 :=
  BitVec.ofNat 1 (xy.1.val % 2) ++ BitVec.ofNat 255 xy.2.val

def canonicalCompress (P : Extended F) : BitVec 256 :=
  compressWith canonicalEncodeAffine P

theorem represents_compress {P : Extended F} {V : GroupPoint}
    (hP : Represents P V) : canonicalCompress P = Bridge.compress V := by
  unfold canonicalCompress compressWith
  rw [(represents_coordinates hP).2.2]
  rfl

/-- The coordinate compression is also the natural-number encoding used in
UpstreamMath: y + parity(x) * 2^255. -/
theorem represents_compress_nat {P : Extended F} {V : GroupPoint}
    (hP : Represents P V) :
    (canonicalCompress P).toNat = UpstreamMath.Canonicality.encode V.y.val V.x.val := by
  rw [represents_compress hP]
  unfold Bridge.compress
  rw [BitVec.toNat_append,
    ← Nat.shiftLeft_add_eq_or_of_lt (BitVec.ofNat 255 V.y.val).isLt,
    Nat.shiftLeft_eq]
  simp only [BitVec.toNat_ofNat, UpstreamMath.Canonicality.encode]
  rw [Nat.mod_eq_of_lt (Bridge.y_lt_two_pow V)]
  norm_num
  omega

/-- The serial recomputation for a decoded public key satisfies exactly the
existing verifier's expected-R group equation and compression specification. -/
theorem serialMath_expectedR (A : GroupPoint) (challenge s : Nat)
    (hs : s < Bridge.subgroupOrder) :
    Represents (serialMath (challenge % UpstreamMath.Canonicality.ell)
      (negatePoint (decodedExtended A)) s)
      (Bridge.expectedR A s (challenge % UpstreamMath.Canonicality.ell)) ∧
    canonicalCompress (serialMath (challenge % UpstreamMath.Canonicality.ell)
      (negatePoint (decodedExtended A)) s) =
      Bridge.compress (Bridge.expectedR A s (challenge % UpstreamMath.Canonicality.ell)) := by
  have h := serialMath_reduced_represents
    (represents_negate (decodedExtended_represents A)) challenge s hs
  exact ⟨h, represents_compress h⟩

/-- The corresponding AVX2 recomputation theorem, with no equality premise
relating its result to the serial result. -/
theorem avx2Math_expectedR (A : GroupPoint) (challenge s : Nat)
    (hs : s < Bridge.subgroupOrder) :
    Represents (avx2Math (challenge % UpstreamMath.Canonicality.ell)
      (negatePoint (decodedExtended A)) s)
      (Bridge.expectedR A s (challenge % UpstreamMath.Canonicality.ell)) ∧
    canonicalCompress (avx2Math (challenge % UpstreamMath.Canonicality.ell)
      (negatePoint (decodedExtended A)) s) =
      Bridge.compress (Bridge.expectedR A s (challenge % UpstreamMath.Canonicality.ell)) := by
  have h := avx2Math_reduced_represents
    (represents_negate (decodedExtended_represents A)) challenge s hs
  exact ⟨h, represents_compress h⟩

end Agave.Ed25519.DoubleBase
