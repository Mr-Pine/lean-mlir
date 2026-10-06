import SSA.Projects.Agave.Ed25519.Bridge.Encoding

/-!
The acceptance-policy bridge at a shared challenge scalar.

This is a specification theorem, not an RIR execution-conformance theorem. The
execution proofs must separately establish their respective predicates below.
The challenge is an explicit common natural number: no equality of SHA-512 or
scalar-reduction implementations is assumed implicitly.
-/

namespace Agave.Ed25519.Bridge

open _root_.Ed25519

/-- The scalar bound used by both clients. This is definitionally the
`groupOrder` in Firedancer's scalar-validation specification. -/
def subgroupOrder : Nat := 2 ^ 252 + 27742317777372353535851937790883648493

def base : CurvePoint := basePoint.toAffine wellFormed_basePoint

/-- Both clients' cofactorless verification equation. -/
def expectedR (A : CurvePoint) (s challenge : Nat) : CurvePoint :=
  challenge • -A + s • base

/-- The acceptance condition of Firedancer's existing verifier specification,
at the challenge returned by its hash/reduction contract. -/
def FiredancerAccept (a r : BitVec 256) (s challenge : Nat) : Prop :=
  s < subgroupOrder ∧ ∃ A R : CurvePoint,
    Encodes a A ∧ Encodes r R ∧
    (A.x, A.y) ∉ lowOrder ∧ (R.x, R.y) ∉ lowOrder ∧
    expectedR A s challenge = R

/-- Agave strict verification: decode both points, reject points killed by
three doublings, require canonical S, and compare recompressed expected R to
the original bytes. The executable backend proof must establish this spec. -/
def AgaveStrictAccept (a r : BitVec 256) (s challenge : Nat) : Prop :=
  s < subgroupOrder ∧ ∃ A R : CurvePoint,
    Encodes a A ∧ Encodes r R ∧
    (8 : Nat) • A ≠ 0 ∧ (8 : Nat) • R ≠ 0 ∧
    compress (expectedR A s challenge) = r

/-- The precise remaining algebraic correspondence between the two
small-order tests, restricted to points decoded by this invocation. It says
nothing about verification, compression, signatures, or execution. -/
def SmallOrderAgreement (a r : BitVec 256) : Prop :=
  ∀ P : CurvePoint, Encodes a P ∨ Encodes r P →
    ((8 : Nat) • P = 0 ↔ (P.x, P.y) ∈ lowOrder)

/-- Exact policy difference, once the separately stated small-order lemma is
available. In particular canonical public-key encoding is not a premise. -/
theorem strict_iff_firedancer_and_canonical
    {a r : BitVec 256} {s challenge : Nat} (hsmall : SmallOrderAgreement a r) :
    AgaveStrictAccept a r s challenge ↔
      FiredancerAccept a r s challenge ∧ CanonicalY r := by
  constructor
  · rintro ⟨hs, A, R, ha, hr, hA, hR, hcompress⟩
    have hnA : (A.x, A.y) ∉ lowOrder :=
      fun h => hA ((hsmall A (Or.inl ha)).mpr h)
    have hnR : (R.x, R.y) ∉ lowOrder :=
      fun h => hR ((hsmall R (Or.inr hr)).mpr h)
    have he : Encodes r (expectedR A s challenge) := by
      rw [← hcompress]; exact compress_encodes _
    have heq := encodes_unique he hr
    exact ⟨⟨hs, A, R, ha, hr, hnA, hnR, heq⟩,
      hcompress ▸ compress_canonical _⟩
  · rintro ⟨⟨hs, A, R, ha, hr, hA, hR, heq⟩, hcanonical⟩
    refine ⟨hs, A, R, ha, hr, ?_, ?_, ?_⟩
    · exact fun h => hA ((hsmall A (Or.inl ha)).mp h)
    · exact fun h => hR ((hsmall R (Or.inr hr)).mp h)
    · rw [heq]
      exact (compress_eq_iff (x_ne_zero_of_not_lowOrder hR)).mpr ⟨hr, hcanonical⟩

theorem strict_implies_firedancer
    {a r : BitVec 256} {s challenge : Nat} (hsmall : SmallOrderAgreement a r)
    (h : AgaveStrictAccept a r s challenge) : FiredancerAccept a r s challenge :=
  ((strict_iff_firedancer_and_canonical hsmall).mp h).1

theorem strict_iff_firedancer_of_canonical
    {a r : BitVec 256} {s challenge : Nat} (hsmall : SmallOrderAgreement a r)
    (hcanonical : CanonicalY r) :
    AgaveStrictAccept a r s challenge ↔ FiredancerAccept a r s challenge := by
  rw [strict_iff_firedancer_and_canonical hsmall, and_iff_left hcanonical]

/-- Noncanonical R can never pass Agave's final byte comparison. This fact
does not depend on the outstanding small-order correspondence. -/
theorem strict_rejects_noncanonical
    {a r : BitVec 256} {s challenge : Nat} (hcanonical : ¬ CanonicalY r) :
    ¬ AgaveStrictAccept a r s challenge := by
  rintro ⟨_, A, R, _, _, _, _, hcompress⟩
  exact hcanonical (hcompress ▸ compress_canonical _)

end Agave.Ed25519.Bridge
