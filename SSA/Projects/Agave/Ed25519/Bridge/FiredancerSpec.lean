import SSA.Projects.Agave.Ed25519.Bridge.Equivalence
import SSA.Projects.Firedancer.Common.Spec.fd_ed25519_verify

/-!
Definition-level connections to the existing Firedancer verification proof.
The pure bridge uses the same group (not a second axiomatized curve), the same
permissive encoding relation, the same low-order list, and the same scalar bound.

This module imports the legacy execution specification only to check those
identities. RIR execution-conformance and hash/reduction correspondence remain
separate obligations; no theorem here substitutes a specification for execution.
-/

namespace Agave.Ed25519.Bridge

theorem encodes_eq_firedancer : Encodes = Firedancer.Common.Encodes := rfl

theorem subgroupOrder_eq_firedancer : subgroupOrder = Firedancer.Common.groupOrder := rfl

/-- The exact successful equation and checks used by Firedancer's existing
verifier specification, with its original definitions. -/
theorem firedancerAccept_iff_existing_spec_checks
    (a r : BitVec 256) (s challenge : Nat) :
    FiredancerAccept a r s challenge ↔
      s < Firedancer.Common.groupOrder ∧ ∃ A R : CurvePoint,
        Firedancer.Common.Encodes a A ∧ Firedancer.Common.Encodes r R ∧
        (A.x, A.y) ∉ _root_.Ed25519.lowOrder ∧
        (R.x, R.y) ∉ _root_.Ed25519.lowOrder ∧
        challenge • -A + s •
          _root_.Ed25519.basePoint.toAffine _root_.Ed25519.wellFormed_basePoint = R :=
  Iff.rfl

/-- Directly state the policy bridge using the encoding/scalar definitions
of the existing Firedancer proof. No encoding or small-order lemma is assumed. -/
theorem agave_iff_existing_firedancer_checks_and_canonical
    (a r : BitVec 256) (s challenge : Nat) :
    AgaveStrictAccept a r s challenge ↔
      (s < Firedancer.Common.groupOrder ∧ ∃ A R : CurvePoint,
        Firedancer.Common.Encodes a A ∧ Firedancer.Common.Encodes r R ∧
        (A.x, A.y) ∉ _root_.Ed25519.lowOrder ∧
        (R.x, R.y) ∉ _root_.Ed25519.lowOrder ∧
        challenge • -A + s •
          _root_.Ed25519.basePoint.toAffine _root_.Ed25519.wellFormed_basePoint = R) ∧
      CanonicalY r :=
  agave_iff_firedancer_and_canonical a r s challenge

end Agave.Ed25519.Bridge
