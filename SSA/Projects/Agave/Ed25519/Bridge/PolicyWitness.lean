import SSA.Projects.Agave.Ed25519.Bridge.Acceptance

/-!
A witness that the canonical-R qualification is necessary at the shared
challenge-scalar boundary. This does **not** exhibit a real-message signature:
the challenge is fixed to 1, and no SHA-512 preimage is asserted.
-/

namespace Agave.Ed25519.Bridge

open _root_.Ed25519

/-- A non-small-order point whose y = 3 admits both canonical and noncanonical
255-bit field representatives. -/
def witnessPoint : CurvePoint :=
  ⟨47490639360184182837601875270316946735278442122217188244898328344323804759522,
    3, by unfold Edwards.Curve.OnCurve; decide +kernel⟩

/-- Noncanonical compressed R: y = p + 3, even x. -/
def witnessR : BitVec 256 := BitVec.ofNat 256 (p + 3)

theorem witnessR_encodes : Encodes witnessR witnessPoint := by
  constructor
  · decide +kernel
  · intro _; decide +kernel

theorem witnessR_noncanonical : ¬ CanonicalY witnessR := by
  unfold CanonicalY
  decide +kernel

theorem witnessPoint_not_lowOrder :
    (witnessPoint.x, witnessPoint.y) ∉ lowOrder := by decide +kernel

theorem neg_witnessPoint_not_lowOrder :
    ((-witnessPoint).x, (-witnessPoint).y) ∉ lowOrder := by decide +kernel

theorem witness_firedancer_accepts :
    FiredancerAccept (compress (-witnessPoint)) witnessR 0 1 := by
  refine ⟨by decide, -witnessPoint, witnessPoint, compress_encodes _,
    witnessR_encodes, neg_witnessPoint_not_lowOrder, witnessPoint_not_lowOrder, ?_⟩
  simp [expectedR]

theorem witness_agave_rejects :
    ¬ AgaveStrictAccept (compress (-witnessPoint)) witnessR 0 1 :=
  strict_rejects_noncanonical witnessR_noncanonical

/-- Therefore shared-challenge acceptance predicates are not unconditionally
equivalent. This theorem makes no claim of a reachable hash input. -/
theorem shared_challenge_policies_differ :
    ∃ a r s challenge, FiredancerAccept a r s challenge ∧
      ¬ AgaveStrictAccept a r s challenge :=
  ⟨_, _, _, _, witness_firedancer_accepts, witness_agave_rejects⟩

end Agave.Ed25519.Bridge
