/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.Firedancer.Common.Spec.Group

namespace Firedancer

/-- Base-point table entries: `B k` is `(2k+1)·G`, precomputed from `Z = 1`. -/
def BaseVals (B : ℕ → Ed25519.PrecomputedPoint) (G : Ed25519.Point) (hG : G.WellFormed) : Prop :=
  ∀ k < 128, ∃ (Q : Ed25519.Point) (hQ : Q.WellFormed), Q.Z = 1 ∧ B k = Q.toPrecomputed
    ∧ Q.toAffine hQ = (2 * k + 1) • G.toAffine hG

end Firedancer
