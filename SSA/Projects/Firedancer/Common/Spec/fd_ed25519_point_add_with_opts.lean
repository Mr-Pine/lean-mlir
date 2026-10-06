/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SSA.Projects.Firedancer.Common.Spec.fd_curve25519_into_precomputed

/-!
# The addition `fd_ed25519_point_add_with_opts` performs on a precomputed point

Both backends add with the formulas of RFC 8032 §5.1.4, reading `Y - X`,
`Y + X` and `2d·T` of the second operand from its precomputed form. That
`addPrecomputed` represents the sum is not proved: the group law is not
formalised (`Curve.lean`).
-/

@[expose] public section

namespace Ed25519

/-- `P + Q` for a precomputed `Q`, in the letters of RFC 8032 §5.1.4. -/
def Point.addPrecomputed (P : Point) (Q : PrecomputedPoint) : Point :=
  let A := (P.Y - P.X) * Q.YminusX
  let B := (P.Y + P.X) * Q.YplusX
  let C := P.T * Q.T2d
  let D := 2 * P.Z * Q.Z
  let E := B - A
  let F := D - C
  let G := D + C
  let H := B + A
  ⟨E * F, G * H, F * G, E * H⟩

end Ed25519
