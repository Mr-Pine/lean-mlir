/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.Firedancer.Common.Spec.fd_ed25519_point_add_with_opts

/-!
# The negation `fd_ed25519_point_sub_with_opts` adds

`a - b` is `a + (-b)`, and `-(X, Y, Z, T) = (-X, Y, Z, -T)`: in precomputed form
`Y - X` and `Y + X` swap and `2d·T` changes sign.
-/

namespace Ed25519

/-- `-Q` for a precomputed `Q`. -/
def PrecomputedPoint.neg (Q : PrecomputedPoint) : PrecomputedPoint :=
  ⟨Q.YplusX, Q.YminusX, Q.Z, -Q.T2d⟩

end Ed25519
