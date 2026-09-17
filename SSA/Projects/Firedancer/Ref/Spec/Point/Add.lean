/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SSA.Projects.Firedancer.Ref.Spec.Point.Dbl
public import SSA.Projects.Firedancer.Common.Spec.fd_ed25519_point_add_with_opts

/-!
# The two halves of a ref addition

With `skip_last_mul`, `fd_ed25519_point_add_with_opts` leaves `E, F, G, H` of
`Point.addPrecomputed` in the coordinates `X, Y, Z, T`;
`fd_ed25519_point_add_final_mul` multiplies them out.
-/

@[expose] public section

namespace Ed25519

/-- What `fd_ed25519_point_add_with_opts` stores into `r` with `skip_last_mul`:
`(E, F, G, H)`. -/
def Point.addPrecomputedPartial (P : Point) (Q : PrecomputedPoint) : Point :=
  let A := (P.Y - P.X) * Q.YminusX
  let B := (P.Y + P.X) * Q.YplusX
  let C := P.T * Q.T2d
  let D := 2 * P.Z * Q.Z
  ⟨B - A, D - C, D + C, B + A⟩

theorem Point.finalMul_addPrecomputedPartial (P : Point) (Q : PrecomputedPoint) :
    (P.addPrecomputedPartial Q).finalMul = P.addPrecomputed Q :=
  rfl

end Ed25519
