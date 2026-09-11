/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.Firedancer.Common.Spec.fd_ed25519_point_dbln

/-!
# The two halves of a ref doubling

`fd_ed25519_partial_dbl` leaves `E, F, G, H` of `Point.dbl` in the coordinates
`X, Y, Z, T`; `fd_ed25519_point_add_final_mul` multiplies them out.
-/

namespace Ed25519

/-- What `fd_ed25519_partial_dbl` stores into `r`: `(E, F, G, H)`. -/
def Point.partialDbl (P : Point) : Point :=
  ⟨(P.X ^ 2 + P.Y ^ 2) - (P.X + P.Y) ^ 2, 2 * P.Z ^ 2 + (P.X ^ 2 - P.Y ^ 2),
    P.X ^ 2 - P.Y ^ 2, P.X ^ 2 + P.Y ^ 2⟩

/-- What `fd_ed25519_point_add_final_mul` stores into `r`. -/
def Point.finalMul (P : Point) : Point := ⟨P.X * P.Y, P.Z * P.T, P.Y * P.Z, P.X * P.T⟩

theorem Point.finalMul_partialDbl (P : Point) : P.partialDbl.finalMul = P.dbl := rfl

end Ed25519
