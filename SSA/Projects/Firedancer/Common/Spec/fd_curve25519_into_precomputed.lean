/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.Firedancer.Curve

/-!
# The precomputed form `fd_curve25519_into_precomputed` writes

Point addition (RFC 8032 §5.1.4) multiplies `Y - X`, `Y + X` and `2d·T` of each
operand. A table point, added many times, stores those three and `Z` instead of
`X, Y, Z, T`, saving a sub, an add and the multiplication by `2d` per addition.
-/

namespace Ed25519

/-- A point as `(Y - X, Y + X, Z, 2d·T)`. -/
structure PrecomputedPoint where
  YminusX : ZMod p
  YplusX : ZMod p
  Z : ZMod p
  T2d : ZMod p

def Point.toPrecomputed (P : Point) : PrecomputedPoint :=
  ⟨P.Y - P.X, P.Y + P.X, P.Z, 2 * d * P.T⟩

def PrecomputedPoint.toPoint (Q : PrecomputedPoint) : Point :=
  ⟨(Q.YplusX - Q.YminusX) / 2, (Q.YplusX + Q.YminusX) / 2, Q.Z, Q.T2d / (2 * d)⟩

/-- The C holds a precomputed point in an `fd_ed25519_point_t`: `Y - X` in `X`,
`Y + X` in `Y`, `2d·T` in `T`. -/
def PrecomputedPoint.ofSlots (P : Point) : PrecomputedPoint := ⟨P.X, P.Y, P.Z, P.T⟩

theorem two_ne_zero_zmod : (2 : ZMod p) ≠ 0 := by decide

theorem d_ne_zero : d ≠ 0 := by decide

@[simp] theorem Point.toPoint_toPrecomputed (P : Point) : P.toPrecomputed.toPoint = P := by
  have := two_ne_zero_zmod
  have := d_ne_zero
  simp only [Point.toPrecomputed, PrecomputedPoint.toPoint]
  congr 1 <;> field_simp <;> ring

@[simp] theorem PrecomputedPoint.toPrecomputed_toPoint (Q : PrecomputedPoint) :
    Q.toPoint.toPrecomputed = Q := by
  have := two_ne_zero_zmod
  have := d_ne_zero
  simp only [Point.toPrecomputed, PrecomputedPoint.toPoint]
  congr 1 <;> field_simp <;> ring

end Ed25519
