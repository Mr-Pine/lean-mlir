import SSA.Projects.Firedancer.Ed25519
import Mathlib.Tactic.LinearCombination

/-!
# Ed25519 group elements / curve points

`fd_r43x6_ge.h` manipulates points of edwards25519, the twisted Edwards curve

    -x² + y² = 1 + d·x²·y²    over GF(2^255-19),

in the extended homogeneous coordinates of RFC 8032 §5.1.4: a point `(x, y)`
is held as `(X, Y, Z, T)` with `x = X/Z`, `y = Y/Z`, `x·y = T/Z`. This file is
the vocabulary those operations are specified in: the constant `d`, the curve
equation, the representation `Point` -- the header's "group element", prefix
`ge` -- and the equality of represented points that `FD_R43X6_GE_IS_EQ`
answers.

The theory is self-contained rather than built on
`Mathlib.AlgebraicGeometry.EllipticCurve.*`: Mathlib's curves are Weierstrass
models, it has neither twisted Edwards curves nor the birational map that
connects edwards25519 to one, and the `ge` operations are about the
*coordinate representation*, which is Edwards on the nose. Mathlib's curve
library becomes the target when the group law's correctness (associativity,
the order of the base point) is at stake, not before.

## Invertibility is `IsUnit`, not `≠ 0`

`ZMod p` is a field only given `p.Prime`, and no tool available here certifies
a 255-bit prime: Mathlib's `Nat.Prime` `norm_num` extension is trial division,
and the `lucas_primality` route needs a Pratt certificate chain formalized --
future work, orthogonal to the point operations. What `ZMod n` does carry
unconditionally is an `Inv` with `ZMod.mul_inv_of_unit`. So denominators are
hypothesised `IsUnit` -- for the true, prime `p` exactly `≠ 0`, and the form
the proofs consume; nothing below would gain from the field structure.
-/

namespace Ed25519

/-- The edwards25519 curve constant of RFC 8032 §5.1, `d = -121665/121666`, as
its canonical representative. `d_spec` checks the fraction; the value the
implementation bakes into `FD_R43X6_QUAD_1112d` is `2·d`. -/
def d : ZMod p :=
  37095705934669439343138083508754565189542113879843219016388785533085940283555

/-- `d` is the fraction the RFC defines it as. -/
theorem d_spec : 121666 * d = -121665 := by decide

/-- The affine curve equation of RFC 8032 §5.1: `(x, y)` is a point of
edwards25519. -/
def OnCurve (x y : ZMod p) : Prop := -x^2 + y^2 = 1 + d * x^2 * y^2

/-- A curve point in the extended homogeneous coordinates of RFC 8032 §5.1.4:
`x = X/Z`, `y = Y/Z`, `x·y = T/Z`. The C side holds the four coordinates as a
`FD_R43X6_QUAD`; which lane is which coordinate is the `Avx512` layer's
concern. Nothing is assumed of the coordinates here -- validity is the
separate `Point.WellFormed`, hypothesised where needed, in the style of the
`R43x6` representation classes. -/
structure Point where
  X : ZMod p
  Y : ZMod p
  Z : ZMod p
  T : ZMod p

namespace Point

/-- The affine x-coordinate, `X/Z`. `ZMod.inv` is total, so this is `X/Z` only
where `IsUnit Z`; every statement about it carries that hypothesis. -/
def x (P : Point) : ZMod p := P.X * P.Z⁻¹

/-- The affine y-coordinate, `Y/Z`. -/
def y (P : Point) : ZMod p := P.Y * P.Z⁻¹

/-- `P` and `Q` represent the same curve point: their affine coordinates
agree. The notion `FD_R43X6_GE_IS_EQ` decides. -/
def SamePoint (P Q : Point) : Prop := P.x = Q.x ∧ P.y = Q.y

theorem samePoint_equivalence : Equivalence SamePoint where
  refl _ := ⟨rfl, rfl⟩
  symm h := ⟨h.1.symm, h.2.symm⟩
  trans h h' := ⟨h.1.trans h'.1, h.2.trans h'.2⟩

/-- The representation invariant of `fd_r43x6_ge.h`: `Z` is invertible, the
affine point is on the curve, and `T` caches `x·y` (`X Y = T Z`, in the
header's words). `fd_r43x6_ge_is_eq` needs only `isUnit_Z`; the group law will
need the rest. -/
structure WellFormed (P : Point) : Prop where
  isUnit_Z : IsUnit P.Z
  onCurve : OnCurve P.x P.y
  t_spec : P.X * P.Y = P.T * P.Z

/-! ## Cross-multiplication

RFC 8032's `__eq__` (quoted verbatim at `fd_r43x6_ge_is_eq`) decides
`X₁/Z₁ = X₂/Z₂` without dividing, by comparing `X₁·Z₂` with `X₂·Z₁`. These are
the two steps of that: fractions to cross-products, and cross-products to the
subtract-and-test-zero the implementation performs. -/

/-- With both denominators invertible, `a/u = b/v ↔ a·v = b·u`. -/
theorem mul_inv_eq_mul_inv_iff {u v : ZMod p} (hu : IsUnit u) (hv : IsUnit v)
    (a b : ZMod p) : a * u⁻¹ = b * v⁻¹ ↔ a * v = b * u := by
  have hu1 : u * u⁻¹ = 1 := ZMod.mul_inv_of_unit u hu
  have hv1 : v * v⁻¹ = 1 := ZMod.mul_inv_of_unit v hv
  constructor <;> intro h
  · linear_combination u * v * h - a * v * hu1 + b * u * hv1
  · linear_combination u⁻¹ * v⁻¹ * h - a * u⁻¹ * hv1 + b * v⁻¹ * hu1

/-- **Cross-multiplication decides point equality**: representations with
invertible `Z`s are the same point iff `X₁·Z₂ = X₂·Z₁` and `Y₁·Z₂ = Y₂·Z₁`.
The four products are `fd_r43x6_ge_is_eq`'s `xn1, xn2, yn1, yn2`. -/
theorem samePoint_iff_cross {P Q : Point} (hP : IsUnit P.Z) (hQ : IsUnit Q.Z) :
    SamePoint P Q ↔ P.X * Q.Z = Q.X * P.Z ∧ P.Y * Q.Z = Q.Y * P.Z := by
  unfold SamePoint x y
  rw [mul_inv_eq_mul_inv_iff hP hQ, mul_inv_eq_mul_inv_iff hP hQ]

/-- `samePoint_iff_cross` in the form the implementation computes it:
`xn1 - xn2` and `yn1 - yn2`, each tested for zero by `fd_r43x6_is_nonzero`. -/
theorem samePoint_iff_cross_sub_eq_zero {P Q : Point}
    (hP : IsUnit P.Z) (hQ : IsUnit Q.Z) :
    SamePoint P Q ↔ P.X * Q.Z - Q.X * P.Z = 0 ∧ P.Y * Q.Z - Q.Y * P.Z = 0 := by
  rw [samePoint_iff_cross hP hQ, sub_eq_zero, sub_eq_zero]

/-! ## The neutral point -/

/-- The neutral point `(0, 1)` as `FD_R43X6_GE_ZERO` represents it,
`(X,Y,Z,T) = (0,1,1,0)`. -/
def zero : Point := ⟨0, 1, 1, 0⟩

theorem wellFormed_zero : zero.WellFormed where
  isUnit_Z := isUnit_one
  onCurve := by simp [OnCurve, x, y, zero]
  t_spec := by simp [zero]

/-! ## Sanity checks

The scale factor between two representations of one point is exactly what the
cross-multiplication criterion has to see through, so check it on one: the
doubled neutral representation `(0, 2, 2, 0)` -- RFC 8032 §5.1.4's "(0, Z, Z, 0)
for any non-zero Z" -- is the same point as `(0, 1, 1, 0)`. `IsUnit 2` is
exhibited by hand: `2·(2^254 - 9) = p + 1`. -/

example : SamePoint ⟨0, 2, 2, 0⟩ zero := by
  have h2 : IsUnit (2 : ZMod p) := IsUnit.of_mul_eq_one ((2^254 - 9 : ℕ) : ZMod p) (by decide)
  rw [samePoint_iff_cross h2 isUnit_one]
  constructor <;> simp [zero]

/-- And a pair that is *not* the same point: `(0, 1/2)` is not `(0, 1)`. -/
example : ¬ SamePoint ⟨0, 2, 2, 0⟩ ⟨0, 1, 2, 0⟩ := by
  intro h
  have h2 : IsUnit (2 : ZMod p) := IsUnit.of_mul_eq_one ((2^254 - 9 : ℕ) : ZMod p) (by decide)
  have := (samePoint_iff_cross h2 h2).mp h
  revert this
  decide

end Point
end Ed25519
