import SSA.Projects.Firedancer.Ed25519
import SSA.Projects.Firedancer.Prime
import Mathlib.Tactic.LinearCombination
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.Algebra.Group.Even

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
def OnCurve (x y : ZMod p) : Prop :=
  -x ^ 2 + y ^ 2 = 1 + d * x ^ 2 * y ^ 2

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
def x (P : Point) : ZMod p :=
  P.X * P.Z⁻¹

/-- The affine y-coordinate, `Y/Z`. -/
def y (P : Point) : ZMod p :=
  P.Y * P.Z⁻¹

/-- `P` and `Q` represent the same curve point: their affine coordinates
agree. The notion `FD_R43X6_GE_IS_EQ` decides. -/
def SamePoint (P Q : Point) : Prop :=
  P.x = Q.x ∧ P.y = Q.y

/-- Equality in `ZMod p` is decidable, so `SamePoint` is: a specification can
say `if P.SamePoint Q then … else …` and still be executable. -/
instance (P Q : Point) : Decidable (P.SamePoint Q) :=
  inferInstanceAs (Decidable (P.x = Q.x ∧ P.y = Q.y))

@[simp]
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
theorem mul_inv_eq_mul_inv_iff {u v : ZMod p} (hu : IsUnit u) (hv : IsUnit v) (a b : ZMod p) :
    a * u⁻¹ = b * v⁻¹ ↔ a * v = b * u := by
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
theorem samePoint_iff_cross_sub_eq_zero {P Q : Point} (hP : IsUnit P.Z) (hQ : IsUnit Q.Z) :
    SamePoint P Q ↔ P.X * Q.Z - Q.X * P.Z = 0 ∧ P.Y * Q.Z - Q.Y * P.Z = 0 := by
  rw [samePoint_iff_cross hP hQ, sub_eq_zero, sub_eq_zero]

/-! ## The neutral point -/

/-- The neutral point `(0, 1)` as `FD_R43X6_GE_ZERO` represents it,
`(X,Y,Z,T) = (0,1,1,0)`. -/
def zero : Point :=
  ⟨0, 1, 1, 0⟩

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
  have h2 : IsUnit (2 : ZMod p) := IsUnit.of_mul_eq_one ((2 ^ 254 - 9 : ℕ) : ZMod p) (by decide)
  rw [samePoint_iff_cross h2 isUnit_one]
  constructor <;> simp [zero]

/-- And a pair that is *not* the same point: `(0, 1/2)` is not `(0, 1)`. -/
example : ¬SamePoint ⟨0, 2, 2, 0⟩ ⟨0, 1, 2, 0⟩ := by
  intro h
  have h2 : IsUnit (2 : ZMod p) := IsUnit.of_mul_eq_one ((2 ^ 254 - 9 : ℕ) : ZMod p) (by decide)
  have := (samePoint_iff_cross h2 h2).mp h
  revert this
  decide

end Point

/-! ## `d` is a quadratic non-residue

What makes edwards25519 complete, and what says point decompression's
denominator `d·y² + 1` never vanishes. `fd_f25519_sqrt_ratio`'s flag is
`∃ x, x² · v = u` while a spec is stated as `IsSquare (u / v)`; `ZMod`
division is total (`a / 0 = 0`, a square), so the two agree only where
`v ≠ 0`. -/

/-- `d` is a quadratic non-residue mod `p` -- the fact that makes edwards25519
complete, and here the one that says the decompression denominator never
vanishes. Euler's criterion, with the 255-bit exponentiation done in the
kernel by `Pratt.powModAux` rather than by `npowRec`. -/
theorem d_not_isSquare : ¬IsSquare (d : ZMod p) := by
  have hd :
    (d : ZMod p) =
      ((37095705934669439343138083508754565189542113879843219016388785533085940283555 : ℕ) :
        ZMod p) := by
    rw [d]; norm_num
  have hd0 : (d : ZMod p) ≠ 0 := by
    rw [hd, Ne, ZMod.natCast_eq_zero_iff]
    decide +kernel
  rw [ZMod.euler_criterion p hd0, hd]
  exact Pratt.pow_ne_one (by norm_num [p]) (by norm_num [p]) (by decide +kernel)

/-- ... so `v = d·y² + 1` is never `0`: if it were, `d = (√-1 / y)²` would be a
square. -/
theorem denom_ne_zero (y : ZMod p) : d * y ^ 2 + 1 ≠ 0 := by
  intro h
  have hy : y ≠ 0 := by
    rintro rfl; simp at h
  refine d_not_isSquare ⟨sqrtm1 * y⁻¹, ?_⟩
  field_simp
  rw [sqrtm1_sq]
  linear_combination h

/-- ... and with a non-zero denominator the region's flag and the spec's
`IsSquare` are the same statement.

Only `mp` needs `b ≠ 0`: `x² · 0 = a` forces `a = 0`, and `0 / 0 = 0` is a
square, so the converse holds outright. -/
theorem isSquare_div_iff {a b : ZMod p} (hb : b ≠ 0) : IsSquare (a / b) ↔ ∃ x, x ^ 2 * b = a := by
  constructor
  · rintro ⟨z, hz⟩
    field_simp at hz
    exact ⟨z, by linear_combination -hz⟩
  · rintro ⟨x, rfl⟩
    exact ⟨x, by field_simp⟩

/-! ## The point a decoding names

RFC 8032 §5.1.3 ends the same way in both backends: a square root `x` of
`(y² - 1)/(d y² + 1)` in hand, the point is `(x : y : 1 : x·y)`. The ref's
`fd_ed25519_point_frombytes` and the avx512 `fd_r43x6_ge_decode2` differ in how
they get `x` and `y` and in how they spell the sign bit, but not in this. -/

/-- The point a root and a `y` name. -/
def decodedPoint (xv yv : ZMod p) : Point :=
  ⟨xv, yv, 1, xv * yv⟩

@[simp]
theorem decodedPoint_X (xv yv : ZMod p) : (decodedPoint xv yv).X = xv :=
  rfl

@[simp]
theorem decodedPoint_Y (xv yv : ZMod p) : (decodedPoint xv yv).Y = yv :=
  rfl

@[simp]
theorem decodedPoint_Z (xv yv : ZMod p) : (decodedPoint xv yv).Z = 1 :=
  rfl

@[simp]
theorem decodedPoint_T (xv yv : ZMod p) : (decodedPoint xv yv).T = xv * yv :=
  rfl

@[simp]
theorem decodedPoint_x (xv yv : ZMod p) : (decodedPoint xv yv).x = xv := by
  simp [Point.x, decodedPoint]

@[simp]
theorem decodedPoint_y (xv yv : ZMod p) : (decodedPoint xv yv).y = yv := by
  simp [Point.y, decodedPoint]

/-- **The root's defining equation is the curve equation** for that point. -/
theorem onCurve_decodedPoint {xv yv : ZMod p} (h : xv ^ 2 * (d * yv ^ 2 + 1) = yv ^ 2 - 1) :
    OnCurve (decodedPoint xv yv).x (decodedPoint xv yv).y := by
  simp only [decodedPoint_x, decodedPoint_y, OnCurve]
  linear_combination -h

/-- ... and its `T` is the product the spec asks for. -/
@[simp]
theorem decodedPoint_T_div_Z (xv yv : ZMod p) :
    (decodedPoint xv yv).T / (decodedPoint xv yv).Z =
      (decodedPoint xv yv).x * (decodedPoint xv yv).y := by
  simp [decodedPoint, Point.x, Point.y]

/-! ## The candidate root

Both backends form the same candidate: `x = u·v³·(u·v⁷)^((p-5)/8)`, then test
`x²·v` against `±u`. The test succeeds exactly when `u/v` is a square, which
is what makes it the decision the specifications are stated with. -/

/-- The exponent both `fd_f25519_pow22523` and `fd_r43x6_pow22523_2` raise to. -/
theorem p_sub_five_div_eight : (p - 5) / 8 = 2 ^ 252 - 3 := by norm_num [p]

/-- **What the candidate root squares to.** `x = u·v³·(u v⁷)^((p-5)/8)` has
`x²·v = u·(u v⁷)^((p-1)/4)`, which is what turns the region's comparison into
Euler's criterion. Both backends form the same candidate, so both need this. -/
theorem sqrtCandidate_sq (u v : ZMod p) :
    (u * v ^ 3 * (u * v ^ 7) ^ ((p - 5) / 8)) ^ 2 * v = u * (u * v ^ 7) ^ ((p - 1) / 4) := by
  have e1 : (p - 5) / 8 * 2 = (p - 5) / 4 := by norm_num [p]
  have e2 : (p - 5) / 4 + 1 = (p - 1) / 4 := by norm_num [p]
  have h8 : ((u * v ^ 7) ^ ((p - 5) / 8)) ^ 2 = (u * v ^ 7) ^ ((p - 5) / 4) := by rw [← pow_mul, e1]
  rw [← e2, pow_add, pow_one, mul_pow, h8]
  ring

/-- **The fourth-power root is `±1` exactly when Euler's criterion holds**:
`w^((p-1)/4)` squares to `w^(p/2)`, so the region's two comparisons together
say that `w` is a square. -/
theorem pow_quarter_eq_pm_one_iff (w : ZMod p) :
    (w ^ ((p - 1) / 4) = -1 ∨ w ^ ((p - 1) / 4) = 1) ↔ w ^ (p / 2) = 1 := by
  have e3 : (p - 1) / 4 * 2 = p / 2 := by norm_num [p]
  rw [← e3, pow_mul, sq, mul_self_eq_one_iff]
  exact or_comm

/-- **`u v⁷` and `u/v` are squares together**: they differ by `v⁸`. What lets
Euler's criterion, which the region runs on `u v⁷`, decide the ratio the
specification is stated with. -/
theorem isSquare_mul_pow_seven_iff {u v : ZMod p} (hv : v ≠ 0) :
    IsSquare (u * v ^ 7) ↔ IsSquare (u / v) := by
  have v8 : IsSquare ((v : ZMod p) ^ 8) := Even.isSquare_pow (Even.two_nsmul 4) _
  have hrw : u * v ^ 7 = (u / v) * v ^ 8 := by field_simp
  rw [hrw]
  refine ⟨fun h => ?_, fun h => IsSquare.mul h v8⟩
  have := IsSquare.div h v8
  rwa [mul_div_cancel_right₀ _ (pow_ne_zero 8 hv)] at this

/-- **The candidate root's test.** `x²·v = ±u` exactly when `u/v` is a
square: the three lemmas above, composed. -/
theorem sqrtCandidate_iff {u v x : ZMod p} (hv : v ≠ 0)
    (hx : x = u * v ^ 3 * (u * v ^ 7) ^ ((p - 5) / 8)) :
    (x ^ 2 * v = u ∨ x ^ 2 * v = -u) ↔ IsSquare (u / v) := by
  by_cases hu : u = 0
  · subst hu
    simp [hx]
  · rw [hx, sqrtCandidate_sq, ← isSquare_mul_pow_seven_iff (u := u) hv,
      ZMod.euler_criterion p (mul_ne_zero hu (pow_ne_zero _ hv)), ← pow_quarter_eq_pm_one_iff]
    constructor
    · rintro (h | h)
      · exact
          Or.inr
            (mul_left_cancel₀ hu
              (by
                rw [h]; ring))
      · exact
          Or.inl
            (mul_left_cancel₀ hu
              (by
                rw [h]; ring))
    · rintro (h | h)
      · exact
          Or.inr
            (by
              rw [h]; ring)
      · exact
          Or.inl
            (by
              rw [h]; ring)

end Ed25519
