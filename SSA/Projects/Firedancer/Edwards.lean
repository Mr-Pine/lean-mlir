/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Algebra.Group.Even
import Mathlib.Algebra.Field.Basic

/-!
# The twisted Edwards group law

The complete twisted Edwards curve `-x² + y² = 1 + d·x²·y²` over a field in which `-1` is a
square and `d` is not: its affine points with the addition of Bernstein–Lange form an
`AddCommGroup`. Completeness is `Curve.mul_ne`; closure and associativity are polynomial
identities modulo the curve equations, with certificates computed by Singular's `lift`.
-/

namespace Edwards

/-- A complete twisted Edwards curve with `a = -1`: `s² = -1`, `d` a non-square, `2 ≠ 0`. -/
structure Curve (K : Type*) [Field K] where
  d : K
  s : K
  s_sq : s ^ 2 = -1
  d_not_isSquare : ¬ IsSquare d
  two_ne_zero : (2 : K) ≠ 0

variable {K : Type*} [Field K] (E : Curve K)

namespace Curve

/-- `(x, y)` is on the curve. -/
def OnCurve (x y : K) : Prop := -x ^ 2 + y ^ 2 = 1 + E.d * x ^ 2 * y ^ 2

/-- **Completeness**: for points on the curve, `d·x₁x₂y₁y₂` is never `±1`. Otherwise
`(s·x₁ ± e·y₁)² = d·(x₁y₁(s·x₂ ± y₂))²` would make `d` a square. -/
theorem mul_ne {x₁ y₁ x₂ y₂ e : K} (h₁ : E.OnCurve x₁ y₁) (h₂ : E.OnCurve x₂ y₂)
    (he : e ^ 2 = 1) : E.d * x₁ * x₂ * y₁ * y₂ ≠ e := by
  intro h
  unfold OnCurve at h₁ h₂
  have he0 : e ≠ 0 := by rintro rfl; norm_num at he
  have hxy : x₁ * y₁ ≠ 0 := fun h0 => he0 (by rw [← h]; linear_combination (E.d * x₂ * y₂) * h0)
  have hs := E.s_sq
  have hp : (E.s * x₁ + e * y₁) ^ 2 = E.d * (x₁ * y₁ * (E.s * x₂ + y₂)) ^ 2 := by
    linear_combination (-x₂^2*y₂^2*E.d - x₂^2 + y₂^2) * h₁ + (x₁^2 - y₁^2 + 1) * h₂
      + (-x₁*y₁*x₂*y₂*E.d - 2*x₁*y₁*E.s - e) * h + (y₁^2 - 1) * he
      + (-x₁^2*y₁^2*x₂^2*E.d + x₁^2) * hs
  have hm : (E.s * x₁ - e * y₁) ^ 2 = E.d * (x₁ * y₁ * (E.s * x₂ - y₂)) ^ 2 := by
    linear_combination (-x₂^2*y₂^2*E.d - x₂^2 + y₂^2) * h₁ + (x₁^2 - y₁^2 + 1) * h₂
      + (-x₁*y₁*x₂*y₂*E.d + 2*x₁*y₁*E.s - e) * h + (y₁^2 - 1) * he
      + (-x₁^2*y₁^2*x₂^2*E.d + x₁^2) * hs
  have square : ∀ a b : K, b ≠ 0 → a ^ 2 = E.d * b ^ 2 → False := fun a b hb hab =>
    E.d_not_isSquare ⟨a / b, by field_simp; linear_combination -hab⟩
  by_cases hq : E.s * x₂ + y₂ = 0
  · by_cases hr : E.s * x₂ - y₂ = 0
    · have hs0 : E.s ≠ 0 := by rintro h0; rw [h0] at hs; norm_num at hs
      have hx₂ : x₂ = 0 := by
        have : (2 * E.s) * x₂ = 0 := by linear_combination hq + hr
        exact (mul_eq_zero.mp this).resolve_left (mul_ne_zero E.two_ne_zero hs0)
      exact he0 (by rw [← h, hx₂]; ring)
    · exact square _ _ (mul_ne_zero hxy hr) hm
  · exact square _ _ (mul_ne_zero hxy hq) hp

theorem den_add_ne_zero {x₁ y₁ x₂ y₂ : K} (h₁ : E.OnCurve x₁ y₁) (h₂ : E.OnCurve x₂ y₂) :
    1 + E.d * x₁ * x₂ * y₁ * y₂ ≠ 0 := fun h =>
  E.mul_ne h₁ h₂ (e := -1) (by norm_num) (by linear_combination h)

theorem den_sub_ne_zero {x₁ y₁ x₂ y₂ : K} (h₁ : E.OnCurve x₁ y₁) (h₂ : E.OnCurve x₂ y₂) :
    1 - E.d * x₁ * x₂ * y₁ * y₂ ≠ 0 := fun h =>
  E.mul_ne h₁ h₂ (e := 1) (by norm_num) (by linear_combination -h)

theorem onCurve_div {a b c e : K} (hb : b ≠ 0) (he : e ≠ 0)
    (h : -a ^ 2 * e ^ 2 + c ^ 2 * b ^ 2 = b ^ 2 * e ^ 2 + E.d * a ^ 2 * c ^ 2) :
    E.OnCurve (a / b) (c / e) := by
  unfold OnCurve
  rw [div_pow, div_pow]
  field_simp
  linear_combination h

/-- **Closure** of the addition formulas. -/
theorem onCurve_add {x₁ y₁ x₂ y₂ : K} (h₁ : E.OnCurve x₁ y₁) (h₂ : E.OnCurve x₂ y₂) :
    E.OnCurve ((x₁ * y₂ + y₁ * x₂) / (1 + E.d * x₁ * x₂ * y₁ * y₂))
      ((y₁ * y₂ + x₁ * x₂) / (1 - E.d * x₁ * x₂ * y₁ * y₂)) := by
  refine E.onCurve_div (E.den_add_ne_zero h₁ h₂) (E.den_sub_ne_zero h₁ h₂) ?_
  unfold OnCurve at h₁ h₂
  linear_combination
      (x₁^2*y₁^2*x₂^4*E.d + x₁^2*y₁^2*y₂^4*E.d + 2*x₁^2*y₁^2*x₂^2*E.d - 2*x₁^2*y₁^2*y₂^2*E.d
        + 2*x₁^2*y₁^2*x₂^2 - 2*x₁^2*y₁^2*y₂^2 + x₁^2*y₁^2*E.d + 2*x₁^2*y₁^2 - x₁^2*x₂^2
        + y₁^2*x₂^2 + x₁^2*y₂^2 - y₁^2*y₂^2 - x₁^2 + y₁^2 + 1) * h₁
    + (x₁^4*y₁^4*x₂^2*y₂^2*E.d^3 - x₁^4*y₁^4*x₂^2*E.d^2 + x₁^4*y₁^4*y₂^2*E.d^2
        - x₁^4*y₁^4*E.d^2 - 2*x₁^4*y₁^4*E.d - x₁^4*y₁^2*x₂^2*E.d + x₁^2*y₁^4*x₂^2*E.d
        + x₁^4*y₁^2*y₂^2*E.d - x₁^2*y₁^4*y₂^2*E.d - 2*x₁^4*y₁^2 + 2*x₁^2*y₁^4 - 2*x₁^2*y₁^2*E.d
        + x₁^4 - 4*x₁^2*y₁^2 + y₁^4) * h₂

section Assoc

variable {E}

theorem den_combine {a b c e p q t : K} (hb : b ≠ 0) (he : e ≠ 0) :
    b * e + t * a * c * p * q = (b * e) * (1 + t * (a / b) * p * (c / e) * q) := by
  field_simp

theorem num_combine {a b c e p q : K} (hb : b ≠ 0) (he : e ≠ 0) :
    a * e * p + c * b * q = (b * e) * (a / b * p + c / e * q) := by
  field_simp

theorem addX_left {a b c e x₃ y₃ : K} (hb : b ≠ 0) (he : e ≠ 0) :
    (a / b * y₃ + c / e * x₃) / (1 + E.d * (a / b) * x₃ * (c / e) * y₃)
      = (a * e * y₃ + c * b * x₃) / (b * e + E.d * a * c * x₃ * y₃) := by
  rw [num_combine hb he, den_combine hb he, mul_div_mul_left _ _ (mul_ne_zero hb he)]

theorem addX_right {a b c e x₁ y₁ : K} (hb : b ≠ 0) (he : e ≠ 0) :
    (x₁ * (c / e) + y₁ * (a / b)) / (1 + E.d * x₁ * (a / b) * y₁ * (c / e))
      = (c * b * x₁ + a * e * y₁) / (b * e + E.d * a * c * x₁ * y₁) := by
  rw [← mul_div_mul_left _ _ (mul_ne_zero hb he)]
  congr 1 <;> field_simp

theorem addY_left {a b c e x₃ y₃ : K} (hb : b ≠ 0) (he : e ≠ 0) :
    (c / e * y₃ + a / b * x₃) / (1 - E.d * (a / b) * x₃ * (c / e) * y₃)
      = (c * b * y₃ + a * e * x₃) / (b * e - E.d * a * c * x₃ * y₃) := by
  rw [← mul_div_mul_left _ _ (mul_ne_zero hb he)]
  congr 1 <;> field_simp

theorem addY_right {a b c e x₁ y₁ : K} (hb : b ≠ 0) (he : e ≠ 0) :
    (y₁ * (c / e) + x₁ * (a / b)) / (1 - E.d * x₁ * (a / b) * y₁ * (c / e))
      = (c * b * y₁ + a * e * x₁) / (b * e - E.d * a * c * x₁ * y₁) := by
  rw [← mul_div_mul_left _ _ (mul_ne_zero hb he)]
  congr 1 <;> field_simp

end Assoc

end Curve

/-- An affine point of `E`. -/
@[ext] structure Point where
  x : K
  y : K
  on : E.OnCurve x y

namespace Point

variable {E}

instance : Zero (Point E) := ⟨⟨0, 1, by simp [Curve.OnCurve]⟩⟩

instance : Neg (Point E) :=
  ⟨fun P => ⟨-P.x, P.y, by have h := P.on; unfold Curve.OnCurve at *; linear_combination h⟩⟩

instance : Add (Point E) :=
  ⟨fun P Q => ⟨(P.x * Q.y + P.y * Q.x) / (1 + E.d * P.x * Q.x * P.y * Q.y),
    (P.y * Q.y + P.x * Q.x) / (1 - E.d * P.x * Q.x * P.y * Q.y), E.onCurve_add P.on Q.on⟩⟩

@[simp] theorem zero_x : (0 : Point E).x = 0 := rfl
@[simp] theorem zero_y : (0 : Point E).y = 1 := rfl
@[simp] theorem neg_x (P : Point E) : (-P).x = -P.x := rfl
@[simp] theorem neg_y (P : Point E) : (-P).y = P.y := rfl
theorem add_x (P Q : Point E) :
    (P + Q).x = (P.x * Q.y + P.y * Q.x) / (1 + E.d * P.x * Q.x * P.y * Q.y) := rfl
theorem add_y (P Q : Point E) :
    (P + Q).y = (P.y * Q.y + P.x * Q.x) / (1 - E.d * P.x * Q.x * P.y * Q.y) := rfl

protected theorem add_comm (P Q : Point E) : P + Q = Q + P := by
  ext <;> simp only [add_x, add_y] <;> ring_nf

protected theorem zero_add (P : Point E) : 0 + P = P := by
  ext <;> simp [add_x, add_y]

protected theorem neg_add_cancel (P : Point E) : -P + P = 0 := by
  have h := P.on
  unfold Curve.OnCurve at h
  ext
  · simp [add_x]; ring_nf; simp
  · simp only [add_y, neg_x, neg_y, zero_y]
    rw [div_eq_one_iff_eq (by
      have := E.den_add_ne_zero P.on P.on
      intro h0; exact this (by linear_combination h0))]
    linear_combination h

protected theorem add_assoc (P Q R : Point E) : P + Q + R = P + (Q + R) := by
  have hPQ := (P + Q).on
  have hQR := (Q + R).on
  rcases P with ⟨x₁, y₁, h₁⟩
  rcases Q with ⟨x₂, y₂, h₂⟩
  rcases R with ⟨x₃, y₃, h₃⟩
  have hb₁ := E.den_add_ne_zero h₁ h₂
  have he₁ := E.den_sub_ne_zero h₁ h₂
  have hb₂ := E.den_add_ne_zero h₂ h₃
  have he₂ := E.den_sub_ne_zero h₂ h₃
  simp only [add_x, add_y] at hPQ hQR ⊢
  have dLx := E.den_add_ne_zero hPQ h₃
  have dLy := E.den_sub_ne_zero hPQ h₃
  have dRx := E.den_add_ne_zero h₁ hQR
  have dRy := E.den_sub_ne_zero h₁ hQR
  unfold Curve.OnCurve at h₁ h₂ h₃
  ext
  · simp only [add_x, add_y]
    rw [E.addX_left hb₁ he₁, E.addX_right hb₂ he₂,
      div_eq_div_iff
        (fun h0 => mul_ne_zero (mul_ne_zero hb₁ he₁) dLx (by rw [← h0]; field_simp))
        (fun h0 => mul_ne_zero (mul_ne_zero hb₂ he₂) dRx (by rw [← h0]; field_simp))]
    linear_combination (x₁*x₂^2*y₂*x₃^2*y₃*E.d - y₁*x₂*y₂^2*x₃^2*y₃*E.d - y₁*x₂^2*y₂*x₃*y₃^2*E.d
          + x₁*x₂*y₂^2*x₃*y₃^2*E.d + x₁*x₂^3*x₃^3 + y₁*x₂^2*y₂*x₃^3 - x₁*x₂*y₂^2*x₃^3
          - y₁*y₂^3*x₃^3 + y₁*x₂^3*x₃^2*y₃ + x₁*x₂^2*y₂*x₃^2*y₃ - y₁*x₂*y₂^2*x₃^2*y₃
          - x₁*y₂^3*x₃^2*y₃ - x₁*x₂^3*x₃*y₃^2 - y₁*x₂^2*y₂*x₃*y₃^2 + x₁*x₂*y₂^2*x₃*y₃^2
          + y₁*y₂^3*x₃*y₃^2 - y₁*x₂^3*y₃^3 - x₁*x₂^2*y₂*y₃^3 + y₁*x₂*y₂^2*y₃^3 + x₁*y₂^3*y₃^3
          + x₁*x₂^3*x₃ + y₁*x₂^2*y₂*x₃ - x₁*x₂*y₂^2*x₃ - y₁*y₂^3*x₃ + x₁*x₂*x₃^3 + y₁*y₂*x₃^3
          + y₁*x₂^3*y₃ + x₁*x₂^2*y₂*y₃ - y₁*x₂*y₂^2*y₃ - x₁*y₂^3*y₃ + y₁*x₂*x₃^2*y₃
          + x₁*y₂*x₃^2*y₃ - x₁*x₂*x₃*y₃^2 - y₁*y₂*x₃*y₃^2 - y₁*x₂*y₃^3 - x₁*y₂*y₃^3 + x₁*x₂*x₃
          + y₁*y₂*x₃ + y₁*x₂*y₃ + x₁*y₂*y₃) * h₁
      + (-x₁^3*y₁^2*x₂^2*y₂*x₃^2*y₃*E.d^2 + x₁^2*y₁^3*x₂*y₂^2*x₃^2*y₃*E.d^2
          + x₁^2*y₁^3*x₂^2*y₂*x₃*y₃^2*E.d^2 - x₁^3*y₁^2*x₂*y₂^2*x₃*y₃^2*E.d^2
          - x₁^3*y₁^2*x₂*x₃^3*E.d - x₁^2*y₁^3*y₂*x₃^3*E.d - x₁^2*y₁*x₂^2*y₂*x₃^3*E.d
          - x₁*y₁^2*x₂*y₂^2*x₃^3*E.d - x₁^2*y₁^3*x₂*x₃^2*y₃*E.d - x₁^3*y₁^2*y₂*x₃^2*y₃*E.d
          + x₁*y₁^2*x₂^2*y₂*x₃^2*y₃*E.d + x₁^2*y₁*x₂*y₂^2*x₃^2*y₃*E.d + x₁^3*y₁^2*x₂*x₃*y₃^2*E.d
          + x₁^2*y₁^3*y₂*x₃*y₃^2*E.d + x₁^2*y₁*x₂^2*y₂*x₃*y₃^2*E.d + x₁*y₁^2*x₂*y₂^2*x₃*y₃^2*E.d
          + x₁^2*y₁^3*x₂*y₃^3*E.d + x₁^3*y₁^2*y₂*y₃^3*E.d - x₁*y₁^2*x₂^2*y₂*y₃^3*E.d
          - x₁^2*y₁*x₂*y₂^2*y₃^3*E.d - x₁^3*y₁^2*x₂*x₃*E.d - x₁^2*y₁^3*y₂*x₃*E.d
          - x₁^2*y₁*x₂^2*y₂*x₃*E.d - x₁*y₁^2*x₂*y₂^2*x₃*E.d - x₁^2*y₁^3*x₂*y₃*E.d
          - x₁^3*y₁^2*y₂*y₃*E.d + x₁*y₁^2*x₂^2*y₂*y₃*E.d + x₁^2*y₁*x₂*y₂^2*y₃*E.d - x₁^3*x₂*x₃^3
          + x₁*y₁^2*x₂*x₃^3 - x₁^2*y₁*y₂*x₃^3 + y₁^3*y₂*x₃^3 - x₁^2*y₁*x₂*x₃^2*y₃
          + y₁^3*x₂*x₃^2*y₃ - x₁^3*y₂*x₃^2*y₃ + x₁*y₁^2*y₂*x₃^2*y₃ + x₁^3*x₂*x₃*y₃^2
          - x₁*y₁^2*x₂*x₃*y₃^2 + x₁^2*y₁*y₂*x₃*y₃^2 - y₁^3*y₂*x₃*y₃^2 + x₁^2*y₁*x₂*y₃^3
          - y₁^3*x₂*y₃^3 + x₁^3*y₂*y₃^3 - x₁*y₁^2*y₂*y₃^3 - x₁^3*x₂*x₃ + x₁*y₁^2*x₂*x₃
          - x₁^2*y₁*y₂*x₃ + y₁^3*y₂*x₃ - x₁*x₂*x₃^3 - y₁*y₂*x₃^3 - x₁^2*y₁*x₂*y₃ + y₁^3*x₂*y₃
          - x₁^3*y₂*y₃ + x₁*y₁^2*y₂*y₃ - y₁*x₂*x₃^2*y₃ - x₁*y₂*x₃^2*y₃ + x₁*x₂*x₃*y₃^2
          + y₁*y₂*x₃*y₃^2 + y₁*x₂*y₃^3 + x₁*y₂*y₃^3 - x₁*x₂*x₃ - y₁*y₂*x₃ - y₁*x₂*y₃
          - x₁*y₂*y₃) * h₂
      + (x₁^2*y₁*x₂^4*y₂^3*x₃*E.d^2 + x₁*y₁^2*x₂^3*y₂^4*x₃*E.d^2 - x₁*y₁^2*x₂^4*y₂^3*y₃*E.d^2
          - x₁^2*y₁*x₂^3*y₂^4*y₃*E.d^2 + x₁^2*y₁*x₂^4*y₂*x₃*E.d + x₁^3*x₂^3*y₂^2*x₃*E.d
          - y₁^3*x₂^2*y₂^3*x₃*E.d - x₁*y₁^2*x₂*y₂^4*x₃*E.d - x₁*y₁^2*x₂^4*y₂*y₃*E.d
          - y₁^3*x₂^3*y₂^2*y₃*E.d + x₁^3*x₂^2*y₂^3*y₃*E.d + x₁^2*y₁*x₂*y₂^4*y₃*E.d
          + x₁*x₂^3*y₂^2*x₃*E.d + y₁*x₂^2*y₂^3*x₃*E.d + y₁*x₂^3*y₂^2*y₃*E.d
          + x₁*x₂^2*y₂^3*y₃*E.d) * h₃
  · simp only [add_x, add_y]
    rw [E.addY_left hb₁ he₁, E.addY_right hb₂ he₂,
      div_eq_div_iff
        (fun h0 => mul_ne_zero (mul_ne_zero hb₁ he₁) dLy (by rw [← h0]; field_simp))
        (fun h0 => mul_ne_zero (mul_ne_zero hb₂ he₂) dRy (by rw [← h0]; field_simp))]
    linear_combination (y₁*x₂^2*y₂*x₃^2*y₃*E.d - x₁*x₂*y₂^2*x₃^2*y₃*E.d - x₁*x₂^2*y₂*x₃*y₃^2*E.d
          + y₁*x₂*y₂^2*x₃*y₃^2*E.d + y₁*x₂^3*x₃^3 + x₁*x₂^2*y₂*x₃^3 - y₁*x₂*y₂^2*x₃^3
          - x₁*y₂^3*x₃^3 + x₁*x₂^3*x₃^2*y₃ + y₁*x₂^2*y₂*x₃^2*y₃ - x₁*x₂*y₂^2*x₃^2*y₃
          - y₁*y₂^3*x₃^2*y₃ - y₁*x₂^3*x₃*y₃^2 - x₁*x₂^2*y₂*x₃*y₃^2 + y₁*x₂*y₂^2*x₃*y₃^2
          + x₁*y₂^3*x₃*y₃^2 - x₁*x₂^3*y₃^3 - y₁*x₂^2*y₂*y₃^3 + x₁*x₂*y₂^2*y₃^3 + y₁*y₂^3*y₃^3
          + y₁*x₂^3*x₃ + x₁*x₂^2*y₂*x₃ - y₁*x₂*y₂^2*x₃ - x₁*y₂^3*x₃ + y₁*x₂*x₃^3 + x₁*y₂*x₃^3
          + x₁*x₂^3*y₃ + y₁*x₂^2*y₂*y₃ - x₁*x₂*y₂^2*y₃ - y₁*y₂^3*y₃ + x₁*x₂*x₃^2*y₃
          + y₁*y₂*x₃^2*y₃ - y₁*x₂*x₃*y₃^2 - x₁*y₂*x₃*y₃^2 - x₁*x₂*y₃^3 - y₁*y₂*y₃^3 + y₁*x₂*x₃
          + x₁*y₂*x₃ + x₁*x₂*y₃ + y₁*y₂*y₃) * h₁
      + (-x₁^2*y₁^3*x₂^2*y₂*x₃^2*y₃*E.d^2 + x₁^3*y₁^2*x₂*y₂^2*x₃^2*y₃*E.d^2
          + x₁^3*y₁^2*x₂^2*y₂*x₃*y₃^2*E.d^2 - x₁^2*y₁^3*x₂*y₂^2*x₃*y₃^2*E.d^2
          - x₁^2*y₁^3*x₂*x₃^3*E.d - x₁^3*y₁^2*y₂*x₃^3*E.d + x₁*y₁^2*x₂^2*y₂*x₃^3*E.d
          + x₁^2*y₁*x₂*y₂^2*x₃^3*E.d - x₁^3*y₁^2*x₂*x₃^2*y₃*E.d - x₁^2*y₁^3*y₂*x₃^2*y₃*E.d
          - x₁^2*y₁*x₂^2*y₂*x₃^2*y₃*E.d - x₁*y₁^2*x₂*y₂^2*x₃^2*y₃*E.d + x₁^2*y₁^3*x₂*x₃*y₃^2*E.d
          + x₁^3*y₁^2*y₂*x₃*y₃^2*E.d - x₁*y₁^2*x₂^2*y₂*x₃*y₃^2*E.d - x₁^2*y₁*x₂*y₂^2*x₃*y₃^2*E.d
          + x₁^3*y₁^2*x₂*y₃^3*E.d + x₁^2*y₁^3*y₂*y₃^3*E.d + x₁^2*y₁*x₂^2*y₂*y₃^3*E.d
          + x₁*y₁^2*x₂*y₂^2*y₃^3*E.d - x₁^2*y₁^3*x₂*x₃*E.d - x₁^3*y₁^2*y₂*x₃*E.d
          + x₁*y₁^2*x₂^2*y₂*x₃*E.d + x₁^2*y₁*x₂*y₂^2*x₃*E.d - x₁^3*y₁^2*x₂*y₃*E.d
          - x₁^2*y₁^3*y₂*y₃*E.d - x₁^2*y₁*x₂^2*y₂*y₃*E.d - x₁*y₁^2*x₂*y₂^2*y₃*E.d
          - x₁^2*y₁*x₂*x₃^3 + y₁^3*x₂*x₃^3 - x₁^3*y₂*x₃^3 + x₁*y₁^2*y₂*x₃^3 - x₁^3*x₂*x₃^2*y₃
          + x₁*y₁^2*x₂*x₃^2*y₃ - x₁^2*y₁*y₂*x₃^2*y₃ + y₁^3*y₂*x₃^2*y₃ + x₁^2*y₁*x₂*x₃*y₃^2
          - y₁^3*x₂*x₃*y₃^2 + x₁^3*y₂*x₃*y₃^2 - x₁*y₁^2*y₂*x₃*y₃^2 + x₁^3*x₂*y₃^3
          - x₁*y₁^2*x₂*y₃^3 + x₁^2*y₁*y₂*y₃^3 - y₁^3*y₂*y₃^3 - x₁^2*y₁*x₂*x₃ + y₁^3*x₂*x₃
          - x₁^3*y₂*x₃ + x₁*y₁^2*y₂*x₃ - y₁*x₂*x₃^3 - x₁*y₂*x₃^3 - x₁^3*x₂*y₃ + x₁*y₁^2*x₂*y₃
          - x₁^2*y₁*y₂*y₃ + y₁^3*y₂*y₃ - x₁*x₂*x₃^2*y₃ - y₁*y₂*x₃^2*y₃ + y₁*x₂*x₃*y₃^2
          + x₁*y₂*x₃*y₃^2 + x₁*x₂*y₃^3 + y₁*y₂*y₃^3 - y₁*x₂*x₃ - x₁*y₂*x₃ - x₁*x₂*y₃
          - y₁*y₂*y₃) * h₂
      + (-x₁*y₁^2*x₂^4*y₂^3*x₃*E.d^2 - x₁^2*y₁*x₂^3*y₂^4*x₃*E.d^2 + x₁^2*y₁*x₂^4*y₂^3*y₃*E.d^2
          + x₁*y₁^2*x₂^3*y₂^4*y₃*E.d^2 - x₁*y₁^2*x₂^4*y₂*x₃*E.d - y₁^3*x₂^3*y₂^2*x₃*E.d
          + x₁^3*x₂^2*y₂^3*x₃*E.d + x₁^2*y₁*x₂*y₂^4*x₃*E.d + x₁^2*y₁*x₂^4*y₂*y₃*E.d
          + x₁^3*x₂^3*y₂^2*y₃*E.d - y₁^3*x₂^2*y₂^3*y₃*E.d - x₁*y₁^2*x₂*y₂^4*y₃*E.d
          + y₁*x₂^3*y₂^2*x₃*E.d + x₁*x₂^2*y₂^3*x₃*E.d + x₁*x₂^3*y₂^2*y₃*E.d
          + y₁*x₂^2*y₂^3*y₃*E.d) * h₃

instance : AddCommGroup (Point E) where
  add_assoc := Point.add_assoc
  zero_add := Point.zero_add
  add_zero P := (Point.add_comm P 0).trans (Point.zero_add P)
  nsmul := nsmulRec
  zsmul := zsmulRec
  neg_add_cancel := Point.neg_add_cancel
  add_comm := Point.add_comm

end Point
end Edwards
