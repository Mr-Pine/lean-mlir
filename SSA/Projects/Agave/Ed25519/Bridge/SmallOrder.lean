/- Released under Apache 2.0 license as described in LICENSE. -/
module
public import SSA.Projects.Firedancer.Common.Spec.Group
public import SSA.Projects.Firedancer.Common.Spec.fd_ed25519_affine_is_small_order

@[expose] public section
namespace Agave.Ed25519.Bridge
open _root_.Ed25519

private theorem double_eq_zero_iff (P : Edwards.Point curve) :
    P + P = 0 ↔ P.x = 0 := by
  constructor
  · intro h
    have he : P = -P := eq_neg_iff_add_eq_zero.mpr h
    have hx := congrArg Edwards.Point.x he
    simp only [Edwards.Point.neg_x] at hx
    have hz : (2 : ZMod p) * P.x = 0 := by linear_combination hx
    exact (mul_eq_zero.mp hz).resolve_left two_ne_zero
  · intro hx
    apply eq_neg_iff_add_eq_zero.mp
    ext <;> simp [hx]

private theorem double_x_zero_iff (P : Edwards.Point curve) :
    (P + P).x = 0 ↔ P.x = 0 ∨ P.y = 0 := by
  rw [Edwards.Point.add_x, div_eq_zero_iff]
  have hd := curve.den_add_ne_zero P.on P.on
  have hnum : P.x * P.y + P.y * P.x = (2 : ZMod p) * (P.x * P.y) := by ring
  simp only [hd, or_false, hnum, mul_eq_zero, _root_.Ed25519.two_ne_zero, false_or]

private theorem double_y_zero_iff (P : Edwards.Point curve) :
    (P + P).y = 0 ↔ P.x ^ 2 + P.y ^ 2 = 0 := by
  rw [Edwards.Point.add_y, div_eq_zero_iff]
  have hd := curve.den_sub_ne_zero P.on P.on
  have hnum : P.y * P.y + P.x * P.x = P.x ^ 2 + P.y ^ 2 := by ring
  simp only [hd, or_false, hnum]

private theorem order8_y0_poly : d * order8_y0 ^ 4 + 2 * order8_y0 ^ 2 - 1 = 0 := by
  decide +kernel

private theorem sum_sq_zero_iff (P : Edwards.Point curve) :
    P.x ^ 2 + P.y ^ 2 = 0 ↔ P.y = order8_y0 ∨ P.y = order8_y1 := by
  have hc : -P.x ^ 2 + P.y ^ 2 = 1 + d * P.x ^ 2 * P.y ^ 2 := P.on
  have ha := order8_y0_poly
  have hden := denom_ne_zero P.y
  constructor
  · intro hs
    have hf : d * P.y ^ 4 + 2 * P.y ^ 2 - 1 = 0 := by
      linear_combination hc + (1 + d * P.y ^ 2) * hs
    have hprod : (P.y ^ 2 - order8_y0 ^ 2) *
        (d * (P.y ^ 2 + order8_y0 ^ 2) + 2) = 0 := by
      linear_combination hf - ha
    rcases mul_eq_zero.mp hprod with hsame | hother
    · have hsq := sq_eq_sq_iff'.mp (sub_eq_zero.mp hsame)
      simpa only [order8_y1_eq_neg] using hsq
    · have hmul : d * (P.y * order8_y0) ^ 2 = -1 := by
        linear_combination P.y ^ 2 * hother - hf
      have hn : P.y * order8_y0 ≠ 0 := by
        intro hz
        rw [hz] at hmul
        norm_num at hmul
      exfalso
      apply d_not_isSquare
      refine ⟨sqrtm1 / (P.y * order8_y0), ?_⟩
      rw [← pow_two, div_pow, eq_div_iff (pow_ne_zero 2 hn)]
      linear_combination hmul - sqrtm1_sq
  · intro hy
    have hs : P.y ^ 2 = order8_y0 ^ 2 := by
      rcases hy with hy | hy
      · rw [hy]
      · rw [hy, order8_y1_eq_neg]; ring
    have hf : d * P.y ^ 4 + 2 * P.y ^ 2 - 1 = 0 := by
      calc
        _ = d * (P.y ^ 2) ^ 2 + 2 * P.y ^ 2 - 1 := by ring
        _ = 0 := by rw [hs]; exact ha
    have hz : (d * P.y ^ 2 + 1) * (P.x ^ 2 + P.y ^ 2) = 0 := by
      linear_combination hf - hc
    exact (mul_eq_zero.mp hz).resolve_left hden

/-- The exact group-theoretic meaning of Firedancer's eight coordinate pairs.
This discharges the small-order predicate boundary with no hypotheses on the point. -/
theorem eight_nsmul_eq_zero_iff_mem_lowOrder (P : Edwards.Point curve) :
    8 • P = 0 ↔ (P.x, P.y) ∈ lowOrder := by
  have h8 : 8 • P = ((P + P) + (P + P)) + ((P + P) + (P + P)) := by abel
  rw [h8, double_eq_zero_iff, double_x_zero_iff, double_x_zero_iff,
    double_y_zero_iff, sum_sq_zero_iff]
  have h := isSmallOrderTest_iff_mem (P := decodedPoint P.x P.y) (by rfl)
    (by simpa [Point.x, Point.y, decodedPoint, OnCurve, Edwards.Curve.OnCurve, curve] using P.on)
  simpa only [IsSmallOrderTest, decodedPoint, or_assoc] using h

end Agave.Ed25519.Bridge
