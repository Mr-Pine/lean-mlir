/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SSA.Projects.Firedancer.Edwards
public import SSA.Projects.Firedancer.Common.Spec.fd_ed25519_point_dbln
public import SSA.Projects.Firedancer.Common.Spec.fd_ed25519_point_sub_with_opts

/-!
# edwards25519's group, and what the `ge` formulas compute in it

`Edwards.Point curve` is the group of affine points of edwards25519. A well-formed extended
representation stands for one (`Point.toAffine`); `Point.dbl` computes its double and
`Point.addPrecomputed` its sum with a precomputed point, `Point.neg` its negation.
-/

@[expose] public section

namespace Ed25519

theorem two_ne_zero : (2 : ZMod p) ≠ 0 := by decide

/-- edwards25519 as a complete twisted Edwards curve. -/
def curve : Edwards.Curve (ZMod p) :=
  ⟨d, sqrtm1, sqrtm1_sq, d_not_isSquare, two_ne_zero⟩

/-- The base point `B = (x, 4/5)` of RFC 8032 §5.1, `x` even. -/
def basePoint : Point :=
  decodedPoint 15112221349535400772501151409588531511454012693041857206046113283949847762202
    46316835694926478169428394003475163141307993866256225615783033603165251855960

theorem wellFormed_basePoint : basePoint.WellFormed where
  isUnit_Z := isUnit_one
  onCurve := onCurve_decodedPoint (by decide)
  t_spec := by simp [basePoint, decodedPoint]

theorem basePoint_Z : basePoint.Z = 1 :=
  rfl

namespace Point

variable {P : Point}

theorem X_eq (h : P.WellFormed) : P.X = P.x * P.Z := by
  rw [x, mul_assoc, inv_mul_cancel₀ h.isUnit_Z.ne_zero, mul_one]

theorem Y_eq (h : P.WellFormed) : P.Y = P.y * P.Z := by
  rw [y, mul_assoc, inv_mul_cancel₀ h.isUnit_Z.ne_zero, mul_one]

theorem T_eq (h : P.WellFormed) : P.T = P.x * P.y * P.Z :=
  mul_right_cancel₀ h.isUnit_Z.ne_zero
    (by
      rw [← h.t_spec, X_eq h, Y_eq h]; ring)

/-- The affine point a well-formed representation stands for. -/
def toAffine (P : Point) (h : P.WellFormed) : Edwards.Point curve :=
  ⟨P.x, P.y, h.onCurve⟩

theorem toAffine_eq_iff {Q : Point} (hP : P.WellFormed) (hQ : Q.WellFormed) :
    P.toAffine hP = Q.toAffine hQ ↔ P.SamePoint Q := by
  constructor
  · intro h; exact ⟨congrArg Edwards.Point.x h, congrArg Edwards.Point.y h⟩
  · intro h; exact Edwards.Point.ext h.1 h.2

/-- `dbl`'s `F` and `G`, in affine terms: `Z²·(1 ∓ d·x²·y²)`, so never `0`. -/
theorem dbl_FG_ne_zero (h : P.WellFormed) :
    2 * P.Z ^ 2 + ((P.x * P.Z) ^ 2 - (P.y * P.Z) ^ 2) ≠ 0 ∧
      (P.x * P.Z) ^ 2 - (P.y * P.Z) ^ 2 ≠ 0 := by
  have hZ := pow_ne_zero 2 h.isUnit_Z.ne_zero
  have hc : -P.x ^ 2 + P.y ^ 2 = 1 + d * P.x ^ 2 * P.y ^ 2 := h.onCurve
  have hp : 1 + d * P.x * P.x * P.y * P.y ≠ 0 := curve.den_add_ne_zero h.onCurve h.onCurve
  have hm : 1 - d * P.x * P.x * P.y * P.y ≠ 0 := curve.den_sub_ne_zero h.onCurve h.onCurve
  exact
    ⟨fun h0 => mul_ne_zero hZ hm (by linear_combination h0 + P.Z ^ 2 * hc), fun h0 =>
      mul_ne_zero hZ hp (by linear_combination -h0 - P.Z ^ 2 * hc)⟩

theorem dbl_x (h : P.WellFormed) : P.dbl.x = (P.toAffine h + P.toAffine h).x := by
  have hc : -P.x ^ 2 + P.y ^ 2 = 1 + d * P.x ^ 2 * P.y ^ 2 := h.onCurve
  have hp : 1 + d * P.x * P.x * P.y * P.y ≠ 0 := curve.den_add_ne_zero h.onCurve h.onCurve
  obtain ⟨hF, hG⟩ := dbl_FG_ne_zero h
  rw [Point.x, Edwards.Point.add_x]
  simp only [dbl, toAffine, show curve.d = d from rfl]
  rw [X_eq h, Y_eq h]
  generalize hFe : 2 * P.Z ^ 2 + ((P.x * P.Z) ^ 2 - (P.y * P.Z) ^ 2) = F at hF
  generalize hGe : (P.x * P.Z) ^ 2 - (P.y * P.Z) ^ 2 = G at hG
  rw [show ∀ E : ZMod p, E * F * (F * G)⁻¹ = E * G⁻¹ * (F * F⁻¹) from fun _ => by ring,
    mul_inv_cancel₀ hF, mul_one, ← div_eq_mul_inv, div_eq_div_iff hG hp]
  rw [← hGe]
  linear_combination (2 * P.x * P.y * P.Z ^ 2) * hc

theorem dbl_y (h : P.WellFormed) : P.dbl.y = (P.toAffine h + P.toAffine h).y := by
  have hc : -P.x ^ 2 + P.y ^ 2 = 1 + d * P.x ^ 2 * P.y ^ 2 := h.onCurve
  have hm : 1 - d * P.x * P.x * P.y * P.y ≠ 0 := curve.den_sub_ne_zero h.onCurve h.onCurve
  obtain ⟨hF, hG⟩ := dbl_FG_ne_zero h
  rw [Point.y, Edwards.Point.add_y]
  simp only [dbl, toAffine, show curve.d = d from rfl]
  rw [X_eq h, Y_eq h]
  generalize hFe : 2 * P.Z ^ 2 + ((P.x * P.Z) ^ 2 - (P.y * P.Z) ^ 2) = F at hF
  generalize hGe : (P.x * P.Z) ^ 2 - (P.y * P.Z) ^ 2 = G at hG
  rw [show ∀ H : ZMod p, G * H * (F * G)⁻¹ = H * F⁻¹ * (G * G⁻¹) from fun _ => by ring,
    mul_inv_cancel₀ hG, mul_one, ← div_eq_mul_inv, div_eq_div_iff hF hm]
  rw [← hFe]
  linear_combination (P.x ^ 2 + P.y ^ 2) * P.Z ^ 2 * hc

theorem wellFormed_dbl (h : P.WellFormed) : P.dbl.WellFormed where
  isUnit_Z := by
    obtain ⟨hF, hG⟩ := dbl_FG_ne_zero h
    simp only [dbl]
    rw [X_eq h, Y_eq h]
    exact (mul_ne_zero hF hG).isUnit
  onCurve := by
    rw [dbl_x h, dbl_y h]; exact (P.toAffine h + P.toAffine h).on
  t_spec := by
    simp only [dbl]; ring

theorem wellFormed_iterate_dbl (h : P.WellFormed) : ∀ k, (dbl^[k] P).WellFormed
  | 0 => h
  | k + 1 => by
    rw [Function.iterate_succ_apply']
    exact wellFormed_dbl (wellFormed_iterate_dbl h k)

theorem wellFormed_dbln (n : BitVec 32) (h : P.WellFormed) : (P.dbln n).WellFormed :=
  wellFormed_iterate_dbl h _

/-- **`dbl` doubles.** -/
theorem toAffine_dbl (h : P.WellFormed) :
    P.dbl.toAffine (wellFormed_dbl h) = P.toAffine h + P.toAffine h :=
  Edwards.Point.ext (dbl_x h) (dbl_y h)

theorem toAffine_congr {Q Q' : Point} (e : Q = Q') (hQ : Q.WellFormed) (hQ' : Q'.WellFormed) :
    Q.toAffine hQ = Q'.toAffine hQ' := by
  subst e; rfl

/-- **`dbln` doubles `dblnCount n` times.** -/
theorem toAffine_iterate_dbl (h : P.WellFormed) :
    ∀ k, (dbl^[k] P).toAffine (wellFormed_iterate_dbl h k) = 2 ^ k • P.toAffine h
  | 0 => by
    rw [pow_zero, one_nsmul]; rfl
  | k + 1 => by
    rw [toAffine_congr (Function.iterate_succ_apply' dbl k P) _
        (wellFormed_dbl (wellFormed_iterate_dbl h k)),
      toAffine_dbl (wellFormed_iterate_dbl h k), toAffine_iterate_dbl h k, pow_succ, mul_nsmul,
      two_nsmul]

theorem toAffine_dbln (h : P.WellFormed) (n : BitVec 32) :
    (P.dbln n).toAffine (wellFormed_dbln n h) = 2 ^ dblnCount n • P.toAffine h :=
  toAffine_iterate_dbl h _

theorem frac_cancel_left {a b c u v : ZMod p} (hb : b ≠ 0) (hc : c ≠ 0) (hv : v ≠ 0)
    (h : a * v = u * c) : a * b * (b * c)⁻¹ = u / v := by
  rw [div_eq_div_iff hc hv |>.mpr h |>.symm, div_eq_mul_inv, mul_inv]
  field_simp

theorem frac_cancel_right {a b c u v : ZMod p} (hb : b ≠ 0) (hc : c ≠ 0) (hv : v ≠ 0)
    (h : a * v = u * b) : c * a * (b * c)⁻¹ = u / v := by
  rw [div_eq_div_iff hb hv |>.mpr h |>.symm, div_eq_mul_inv, mul_inv]
  field_simp

variable {R : Point}

theorem addPrecomputed_x (hP : P.WellFormed) (hR : R.WellFormed) :
    (P.addPrecomputed R.toPrecomputed).x = (P.toAffine hP + R.toAffine hR).x := by
  have hp : 1 + d * P.x * R.x * P.y * R.y ≠ 0 := curve.den_add_ne_zero hP.onCurve hR.onCurve
  have hm : 1 - d * P.x * R.x * P.y * R.y ≠ 0 := curve.den_sub_ne_zero hP.onCurve hR.onCurve
  have h2 : 2 * P.Z * R.Z ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero hP.isUnit_Z.ne_zero) hR.isUnit_Z.ne_zero
  rw [Point.x, Edwards.Point.add_x]
  simp only [addPrecomputed, toPrecomputed, toAffine, show curve.d = d from rfl]
  rw [X_eq hP, Y_eq hP, T_eq hP, X_eq hR, Y_eq hR, T_eq hR]
  refine frac_cancel_left ?_ ?_ hp (by ring)
  · exact fun h0 => mul_ne_zero h2 hm (by linear_combination h0)
  · exact fun h0 => mul_ne_zero h2 hp (by linear_combination h0)

theorem addPrecomputed_y (hP : P.WellFormed) (hR : R.WellFormed) :
    (P.addPrecomputed R.toPrecomputed).y = (P.toAffine hP + R.toAffine hR).y := by
  have hp : 1 + d * P.x * R.x * P.y * R.y ≠ 0 := curve.den_add_ne_zero hP.onCurve hR.onCurve
  have hm : 1 - d * P.x * R.x * P.y * R.y ≠ 0 := curve.den_sub_ne_zero hP.onCurve hR.onCurve
  have h2 : 2 * P.Z * R.Z ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero hP.isUnit_Z.ne_zero) hR.isUnit_Z.ne_zero
  rw [Point.y, Edwards.Point.add_y]
  simp only [addPrecomputed, toPrecomputed, toAffine, show curve.d = d from rfl]
  rw [X_eq hP, Y_eq hP, T_eq hP, X_eq hR, Y_eq hR, T_eq hR]
  refine frac_cancel_right ?_ ?_ hm (by ring)
  · exact fun h0 => mul_ne_zero h2 hm (by linear_combination h0)
  · exact fun h0 => mul_ne_zero h2 hp (by linear_combination h0)

theorem wellFormed_addPrecomputed (hP : P.WellFormed) (hR : R.WellFormed) :
    (P.addPrecomputed R.toPrecomputed).WellFormed
    where
  isUnit_Z := by
    have hp : 1 + d * P.x * R.x * P.y * R.y ≠ 0 := curve.den_add_ne_zero hP.onCurve hR.onCurve
    have hm : 1 - d * P.x * R.x * P.y * R.y ≠ 0 := curve.den_sub_ne_zero hP.onCurve hR.onCurve
    have h2 : 2 * P.Z * R.Z ≠ 0 :=
      mul_ne_zero (mul_ne_zero two_ne_zero hP.isUnit_Z.ne_zero) hR.isUnit_Z.ne_zero
    simp only [addPrecomputed, toPrecomputed]
    rw [T_eq hP, T_eq hR]
    exact
      (mul_ne_zero (fun h0 => mul_ne_zero h2 hm (by linear_combination h0))
          (fun h0 => mul_ne_zero h2 hp (by linear_combination h0))).isUnit
  onCurve := by
    rw [addPrecomputed_x hP hR, addPrecomputed_y hP hR]; exact (P.toAffine hP + R.toAffine hR).on
  t_spec := by
    simp only [addPrecomputed]; ring

/-- **`addPrecomputed` adds**, against a well-formed point's precomputed form. -/
theorem toAffine_addPrecomputed (hP : P.WellFormed) (hR : R.WellFormed) :
    (P.addPrecomputed R.toPrecomputed).toAffine (wellFormed_addPrecomputed hP hR) =
      P.toAffine hP + R.toAffine hR :=
  Edwards.Point.ext (addPrecomputed_x hP hR) (addPrecomputed_y hP hR)

theorem wellFormed_neg (h : P.WellFormed) : P.neg.WellFormed where
  isUnit_Z := h.isUnit_Z
  onCurve := by
    have hc := h.onCurve
    simp only [OnCurve, x, y, neg] at hc ⊢
    linear_combination hc
  t_spec := by
    simp only [neg]; linear_combination -h.t_spec

/-- **`neg` negates.** -/
theorem toAffine_neg (h : P.WellFormed) : P.neg.toAffine (wellFormed_neg h) = -P.toAffine h :=
  Edwards.Point.ext
    (by
      simp only [toAffine, Edwards.Point.neg_x, x, neg]; ring)
    rfl

theorem toPrecomputed_neg (P : Point) : P.neg.toPrecomputed = P.toPrecomputed.neg := by
  simp only [neg, toPrecomputed, PrecomputedPoint.neg, PrecomputedPoint.mk.injEq]
  refine ⟨?_, ?_, trivial, ?_⟩ <;> ring

theorem wellFormed_addPrecomputed_neg (hP : P.WellFormed) (hR : R.WellFormed) :
    (P.addPrecomputed R.toPrecomputed.neg).WellFormed := by
  rw [← toPrecomputed_neg]
  exact wellFormed_addPrecomputed hP (wellFormed_neg hR)

/-- **`addPrecomputed` of a negated precomputed point subtracts.** -/
theorem toAffine_addPrecomputed_neg (hP : P.WellFormed) (hR : R.WellFormed) :
    (P.addPrecomputed R.toPrecomputed.neg).toAffine (wellFormed_addPrecomputed_neg hP hR) =
      P.toAffine hP - R.toAffine hR := by
  rw [toAffine_congr (congrArg P.addPrecomputed (toPrecomputed_neg R)).symm _
      (wellFormed_addPrecomputed hP (wellFormed_neg hR)),
    toAffine_addPrecomputed hP (wellFormed_neg hR), toAffine_neg hR, sub_eq_add_neg]

/-! ## Representation up to `T` -/

/-- `P`'s `X, Y, Z` stand for `V`; `T` is not constrained. -/
structure Represents (P : Point) (V : Edwards.Point curve) : Prop where
  isUnit_Z : IsUnit P.Z
  x_eq : P.x = V.x
  y_eq : P.y = V.y

theorem represents_toAffine (h : P.WellFormed) : P.Represents (P.toAffine h) :=
  ⟨h.isUnit_Z, rfl, rfl⟩

/-- `P` with `T` recomputed from `X, Y, Z`. -/
def fixT (P : Point) : Point :=
  ⟨P.X, P.Y, P.Z, P.x * P.y * P.Z⟩

variable {V : Edwards.Point curve}

theorem Represents.wellFormed_fixT (h : P.Represents V) : P.fixT.WellFormed where
  isUnit_Z := h.isUnit_Z
  onCurve := by
    show OnCurve P.x P.y
    rw [h.x_eq, h.y_eq]
    exact V.on
  t_spec := by
    have hZ := h.isUnit_Z.ne_zero
    simp only [fixT, x, y]
    field_simp

theorem Represents.toAffine_fixT (h : P.Represents V) : P.fixT.toAffine h.wellFormed_fixT = V :=
  Edwards.Point.ext h.x_eq h.y_eq

/-- `T` does not matter. -/
theorem Represents.withT (h : P.Represents V) (t : ZMod p) :
    ({ P with T := t } : Point).Represents V :=
  ⟨h.isUnit_Z, h.x_eq, h.y_eq⟩

end Point

end Ed25519
