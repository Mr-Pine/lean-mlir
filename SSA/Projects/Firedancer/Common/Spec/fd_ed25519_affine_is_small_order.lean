/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.Firedancer.Curve

/-!
# The eight low-order points, and the test `fd_ed25519_affine_is_small_order` runs

Backend-independent: this file is about `ZMod p` and the curve, and mentions no
memory, no limbs and no region. Both backends' specifications for
`fd_ed25519_affine_is_small_order` are stated with `lowOrder`, the eight points
listed here; `IsSmallOrderTest` is the disjunction the regions literally
compute, and `isSmallOrderTest_iff_mem` is the bridge between the two.

`fd_curve25519.h:105` lists the eight points of order dividing 8, in compressed
form, and then takes the shortcut the two regions implement: for an *affine*
point (`Z = 1`),

    X = 0  ∨  Y = 0  ∨  Y = y0  ∨  Y = y1

where `y0`, `y1` are the two globals `@fd_ed25519_order8_point_y{0,1}`. The
shortcut is a statement about `Y` alone in six of the eight cases, which is why
it is cheap and also why it needs `Z = 1`: on a scaled representation `Y` is not
the affine `y`.

`lowOrder` is that list of eight, decompressed. Which `x` goes with which `y` is
forced by the curve equation up to sign, and both signs occur, so each `y` value
contributes two points:

| `y` | `x` | order |
|---|---|---|
| `1` | `0` | 1 |
| `-1` | `0` | 2 |
| `0` | `±sqrtm1` | 4 |
| `y0` | `±order8_x` | 8 |
| `y1 = -y0` | `±order8_x` | 8 |

That these eight are *exactly* the points of order dividing 8 is not proved here
and cannot be: the group law is not formalised in this development (see
`Curve.lean`, which stops at the representation and cross-multiplication). What
is proved is the part the specifications actually rest on -- that the test
holds, on the curve with `Z = 1`, exactly for the eight coordinate pairs
listed. The order labels come from the C comment and RFC 8032 and are
documentation.
-/

namespace Ed25519

/-! ## The two constants the globals hold -/

/-- `@fd_ed25519_order8_point_y0`: the `y` of the two order-8 points that
`fd_curve25519_tables.c` decodes from
`26e8958fc2b227b045c3f489f2ef98f0d5dfac05d3c63339b13802886d53fc05`. -/
def order8_y0 : ZMod p :=
  2707385501144840649318225287225658788936804267575313519463743609750303402022

/-- `@fd_ed25519_order8_point_y1`, from
`c7176a703d4dd84fba3c0b760d10670f2a2053fa2c39ccc64ec7fd7792ac037a`. -/
def order8_y1 : ZMod p :=
  55188659117513257062467267217118295137698188065244968500265048394206261417927

/-- The two globals are negatives: `y1 = -y0`. The C table decodes them
independently, so this is checked rather than assumed. -/
theorem order8_y1_eq_neg : order8_y1 = -order8_y0 := by decide +kernel

/-- The `x` shared by all four order-8 points, up to sign: the even root of
`(y0² - 1)/(d·y0² + 1)`, which the C comment prints as `4a…`. -/
def order8_x : ZMod p :=
  14399317868200118260347934320527232580618823971194345261214217575416788799818

/-- `order8_x` is a root of the curve equation's `x²` at `y = y0`, in the
cleared-denominator form `Curve.lean` states decompression with. -/
theorem order8_x_sq : order8_x ^ 2 * (d * order8_y0 ^ 2 + 1) = order8_y0 ^ 2 - 1 := by
  decide +kernel

/-! ## The eight points -/

/-- The eight points of order dividing 8, as affine `(x, y)` pairs, in the
order `fd_curve25519.h:105` lists them: `P0`, `P1`, `±P2`, `±P3`, `±P4`. -/
def lowOrder : List (ZMod p × ZMod p) :=
  [(0, 1), (0, -1),
   (sqrtm1, 0), (-sqrtm1, 0),
   (order8_x, order8_y0), (-order8_x, order8_y0),
   (order8_x, order8_y1), (-order8_x, order8_y1)]

/-- All eight are on the curve. -/
theorem onCurve_of_mem_lowOrder {q : ZMod p × ZMod p} (hq : q ∈ lowOrder) :
    OnCurve q.1 q.2 := by
  fin_cases hq <;> simp only [OnCurve] <;> decide +kernel

/-! ## The test

The disjunction the two regions compute, stated on the *representation* rather
than on the affine point: the regions read `X` and `Y` out of the point struct
with `fd_ed25519_point_to` and never divide by `Z`. -/

/-- `X = 0 | Y = 0 | Y == y0 | Y == y1`, the four `i32`s the regions `or`
together. -/
def IsSmallOrderTest (P : Point) : Prop :=
  P.X = 0 ∨ P.Y = 0 ∨ P.Y = order8_y0 ∨ P.Y = order8_y1

instance (P : Point) : Decidable (IsSmallOrderTest P) :=
  inferInstanceAs (Decidable (_ ∨ _ ∨ _ ∨ _))

/-! ## What the test decides

Three square roots, one per branch of the disjunction. Each is the same step:
the curve equation pins `x²` (or `y²`), and a field has two square roots. -/

/-- Two elements with equal squares differ by a sign. `ZMod p` is a field --
`Prime.lean` supplies `Fact (Nat.Prime p)` -- so `a² - b²` factors and one
factor vanishes. -/
theorem sq_eq_sq_iff' {a b : ZMod p} : a ^ 2 = b ^ 2 ↔ a = b ∨ a = -b := by
  constructor
  · intro h
    have hf : (a - b) * (a + b) = 0 := by linear_combination h
    rcases mul_eq_zero.mp hf with h' | h'
    · exact Or.inl (sub_eq_zero.mp h')
    · exact Or.inr (eq_neg_of_add_eq_zero_left h')
  · rintro (rfl | rfl) <;> ring

/-- On an affine representation the projective `X` *is* the affine `x`. This is
where `Z = 1` is spent: the regions test `X` and `Y`, the curve equation
constrains `x` and `y`. -/
@[simp] theorem x_of_Z_eq_one {P : Point} (hZ : P.Z = 1) : P.x = P.X := by
  simp [Point.x, hZ]

/-- ... and likewise for `Y`. -/
@[simp] theorem y_of_Z_eq_one {P : Point} (hZ : P.Z = 1) : P.y = P.Y := by
  simp [Point.y, hZ]

/-- **The test decides membership in `lowOrder`**, for a point on the curve
given in affine form (`Z = 1`).

Forward, branch by branch: `X = 0` leaves `Y² = 1`; `Y = 0` leaves
`X² = -1 = sqrtm1²`; `Y = y0` (and `Y = y1 = -y0`, which has the same square)
leaves `X²·(d·y0² + 1) = y0² - 1 = order8_x²·(d·y0² + 1)`, and the denominator
`d·y0² + 1` is non-zero because `d` is not a square (`denom_ne_zero`). -/
theorem isSmallOrderTest_iff_mem {P : Point} (hZ : P.Z = 1)
    (hc : OnCurve P.x P.y) : IsSmallOrderTest P ↔ (P.X, P.Y) ∈ lowOrder := by
  rw [x_of_Z_eq_one hZ, y_of_Z_eq_one hZ] at hc
  simp only [IsSmallOrderTest, lowOrder, List.mem_cons, List.not_mem_nil, or_false,
    Prod.mk.injEq]
  constructor
  · rintro (hX | hY | hY | hY)
    · -- `X = 0`: the curve equation is `Y² = 1`.
      have h : P.Y ^ 2 = 1 ^ 2 := by rw [OnCurve, hX] at hc; linear_combination hc
      rcases sq_eq_sq_iff'.mp h with h' | h'
      · exact Or.inl ⟨hX, h'⟩
      · exact Or.inr (Or.inl ⟨hX, by simpa using h'⟩)
    · -- `Y = 0`: the curve equation is `X² = -1 = sqrtm1²`.
      have h : P.X ^ 2 = sqrtm1 ^ 2 := by
        rw [OnCurve, hY] at hc; rw [sqrtm1_sq]; linear_combination -hc
      rcases sq_eq_sq_iff'.mp h with h' | h'
      · exact Or.inr (Or.inr (Or.inl ⟨h', hY⟩))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h', hY⟩)))
    · -- `Y = y0`: `X²` is pinned once the denominator is cleared.
      have hden : d * order8_y0 ^ 2 + 1 ≠ 0 := denom_ne_zero order8_y0
      have h : P.X ^ 2 = order8_x ^ 2 := by
        rw [OnCurve, hY] at hc
        refine mul_right_cancel₀ hden ?_
        rw [order8_x_sq]; linear_combination -hc
      rcases sq_eq_sq_iff'.mp h with h' | h'
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h', hY⟩))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h', hY⟩)))))
    · -- `Y = y1 = -y0`: same square, so the same two roots.
      have hden : d * order8_y0 ^ 2 + 1 ≠ 0 := denom_ne_zero order8_y0
      have hsq : P.Y ^ 2 = order8_y0 ^ 2 := by rw [hY, order8_y1_eq_neg]; ring
      have h : P.X ^ 2 = order8_x ^ 2 := by
        rw [OnCurve] at hc
        refine mul_right_cancel₀ hden ?_
        rw [order8_x_sq]; linear_combination -hc + (1 - d * P.X ^ 2) * hsq
      rcases sq_eq_sq_iff'.mp h with h' | h'
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h', hY⟩))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h', hY⟩))))))
  · rintro (⟨hX, -⟩ | ⟨hX, -⟩ | ⟨-, hY⟩ | ⟨-, hY⟩ | ⟨-, hY⟩ | ⟨-, hY⟩ | ⟨-, hY⟩ | ⟨-, hY⟩)
    · exact Or.inl hX
    · exact Or.inl hX
    · exact Or.inr (Or.inl hY)
    · exact Or.inr (Or.inl hY)
    · exact Or.inr (Or.inr (Or.inl hY))
    · exact Or.inr (Or.inr (Or.inl hY))
    · exact Or.inr (Or.inr (Or.inr hY))
    · exact Or.inr (Or.inr (Or.inr hY))

/-! ## How the region combines the four flags

The one place this file mentions the regions' `i32`s. Both backends `or`
together four results that are each `0` or `1`, and this is what that `or` is:
the flag of the disjunction. -/

/-- Two `0`/`1` flags `or`ed is the flag of their disjunction. -/
theorem or_ite_or {b c : Prop} [Decidable b] [Decidable c] :
    ((if b then 1#32 else 0#32) ||| (if c then 1#32 else 0#32) : BitVec 32)
      = if b ∨ c then 1#32 else 0#32 := by
  by_cases hb : b <;> by_cases hc : c <;> simp [hb, hc]

end Ed25519
