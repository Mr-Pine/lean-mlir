/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.Firedancer.Avx512.Spec.fd_r43x6_quad_mul_fast
import SSA.Projects.Firedancer.Avx512.Spec.fd_r43x6_is_nonzero
import SSA.Projects.Firedancer.Curve

/-!
# What `fd_r43x6_ge_is_eq` is specified to compute

`FD_R43X6_GE_IS_EQ(X, Y)` decides whether two `FD_R43X6_QUAD`s, each holding a
curve point in the extended homogeneous coordinates of `Curve.lean`, represent
the *same* point. The C quotes RFC 8032's `__eq__` verbatim: rather than
dividing by the `Z`s it cross-multiplies,

    xn1 = X₁·Z₂    xn2 = X₂·Z₁    yn1 = Y₁·Z₂    yn2 = Y₂·Z₁

and answers `xn1 == xn2 and yn1 == yn2`. That this decides `SamePoint` is
`Ed25519.Point.samePoint_iff_cross_sub_eq_zero`, proved in `Curve.lean`;
everything here is the bridge between that statement and the machine
representation. It is the first specification at the *point* level, so the
file opens with the bridge itself: `Quad.toPoint` reads an `Ed25519.Point` out of
the QUAD layout of `Spec/Quad.lean`, one `decodeNat` per lane.

## The model

The implementation permutes the first QUAD by `(2,0,2,1)` and the second by
`(0,2,1,2)` and hands both to `FD_R43X6_QUAD_MUL_FAST`, so the product QUAD
carries `(xn2, xn1, yn2, yn1)` in lanes 0-3 -- and `T` never enters. The model
performs the permutation at the element level: each of the four products is
the scalar `limb` column sum of `Spec/fd_r43x6_mul_fast.lean` on the pair of
elements its lane multiplies, in the implementation's operand order.

Each difference then goes through `fd_r43x6_sub_fast`, which is `x + (p - y)`
limbwise -- the compiler reassociates it to `(x - y) + p`, equal on the nose
over `ℤ`, and `subFast` follows the compiled form. `fd_r43x6_p()` is `pLimbs`,
the nearly reduced representation of `p` itself; the bias costs nothing in the
field (`intCast_decodeLimbs_subFast`) and is what keeps every limb
`fd_r43x6_is_nonzero` sees inside a `long`. The decision `geIsEq` is two
`isNonzero`s (`Spec/fd_r43x6_is_nonzero.lean`) and an and.

## Hypotheses

* **`R43x6.U46` on all six vectors** -- the header: "X and Y should be
  FD_R43X6_QUAD holding u46 representations". It is what the width chain
  rests on: the products are below `7000·2^49 ≈ 0.85·2^62` (`crossLimb_lt`,
  the exact count behind the table's `u62` row -- the row itself is too weak
  here), so the differences are `s62` as the C comments claim (`subFast_s62`)
  and their limbs lie in `BcpPre (2^20)` (`bcpPre_subFast`), the range the
  `isNonzero` obligations are stated under and without which the region does
  not even denote to a value.

* **`IsUnit` of both `Z`s** -- what the cross-multiplication criterion needs;
  for the true, prime `p` it is exactly `Z ≠ 0`, i.e. the QUADs hold actual
  representations. Nothing else of `Point.WellFormed` is used: the permutes
  drop `T` before anything is computed, and the curve equation is irrelevant
  to equality of representations.

## The obligation

`GeIsEqDecides` at the end is the statement the lifted region will be measured
against, in the style of `IsNonzeroDecides`: under the two hypotheses, the
model returns `1` exactly on QUADs representing the same point. Its discharge
(in `Proof/`) composes `samePoint_iff_cross_sub_eq_zero` with
`IsNonzeroDecides` through the decode lemmas below.
-/

namespace Firedancer.Avx512
open LeanMLIR SLLVM
open InstCombine (LLVM)
open Ed25519
open Quad

/-! ## The four cross products

Lanes 0-3 of the product QUAD, each a scalar multiply of the two elements the
permutes pair up, first operand from the first QUAD. RFC 8032's names, `n` for
numerator: `xn1/xn2` are the x-coordinate numerators on the common denominator
`Z₁·Z₂`, `yn1/yn2` the y-coordinate ones. -/

/-- Lane 0, `xn2 = Z₁·X₂`. -/
def xn2Limb (x y: Quad) : Fin 6 → ℕ :=
  limb (x.vectorFunc 2) (y.vectorFunc 0)

/-- Lane 1, `xn1 = X₁·Z₂`. -/
def xn1Limb (x y: Quad) : Fin 6 → ℕ :=
  limb (x.vectorFunc 0) (y.vectorFunc 2)

/-- Lane 2, `yn2 = Z₁·Y₂`. -/
def yn2Limb (x y: Quad) : Fin 6 → ℕ :=
  limb (x.vectorFunc 2) (y.vectorFunc 1)

/-- Lane 3, `yn1 = Y₁·Z₂`. -/
def yn1Limb (x y: Quad) : Fin 6 → ℕ :=
  limb (x.vectorFunc 1) (y.vectorFunc 2)

/-! Each decodes to the product of coordinates it is named for; all four are
the scalar ring correctness `decodeLimbs_limb_zmod`. -/

theorem decodeLimbs_xn2Limb_zmod (x y: Quad) :
    ((decodeNat (xn2Limb x y) : ℕ) : ZMod p)
      = x.toPoint.Z * y.toPoint.X :=
  decodeLimbs_limb_zmod _ _

theorem decodeLimbs_xn1Limb_zmod (x y: Quad) :
    ((decodeNat (xn1Limb x y) : ℕ) : ZMod p)
      = x.toPoint.X * y.toPoint.Z :=
  decodeLimbs_limb_zmod _ _

theorem decodeLimbs_yn2Limb_zmod (x y: Quad) :
    ((decodeNat (yn2Limb x y) : ℕ) : ZMod p)
      = x.toPoint.Z * y.toPoint.Y :=
  decodeLimbs_limb_zmod _ _

theorem decodeLimbs_yn1Limb_zmod (x y: Quad) :
    ((decodeNat (yn1Limb x y) : ℕ) : ZMod p)
      = x.toPoint.Y * y.toPoint.Z :=
  decodeLimbs_limb_zmod _ _

/-! ## `fd_r43x6_sub_fast` -/

/-- `fd_r43x6_p()`: the nearly reduced representation of `p` itself, the
`dense<[8796093022189, …]>` constant of the region. -/
def pLimbs : Fin R43x6.limbCount → ℤ :=
  R43x6.limbs6 (2^43 - 19) (2^43 - 1) (2^43 - 1) (2^43 - 1) (2^43 - 1) (2^40 - 1)

theorem decodeLimbs_pLimbs : R43x6.decodeLimbs pLimbs = (p : ℤ) := by decide

/-- `fd_r43x6_sub_fast x y = x - y + p`, limbwise over `ℤ`: the difference of
two unsigned products with the representation of `p` added to bound the limbs
away from `long` underflow. -/
def subFast (x y : Fin 6 → ℕ) : Fin 6 → ℤ :=
  fun k => (x k : ℤ) - (y k : ℤ) + pLimbs k

/-- The bias vanishes in the field: `subFast` decodes to the difference of
its arguments' decodes. -/
theorem intCast_decodeLimbs_subFast (x y : Fin 6 → ℕ) :
    ((R43x6.decodeLimbs (subFast x y) : ℤ) : ZMod p)
      = ((decodeNat x : ℕ) : ZMod p) - ((decodeNat y : ℕ) : ZMod p) := by
  have h : R43x6.decodeLimbs (subFast x y)
      = ((decodeNat x : ℕ) : ℤ) - ((decodeNat y : ℕ) : ℤ)
        + R43x6.decodeLimbs pLimbs := by
    simp only [subFast, R43x6.decodeLimbs_eq, decodeNat_eq]
    push_cast
    ring
  rw [h, decodeLimbs_pLimbs]
  push_cast
  simp

/-! ## Bounds

The width chain of the C comments: `u46` elements make `u62` products, and
the differences are `s62`. The second claim needs more than the first -- a
`u62 - u62 + p` limb can exceed `2^62` by nearly `p`'s top limb -- so the
products are bounded by the exact count `7000·2^49 ≈ 0.85·2^62`
(`limb_lt_u46_tight`), which absorbs the `+ p`. -/

/-- **`u46` QUADs make cross products below `7000·2^49`**: the exact count of
the `u46` multiply row, at any two elements. Each of `xn1Limb`-`yn2Limb` is an
instance. -/
theorem crossLimb_lt {x y : Quad}
    (hx03 : R43x6.U46 x.v03) (hx14 : R43x6.U46 x.v14) (hx25 : R43x6.U46 x.v25)
    (hy03 : R43x6.U46 y.v03) (hy14 : R43x6.U46 y.v14) (hy25 : R43x6.U46 y.v25)
    (j j' : Fin 4) (k : Fin 6) :
    limb (x.vectorFunc j) (y.vectorFunc j') k < 7000 * 2 ^ 49 := by
  show limb (laneFunc (x.vector j)) (laneFunc (y.vector j')) k < 7000 * 2 ^ 49
  rw [laneFunc_vector, laneFunc_vector]
  exact limb_lt_u46_tight _ _
    (fun i => quadLimb_lt x 46 (by omega) hx03 hx14 hx25 j i)
    (fun i => quadLimb_lt y 46 (by omega) hy03 hy14 hy25 j' i) k

private theorem pLimbs_0 : pLimbs 0 = 2 ^ 43 - 19 := by decide
private theorem pLimbs_mid : ∀ i : Fin R43x6.limbCount,
    1 ≤ (i : ℕ) → (i : ℕ) ≤ 4 → pLimbs i = 2 ^ 43 - 1 := by decide
private theorem pLimbs_5 : pLimbs 5 = 2 ^ 40 - 1 := by decide

/-- **`u62 - u62 + p` is in the `is_nonzero` input range.** The differences
are the "s62" of the C comments; `BcpPre (2^20)` is the range the `isNonzero`
obligations hold under, and it accommodates them with two bits to spare. -/
theorem bcpPre_subFast {x y : Fin 6 → ℕ}
    (hx : ∀ k, x k < 2 ^ 62) (hy : ∀ k, y k < 2 ^ 62) :
    BcpPre (2 ^ 20) (subFast x y) := by
  have hx' : ∀ k : Fin 6, (x k : ℤ) < 2 ^ 62 := fun k => by
    exact_mod_cast hx k
  have hy' : ∀ k : Fin 6, (y k : ℤ) < 2 ^ 62 := fun k => by
    exact_mod_cast hy k
  refine ⟨?_, fun i h1 h4 => ?_, ?_⟩ <;> simp only [subFast]
  · rw [pLimbs_0]
    have := hx' 0; have := hy' 0
    omega
  · rw [pLimbs_mid i h1 h4]
    have := hx' i; have := hy' i
    omega
  · rw [pLimbs_5]
    have := hx' 5; have := hy' 5
    omega

private theorem pLimbs_bounds : ∀ k : Fin R43x6.limbCount,
    0 ≤ pLimbs k ∧ pLimbs k ≤ 2 ^ 43 - 1 := by decide

/-- **The differences are `s62`**, as the C comments at the two
`fd_r43x6_sub_fast` calls claim: with the products bounded by the exact count
`7000·2^49`, the `+ p` bias no longer reaches `2^62`. The `u62` row alone
could not give this -- `s63` is where the header's own conservative rules put
`u62 + s62`. -/
theorem subFast_s62 {x y : Fin 6 → ℕ}
    (hx : ∀ k, x k < 7000 * 2 ^ 49) (hy : ∀ k, y k < 7000 * 2 ^ 49) :
    ∀ k : Fin 6,
      -(2 ^ 62 - 1) ≤ subFast x y k ∧ subFast x y k ≤ 2 ^ 62 - 1 := by
  intro k
  have hx' : (x k : ℤ) < 7000 * 2 ^ 49 := by exact_mod_cast hx k
  have hy' : (y k : ℤ) < 7000 * 2 ^ 49 := by exact_mod_cast hy k
  have hp := pLimbs_bounds k
  simp only [subFast]
  omega

/-! ## The decision -/

/-- The `i32` `fd_r43x6_ge_is_eq` returns: `1` iff both cross-product
differences reduce to zero. The compiled readout is `(b ^ 1) & ~a` on the two
`{0,1}` results, which is the same and. -/
def geIsEq (x y : Quad) : BitVec 32 :=
  let X := x.toPoint
  let Y := y.toPoint
  if ((X.X * Y.Z) - (X.Z * Y.X)) = 0
      ∧ ((X.Y * Y.Z) - (X.Z * Y.Y)) = 0
  then 1 else 0

/-- **The decision is point equality.** On two `u46` QUADs whose `Z`s are
invertible, the model returns `1` when they represent the same curve point and
`0` otherwise -- the header's contract as one equation, `SamePoint` being
decidable. Discharged in `Proof/` by composing
`Ed25519.Point.samePoint_iff_cross_sub_eq_zero` with `IsNonzeroDecides`,
through `intCast_decodeLimbs_subFast` and the four cross-product decodes. -/
def GeIsEqDecides (x y : Quad) : Prop :=
  R43x6.U46 x.v03 → R43x6.U46 x.v14 → R43x6.U46 x.v25 →
  R43x6.U46 y.v03 → R43x6.U46 y.v14 → R43x6.U46 y.v25 →
  IsUnit x.toPoint.Z → IsUnit y.toPoint.Z →
    geIsEq x y
      = if x.toPoint.SamePoint y.toPoint then 1 else 0

/-! ## Sanity checks

The model is executable, so the criterion can be watched deciding actual
representations. Test QUADs are built limb by limb: element `j` of `(a,b,c)`
has limbs `(a[j], b[j], c[j], a[j+4], b[j+4], c[j+4])`. -/

private def v0 : Vector (BitVec 64) 8 := #v[0, 0, 0, 0, 0, 0, 0, 0]

/-- The scale factor the criterion has to see through: `(0,2,2,0)` is the
neutral point `(0,1,1,0)` at `Z = 2`. -/
example : geIsEq ⟨#v[0, 1, 1, 0, 0, 0, 0, 0], v0, v0⟩
                 ⟨#v[0, 2, 2, 0, 0, 0, 0, 0], v0, v0⟩ = 1 := by decide

/-- A multi-limb scale factor, `Z = 2^43 + 1`. -/
example : geIsEq ⟨#v[0, 1, 1, 0, 0, 0, 0, 0], v0, v0⟩
                 ⟨#v[0, 1, 1, 0, 0, 0, 0, 0], #v[0, 1, 1, 0, 0, 0, 0, 0], v0⟩ = 1 := by
  decide

/-- `y` differs: `(0, 1)` is not `(0, 1/2)`. -/
example : geIsEq ⟨#v[0, 1, 1, 0, 0, 0, 0, 0], v0, v0⟩
                 ⟨#v[0, 1, 2, 0, 0, 0, 0, 0], v0, v0⟩ = 0 := by decide

/-- `x` differs: `(0, 1)` is not `(1, 1)`. -/
example : geIsEq ⟨#v[0, 1, 1, 0, 0, 0, 0, 0], v0, v0⟩
                 ⟨#v[1, 1, 1, 1, 0, 0, 0, 0], v0, v0⟩ = 0 := by decide

end Firedancer.Avx512
