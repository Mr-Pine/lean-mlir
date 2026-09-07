/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.Firedancer.Avx512.Spec.Quad
import SSA.Projects.Firedancer.Avx512.Spec.Field.fd_r43x6_mul_fast

/-!
# What `fd_r43x6_quad_mul_fast` is specified to compute

`FD_R43X6_QUAD_MUL_FAST(R,P,Q)` is documented as

    [ fd_r43x6_mul_fast(PX,QX) fd_r43x6_mul_fast(PY,QY)
      fd_r43x6_mul_fast(PZ,QZ) fd_r43x6_mul_fast(PT,QT) ]

and that is exactly what this file says: the ℕ-level model is the *scalar*
`limb` of `Spec/fd_r43x6_mul_fast.lean`, applied at each of the four lanes of
the QUAD layout (`Spec/Quad.lean`). Ring correctness and the width table come
straight from the scalar file — `decodeLimbs_limb_zmod` and `limb_lt_u4x` are used
unchanged, four times.

The implementation is *not* four calls to `fd_r43x6_mul_fast`, though: it is a
separate kernel with its own `vpmadd52` schedule, forming the same thirty-six
products per element but broadcasting limbs across half-vectors instead of
sliding accumulators. What is shared is the arithmetic, not the code, so the
denotation still has to be derived instruction by instruction — that is
`Avx512/Proof/fd_r43x6_quad_mul_fast_z*.lean`.

## Hypotheses

`R43x6.U47` on all six input vectors, i.e. every limb of every one of the
four elements of both QUADs is unreduced.

Unlike the scalar kernel there are **no zero-lane hypotheses**. The scalar
`fd_r43x6_mul_fast` needs `y[6] = y[7] = 0` because its accumulators multiply
against all eight lanes of `y` and the slides move lane-6/7 products into the
result. In a QUAD lanes 6 and 7 hold limbs 2 and 5 of elements 2 and 3, every
product stays inside one lane, and nothing is ignored.
-/

namespace Firedancer.Avx512
open LeanMLIR SLLVM
open InstCombine (LLVM)
open Quad

/-- The four elements' output limbs: `quadMulLimb … j k` is limb `k` of the
product of element `j` of the two input QUADs, i.e. the scalar `limb` applied
lanewise. -/
def quadMulLimb (x y : Quad) : Fin 4 → Fin 6 → ℕ :=
  fun j k => limb (quadLimb x.v03 x.v14 x.v25 j) (quadLimb y.v03 y.v14 y.v25 j) k

def quadMulResult (x y: Quad): Quad where
  v03 := quadVec (quadMulLimb x y) 0 3
  v14 := quadVec (quadMulLimb x y) 1 4
  v25 := quadVec (quadMulLimb x y) 2 5

/-! ## Ring correctness

Per element, this is the scalar theorem. -/

/-- **Ring correctness**, elementwise: the limbs `quadMulLimb` predicts for
element `j` decode to the product of the two decoded inputs in
`GF(2^255 - 19)`. -/
theorem decodeLimbs_quadMulLimb_zmod (x y : Quad) (j : Fin 4) :
    ((decodeNat (quadMulLimb x y j) : ℕ) : ZMod p)
      = ((decodeNat (laneFunc (x.vector j)) : ℕ) : ZMod p)
        * ((decodeNat (laneFunc (y.vector j)) : ℕ) : ZMod p) := by
  rw [laneFunc_vector, laneFunc_vector]
  exact decodeLimbs_limb_zmod _ _

/-! ## Bounds

The four rows of the `fd_r43x6.h` width table, lifted lanewise. Each is the
scalar `limb_lt_u4x` under a `UNN` hypothesis on all six vectors. -/

/-- The scalar width table, applied at every lane of the QUAD. -/
private theorem quadMulLimb_lt_of (x y: Quad)
    (n N : ℕ) (hn : n ≤ 62)
    (scalar : ∀ a b : Fin 6 → ℕ, (∀ i, a i < 2 ^ n) → (∀ i, b i < 2 ^ n) →
      ∀ k, limb a b k < N)
    (hx03 : R43x6.UNN n x.v03) (hx14 : R43x6.UNN n x.v14) (hx25 : R43x6.UNN n x.v25)
    (hy03 : R43x6.UNN n y.v03) (hy14 : R43x6.UNN n y.v14) (hy25 : R43x6.UNN n y.v25)
    (j : Fin 4) (k : Fin 6) :
    quadMulLimb x y j k < N :=
  scalar _ _
    (fun i => quadLimb_lt x n hn hx03 hx14 hx25 j i)
    (fun i => quadLimb_lt y n hn hy03 hy14 hy25 j i) k

/-- **`u44` in, `u62` out.** -/
theorem quadMulLimb_lt_u44 (x y : Quad)
    (hx03 : R43x6.U44 x.v03) (hx14 : R43x6.U44 x.v14) (hx25 : R43x6.U44 x.v25)
    (hy03 : R43x6.U44 y.v03) (hy14 : R43x6.U44 y.v14) (hy25 : R43x6.U44 y.v25)
    (j : Fin 4) (k : Fin 6) :
    quadMulLimb x y j k < 2 ^ 62 :=
  quadMulLimb_lt_of x y 44 (2 ^ 62) (by omega) limb_lt_u44
    hx03 hx14 hx25 hy03 hy14 hy25 j k

/-- **`u46` in, `7000·2^49` out**: the exact count (`limb_lt_u46_tight`),
lanewise. It is what makes the `fd_r43x6_ge_is_eq` differences `s62`. -/
theorem quadMulLimb_lt_u46_tight (x y : Quad)
    (hx03 : R43x6.U46 x.v03) (hx14 : R43x6.U46 x.v14) (hx25 : R43x6.U46 x.v25)
    (hy03 : R43x6.U46 y.v03) (hy14 : R43x6.U46 y.v14) (hy25 : R43x6.U46 y.v25)
    (j : Fin 4) (k : Fin 6) :
    quadMulLimb x y j k < 7000 * 2 ^ 49 :=
  quadMulLimb_lt_of x y 46 (7000 * 2 ^ 49) (by omega) limb_lt_u46_tight
    hx03 hx14 hx25 hy03 hy14 hy25 j k

/-- **`u47` in, `u63` out.** -/
theorem quadMulLimb_lt_u47 (x y : Quad)
    (hx03 : R43x6.U47 x.v03) (hx14 : R43x6.U47 x.v14) (hx25 : R43x6.U47 x.v25)
    (hy03 : R43x6.U47 y.v03) (hy14 : R43x6.U47 y.v14) (hy25 : R43x6.U47 y.v25)
    (j : Fin 4) (k : Fin 6) :
    quadMulLimb x y j k < 2 ^ 63 :=
  quadMulLimb_lt_of x y 47 (2 ^ 63) (by omega) limb_lt_u47
    hx03 hx14 hx25 hy03 hy14 hy25 j k

/-- The bound the `BitVec.toInt` transfer needs: below `2^63` a lane is not
read back as negative. For a multiply this *is* the `u47` row of the table --
the scalar bound is `u63`, exactly on the boundary. -/
theorem quadMulLimb_lt_two_pow_63 (x y : Quad)
    (hx03 : R43x6.U47 x.v03) (hx14 : R43x6.U47 x.v14) (hx25 : R43x6.U47 x.v25)
    (hy03 : R43x6.U47 y.v03) (hy14 : R43x6.U47 y.v14) (hy25 : R43x6.U47 y.v25)
    (j : Fin 4) (k : Fin 6) :
    quadMulLimb x y j k < 2 ^ 63 :=
  quadMulLimb_lt_u47 x y hx03 hx14 hx25 hy03 hy14 hy25 j k

end Firedancer.Avx512
