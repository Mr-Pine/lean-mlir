/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.Firedancer.Avx512.Spec.Quad
import SSA.Projects.Firedancer.Avx512.Spec.fd_r43x6_mul_fast

/-!
# What `fd_r43x6_quad_mul_fast` is specified to compute

`FD_R43X6_QUAD_MUL_FAST(R,P,Q)` is documented as

    [ fd_r43x6_mul_fast(PX,QX) fd_r43x6_mul_fast(PY,QY)
      fd_r43x6_mul_fast(PZ,QZ) fd_r43x6_mul_fast(PT,QT) ]

and that is exactly what this file says: the ℕ-level model is the *scalar*
`limb` of `Spec/fd_r43x6_mul_fast.lean`, applied at each of the four lanes of
the QUAD layout (`Spec/Quad.lean`). Ring correctness and the width table come
straight from the scalar file — `pack_limb_zmod` and `limb_lt_u4x` are used
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

/-- The four elements' output limbs: `quadMulLimb … j k` is limb `k` of the
product of element `j` of the two input QUADs, i.e. the scalar `limb` applied
lanewise. -/
def quadMulLimb (a b c d e f : Vector (BitVec 64) 8) : ℕ → ℕ → ℕ :=
  fun j k => limb (quadLimb a b c j) (quadLimb d e f j) k

/-- The three result vectors predicted by the specification. -/
def quadMulVec03 (a b c d e f : Vector (BitVec 64) 8) : Vector (BitVec 64) 8 :=
  quadVec (quadMulLimb a b c d e f) 0 3
def quadMulVec14 (a b c d e f : Vector (BitVec 64) 8) : Vector (BitVec 64) 8 :=
  quadVec (quadMulLimb a b c d e f) 1 4
def quadMulVec25 (a b c d e f : Vector (BitVec 64) 8) : Vector (BitVec 64) 8 :=
  quadVec (quadMulLimb a b c d e f) 2 5

/-- The complete result predicted for `fd_r43x6_quad_mul_fast`: the three
output vectors concatenated, as the lifted region returns them. -/
def quadMulVec (a b c d e f : Vector (BitVec 64) 8) : Vector (BitVec 64) 24 :=
  quadVec24 (quadMulLimb a b c d e f)

/-! The three thirds of that result. Output bounds are stated per third,
since `R43x6.UNN` is a predicate on eight-lane vectors. -/

@[simp] theorem slice03_quadMulVec (a b c d e f : Vector (BitVec 64) 8) :
    slice03 (quadMulVec a b c d e f) = quadMulVec03 a b c d e f := by
  rw [quadMulVec, quadVec24, slice03_quadCat]; rfl
@[simp] theorem slice14_quadMulVec (a b c d e f : Vector (BitVec 64) 8) :
    slice14 (quadMulVec a b c d e f) = quadMulVec14 a b c d e f := by
  rw [quadMulVec, quadVec24, slice14_quadCat]; rfl
@[simp] theorem slice25_quadMulVec (a b c d e f : Vector (BitVec 64) 8) :
    slice25 (quadMulVec a b c d e f) = quadMulVec25 a b c d e f := by
  rw [quadMulVec, quadVec24, slice25_quadCat]; rfl

/-! ## Ring correctness

Per element, this is the scalar theorem. -/

/-- **Ring correctness**, elementwise: the limbs `quadMulLimb` predicts for
element `j` decode to the product of the two decoded inputs in
`GF(2^255 - 19)`. -/
theorem pack_quadMulLimb_zmod (a b c d e f : Vector (BitVec 64) 8) (j : ℕ) :
    ((pack (quadMulLimb a b c d e f j) : ℕ) : ZMod p)
      = ((pack (quadLimb a b c j) : ℕ) : ZMod p)
        * ((pack (quadLimb d e f j) : ℕ) : ZMod p) :=
  pack_limb_zmod _ _

/-! ## Bounds

The four rows of the `fd_r43x6.h` width table, lifted lanewise. Each is the
scalar `limb_lt_u4x` under a `UNN` hypothesis on all six vectors. -/

/-- The scalar width table, applied at every lane of the QUAD. -/
private theorem quadMulLimb_lt_of (a b c d e f : Vector (BitVec 64) 8)
    (n N : ℕ) (hn : n ≤ 62)
    (scalar : ∀ x y : ℕ → ℕ, (∀ i < 6, x i < 2 ^ n) → (∀ i < 6, y i < 2 ^ n) →
      ∀ k < 6, limb x y k < N)
    (ha : R43x6.UNN n a) (hb : R43x6.UNN n b) (hc : R43x6.UNN n c)
    (hd : R43x6.UNN n d) (he : R43x6.UNN n e) (hf : R43x6.UNN n f)
    (j : ℕ) (hj : j < 4) (k : ℕ) (hk : k < 6) :
    quadMulLimb a b c d e f j k < N :=
  scalar _ _
    (fun i hi => quadLimb_lt a b c n hn ha hb hc j hj i hi)
    (fun i hi => quadLimb_lt d e f n hn hd he hf j hj i hi) k hk

/-- **`u44` in, `u62` out.** -/
theorem quadMulLimb_lt_u44 (a b c d e f : Vector (BitVec 64) 8)
    (ha : R43x6.U44 a) (hb : R43x6.U44 b) (hc : R43x6.U44 c)
    (hd : R43x6.U44 d) (he : R43x6.U44 e) (hf : R43x6.U44 f)
    (j : ℕ) (hj : j < 4) (k : ℕ) (hk : k < 6) :
    quadMulLimb a b c d e f j k < 2 ^ 62 :=
  quadMulLimb_lt_of a b c d e f 44 (2 ^ 62) (by omega) limb_lt_u44
    ha hb hc hd he hf j hj k hk

/-- **`u45` in, `u62` out.** -/
theorem quadMulLimb_lt_u45 (a b c d e f : Vector (BitVec 64) 8)
    (ha : R43x6.U45 a) (hb : R43x6.U45 b) (hc : R43x6.U45 c)
    (hd : R43x6.U45 d) (he : R43x6.U45 e) (hf : R43x6.U45 f)
    (j : ℕ) (hj : j < 4) (k : ℕ) (hk : k < 6) :
    quadMulLimb a b c d e f j k < 2 ^ 62 :=
  quadMulLimb_lt_of a b c d e f 45 (2 ^ 62) (by omega) limb_lt_u45
    ha hb hc hd he hf j hj k hk

/-- **`u46` in, `u62` out.** -/
theorem quadMulLimb_lt_u46 (a b c d e f : Vector (BitVec 64) 8)
    (ha : R43x6.U46 a) (hb : R43x6.U46 b) (hc : R43x6.U46 c)
    (hd : R43x6.U46 d) (he : R43x6.U46 e) (hf : R43x6.U46 f)
    (j : ℕ) (hj : j < 4) (k : ℕ) (hk : k < 6) :
    quadMulLimb a b c d e f j k < 2 ^ 62 :=
  quadMulLimb_lt_of a b c d e f 46 (2 ^ 62) (by omega) limb_lt_u46
    ha hb hc hd he hf j hj k hk

/-- **`u47` in, `u63` out.** -/
theorem quadMulLimb_lt_u47 (a b c d e f : Vector (BitVec 64) 8)
    (ha : R43x6.U47 a) (hb : R43x6.U47 b) (hc : R43x6.U47 c)
    (hd : R43x6.U47 d) (he : R43x6.U47 e) (hf : R43x6.U47 f)
    (j : ℕ) (hj : j < 4) (k : ℕ) (hk : k < 6) :
    quadMulLimb a b c d e f j k < 2 ^ 63 :=
  quadMulLimb_lt_of a b c d e f 47 (2 ^ 63) (by omega) limb_lt_u47
    ha hb hc hd he hf j hj k hk

/-- The bound the `BitVec.toInt` transfer needs: below `2^63` a lane is not
read back as negative. For a multiply this *is* the `u47` row of the table --
the scalar bound is `u63`, exactly on the boundary. -/
theorem quadMulLimb_lt_two_pow_63 (a b c d e f : Vector (BitVec 64) 8)
    (ha : R43x6.U47 a) (hb : R43x6.U47 b) (hc : R43x6.U47 c)
    (hd : R43x6.U47 d) (he : R43x6.U47 e) (hf : R43x6.U47 f)
    (j : ℕ) (hj : j < 4) (k : ℕ) (hk : k < 6) :
    quadMulLimb a b c d e f j k < 2 ^ 63 :=
  quadMulLimb_lt_u47 a b c d e f ha hb hc hd he hf j hj k hk

end Firedancer.Avx512
