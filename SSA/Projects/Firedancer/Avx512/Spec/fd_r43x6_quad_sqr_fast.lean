/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.Firedancer.Avx512.Spec.Quad
import SSA.Projects.Firedancer.Avx512.Spec.fd_r43x6_sqr_fast

/-!
# What `fd_r43x6_quad_sqr_fast` is specified to compute

`FD_R43X6_QUAD_SQR_FAST(R,P)` is documented as

    [ fd_r43x6_sqr_fast(PX) fd_r43x6_sqr_fast(PY)
      fd_r43x6_sqr_fast(PZ) fd_r43x6_sqr_fast(PT) ]

so the ℕ-level model is the *scalar* `sqLimb` of
`Spec/fd_r43x6_sqr_fast.lean`, applied at each of the four lanes of the QUAD
layout (`Spec/Quad.lean`). Ring correctness and the width table come straight
from the scalar file, four times over.

The code is again a different kernel, and further from its scalar counterpart
than the multiply is. Both exploit `i <-> j` symmetry to form only twenty-one
products per element instead of thirty-six, but they split the columns
differently: the scalar version keeps one column per lane, while the quad
version packs column `k` and column `11 - k` into the two halves of one
vector (the `p0a`, `p19`, ... `p55` of `fd_r43x6_inl.h`, mirror-symmetric
about column 5). Two columns are therefore *split across both halves* of a
single vector and are re-joined by an extra add: column 5 out of `p55` and
column 6 out of `q66`.

The columns nevertheless come out equal to the scalar `sqCol` term by term,
up to commuting the operands of some products -- the quad kernel forms
`pl (2 * x 5) (x 1)` where the scalar forms `pl (2 * x 1) (x 5)`. Those agree
as naturals, and the derivation closes the gap with `ring_nf` at the last
step, exactly as the scalar `sqr` proof already does for its own reassociated
lanes.

## Hypotheses

`R43x6.U47` on the three input vectors. As for the multiply, there are **no
zero-lane hypotheses**: a QUAD has no ignored lanes.

One lane genuinely is a zero, but it is the *kernel's own* constant, not a
contract on the input -- `x4z = wwl_pack_halves(x14,1, _zz,0)` supplies a zero
against which `two_x14` is multiplied, so that the mirror-symmetric schedule
has a term to pair `2*p41l` with. It contributes `pl a 0 = ph a 0 = 0` and
drops out.
-/

namespace Firedancer.Avx512
open LeanMLIR SLLVM
open InstCombine (LLVM)

/-- The four elements' output limbs: `quadSqrLimb … j k` is limb `k` of the
square of element `j` of the input QUAD, i.e. the scalar `sqLimb` applied
lanewise. -/
def quadSqrLimb (a b c : Vector (BitVec 64) 8) : ℕ → ℕ → ℕ :=
  fun j k => sqLimb (quadLimb a b c j) k

/-- The three result vectors predicted by the specification. -/
def quadSqrVec03 (a b c : Vector (BitVec 64) 8) : Vector (BitVec 64) 8 :=
  quadVec (quadSqrLimb a b c) 0 3
def quadSqrVec14 (a b c : Vector (BitVec 64) 8) : Vector (BitVec 64) 8 :=
  quadVec (quadSqrLimb a b c) 1 4
def quadSqrVec25 (a b c : Vector (BitVec 64) 8) : Vector (BitVec 64) 8 :=
  quadVec (quadSqrLimb a b c) 2 5

/-- The complete result predicted for `fd_r43x6_quad_sqr_fast`: the three
output vectors concatenated, as the lifted region returns them. -/
def quadSqrVec (a b c : Vector (BitVec 64) 8) : Vector (BitVec 64) 24 :=
  quadVec24 (quadSqrLimb a b c)

/-! The three thirds of that result. Output bounds are stated per third,
since `R43x6.UNN` is a predicate on eight-lane vectors. -/

@[simp] theorem slice03_quadSqrVec (a b c : Vector (BitVec 64) 8) :
    slice03 (quadSqrVec a b c) = quadSqrVec03 a b c := by
  rw [quadSqrVec, quadVec24, slice03_quadCat]; rfl
@[simp] theorem slice14_quadSqrVec (a b c : Vector (BitVec 64) 8) :
    slice14 (quadSqrVec a b c) = quadSqrVec14 a b c := by
  rw [quadSqrVec, quadVec24, slice14_quadCat]; rfl
@[simp] theorem slice25_quadSqrVec (a b c : Vector (BitVec 64) 8) :
    slice25 (quadSqrVec a b c) = quadSqrVec25 a b c := by
  rw [quadSqrVec, quadVec24, slice25_quadCat]; rfl

/-! ## Ring correctness

Per element, this is the scalar theorem. -/

/-- **Ring correctness**, elementwise: the limbs `quadSqrLimb` predicts for
element `j` decode to the square of the decoded input in `GF(2^255 - 19)`. -/
theorem pack_quadSqrLimb_zmod (a b c : Vector (BitVec 64) 8) (j : ℕ) :
    ((pack (quadSqrLimb a b c j) : ℕ) : ZMod p)
      = ((pack (quadLimb a b c j) : ℕ) : ZMod p) ^ 2 :=
  pack_sqLimb_zmod _

/-! ## Bounds

The four rows of the `fd_r43x6.h` width table for squaring
(`u44/u45/u46/u47` in, `u61/u61/u62/u62` out), lifted lanewise. -/

/-- The scalar width table, applied at every lane of the QUAD. -/
private theorem quadSqrLimb_lt_of (a b c : Vector (BitVec 64) 8)
    (n N : ℕ) (hn : n ≤ 62)
    (scalar : ∀ x : ℕ → ℕ, (∀ i < 6, x i < 2 ^ n) → ∀ k < 6, sqLimb x k < N)
    (ha : R43x6.UNN n a) (hb : R43x6.UNN n b) (hc : R43x6.UNN n c)
    (j : ℕ) (hj : j < 4) (k : ℕ) (hk : k < 6) :
    quadSqrLimb a b c j k < N :=
  scalar _ (fun i hi => quadLimb_lt a b c n hn ha hb hc j hj i hi) k hk

/-- **`u44` in, `u61` out.** -/
theorem quadSqrLimb_lt_u44 (a b c : Vector (BitVec 64) 8)
    (ha : R43x6.U44 a) (hb : R43x6.U44 b) (hc : R43x6.U44 c)
    (j : ℕ) (hj : j < 4) (k : ℕ) (hk : k < 6) :
    quadSqrLimb a b c j k < 2 ^ 61 :=
  quadSqrLimb_lt_of a b c 44 (2 ^ 61) (by omega) sqLimb_lt_u44 ha hb hc j hj k hk

/-- **`u45` in, `u61` out.** -/
theorem quadSqrLimb_lt_u45 (a b c : Vector (BitVec 64) 8)
    (ha : R43x6.U45 a) (hb : R43x6.U45 b) (hc : R43x6.U45 c)
    (j : ℕ) (hj : j < 4) (k : ℕ) (hk : k < 6) :
    quadSqrLimb a b c j k < 2 ^ 61 :=
  quadSqrLimb_lt_of a b c 45 (2 ^ 61) (by omega) sqLimb_lt_u45 ha hb hc j hj k hk

/-- **`u46` in, `u62` out.** -/
theorem quadSqrLimb_lt_u46 (a b c : Vector (BitVec 64) 8)
    (ha : R43x6.U46 a) (hb : R43x6.U46 b) (hc : R43x6.U46 c)
    (j : ℕ) (hj : j < 4) (k : ℕ) (hk : k < 6) :
    quadSqrLimb a b c j k < 2 ^ 62 :=
  quadSqrLimb_lt_of a b c 46 (2 ^ 62) (by omega) sqLimb_lt_u46 ha hb hc j hj k hk

/-- **`u47` in, `u62` out.** -/
theorem quadSqrLimb_lt_u47 (a b c : Vector (BitVec 64) 8)
    (ha : R43x6.U47 a) (hb : R43x6.U47 b) (hc : R43x6.U47 c)
    (j : ℕ) (hj : j < 4) (k : ℕ) (hk : k < 6) :
    quadSqrLimb a b c j k < 2 ^ 62 :=
  quadSqrLimb_lt_of a b c 47 (2 ^ 62) (by omega) sqLimb_lt_u47 ha hb hc j hj k hk

/-- The bound the `BitVec.toInt` transfer needs: below `2^63`, a lane is not
read back as negative. -/
theorem quadSqrLimb_lt_two_pow_63 (a b c : Vector (BitVec 64) 8)
    (ha : R43x6.U47 a) (hb : R43x6.U47 b) (hc : R43x6.U47 c)
    (j : ℕ) (hj : j < 4) (k : ℕ) (hk : k < 6) :
    quadSqrLimb a b c j k < 2 ^ 63 := by
  have := quadSqrLimb_lt_u47 a b c ha hb hc j hj k hk
  omega

end Firedancer.Avx512
