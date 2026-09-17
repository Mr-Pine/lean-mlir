/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SSA.Projects.Firedancer.Avx512.Spec.Quad
public import SSA.Projects.Firedancer.Avx512.Spec.Field.fd_r43x6_sqr_fast

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

@[expose] public section

namespace Firedancer.Avx512
open LeanMLIR SLLVM
open InstCombine (LLVM)

open Quad

/-- The four elements' output limbs: `quadSqrLimb … j k` is limb `k` of the
square of element `j` of the input QUAD, i.e. the scalar `sqLimb` applied
lanewise. -/
def quadSqrLimb (x : Quad) : QuadFunc :=
  fun j k => sqLimb (quadLimb x.v03 x.v14 x.v25 j) k

/-- The result QUAD predicted by the specification. -/
def quadSqrResult (x : Quad) : Quad where
  v03 := quadVec (quadSqrLimb x) 0 3
  v14 := quadVec (quadSqrLimb x) 1 4
  v25 := quadVec (quadSqrLimb x) 2 5

/-! ## Ring correctness

Per element, this is the scalar theorem. -/

/-- **Ring correctness**, elementwise: the limbs `quadSqrLimb` predicts for
element `j` decode to the square of the decoded input in `GF(2^255 - 19)`. -/
theorem decodeLimbs_quadSqrLimb_zmod (x : Quad) (j : Fin 4) :
    ((decodeNat (quadSqrLimb x j) : ℕ) : ZMod p)
      = ((decodeNat (laneFunc (x.vector j)) : ℕ) : ZMod p) ^ 2 := by
  rw [laneFunc_vector]
  exact decodeLimbs_sqLimb_zmod _

/-! ## Bounds

The four rows of the `fd_r43x6.h` width table for squaring
(`u44/u45/u46/u47` in, `u61/u61/u62/u62` out), lifted lanewise. -/

/-- The scalar width table, applied at every lane of the QUAD. -/
private theorem quadSqrLimb_lt_of (x : Quad)
    (n N : ℕ) (hn : n ≤ 62)
    (scalar : ∀ a : Fin 6 → ℕ, (∀ i, a i < 2 ^ n) → ∀ k, sqLimb a k < N)
    (h03 : R43x6.UNN n x.v03) (h14 : R43x6.UNN n x.v14) (h25 : R43x6.UNN n x.v25)
    (j : Fin 4) (k : Fin 6) :
    quadSqrLimb x j k < N :=
  scalar _ (fun i => quadLimb_lt x n hn h03 h14 h25 j i) k

/-- **`u44` in, `u61` out.** -/
theorem quadSqrLimb_lt_u44 (x : Quad)
    (h03 : R43x6.U44 x.v03) (h14 : R43x6.U44 x.v14) (h25 : R43x6.U44 x.v25)
    (j : Fin 4) (k : Fin 6) :
    quadSqrLimb x j k < 2 ^ 61 :=
  quadSqrLimb_lt_of x 44 (2 ^ 61) (by omega) sqLimb_lt_u44 h03 h14 h25 j k

/-- **`u47` in, `u62` out.** -/
theorem quadSqrLimb_lt_u47 (x : Quad)
    (h03 : R43x6.U47 x.v03) (h14 : R43x6.U47 x.v14) (h25 : R43x6.U47 x.v25)
    (j : Fin 4) (k : Fin 6) :
    quadSqrLimb x j k < 2 ^ 62 :=
  quadSqrLimb_lt_of x 47 (2 ^ 62) (by omega) sqLimb_lt_u47 h03 h14 h25 j k

/-- The bound the `BitVec.toInt` transfer needs: below `2^63`, a lane is not
read back as negative. -/
theorem quadSqrLimb_lt_two_pow_63 (x : Quad)
    (h03 : R43x6.U47 x.v03) (h14 : R43x6.U47 x.v14) (h25 : R43x6.U47 x.v25)
    (j : Fin 4) (k : Fin 6) :
    quadSqrLimb x j k < 2 ^ 63 := by
  have := quadSqrLimb_lt_u47 x h03 h14 h25 j k
  omega

end Firedancer.Avx512
