/-
Released under Apache 2.0 license as described in the file LICENSE.
NOTE: the bulk of this file was machine-generated; the structure mirrors
the data flow of `fd_r43x6_quad_sqr_fast`.
-/
import SSA.Projects.Firedancer.Avx512.Mlir.fd_r43x6_quad_sqr_fast
import SSA.Projects.Firedancer.Avx512.Proof.Mem
import SSA.Projects.Firedancer.Avx512.Spec.fd_r43x6_quad_sqr_fast

/-!
# `fd_r43x6_quad_sqr_fast` squares four field elements at once

This is the kernel lifted **verbatim** -- three `!llvm.ptr` out-parameters and
three `llvm.store`s, with no extraction probe. The derivation shows the region
denotes to exactly three whole-vector stores of the specified results;
`Proof/Mem.lean` turns that into a statement about memory.

Every intermediate is introduced as a `let` at the point the program computes
it, under the name `fd_r43x6_inl.h` gives it, so the derivation reads against
the C line by line. Each step names in its `with` list exactly the values it
reads; `simp only` zeta-delta-unfolds those and leaves the rest folded.

The kernel packs column `k` and column `11 - k` into the two halves of one
vector, so an operand carries different limbs in its two halves. Two columns
straddle both halves and are re-joined by an extra add: column 5 out of `p55`
and column 6 out of `q66`.

## Hypotheses

`R43x6.U47` on the three input vectors. There are no zero-lane hypotheses: a
QUAD has no ignored lanes. The one zero the kernel multiplies against is its
own constant `x4z`, not a contract on the input.
-/

namespace Firedancer.Avx512
open LeanMLIR SLLVM
open InstCombine (LLVM)

/-! ## The result lanes, against the specification

One lemma per lane of the result, in the vocabulary the derivation
leaves behind: its `let`s are zeta-unfolded down to lanes, while the
specification still reads `quadSqrLimb … j`. Proving these separately
keeps the last step of the derivation a rewrite rather than a
twenty-four-fold re-normalisation of the whole result. -/

private theorem lane_0 (x : Quad) :
    (((0) + (pl (x.v03[0].toNat) (x.v03[0].toNat))) + ((((ph (2 * x.v03[4].toNat) (x.v25[0].toNat) + ph (2 * x.v14[4].toNat) 0) + (pl (x.v03[4].toNat) (x.v03[4].toNat) + pl (2 * x.v25[4].toNat) (x.v14[0].toNat) + pl (2 * x.v25[0].toNat) (x.v14[4].toNat))) + (ph (2 * x.v03[0].toNat) (x.v25[4].toNat) + ph (2 * x.v14[0].toNat) (x.v14[4].toNat))) * 128)) + ((((ph (2 * x.v03[4].toNat) (x.v25[0].toNat) + ph (2 * x.v14[4].toNat) 0) + (pl (x.v03[4].toNat) (x.v03[4].toNat) + pl (2 * x.v25[4].toNat) (x.v14[0].toNat) + pl (2 * x.v25[0].toNat) (x.v14[4].toNat))) + (ph (2 * x.v03[0].toNat) (x.v25[4].toNat) + ph (2 * x.v14[0].toNat) (x.v14[4].toNat))) * 24)
      = quadSqrLimb x 0 0 := by
  simp only [quadSqrLimb, sqLimb, sqCol, ph, pl, quadLimb, vlane,
    Fin.reduceCastAdd, Fin.reduceAddNat, Nat.mul_comm, Nat.mul_left_comm, Nat.zero_div, Nat.zero_mul]
  ring_nf

private theorem lane_1 (x : Quad) :
    (((0) + (pl (x.v03[1].toNat) (x.v03[1].toNat))) + ((((ph (2 * x.v03[5].toNat) (x.v25[1].toNat) + ph (2 * x.v14[5].toNat) 0) + (pl (x.v03[5].toNat) (x.v03[5].toNat) + pl (2 * x.v25[5].toNat) (x.v14[1].toNat) + pl (2 * x.v25[1].toNat) (x.v14[5].toNat))) + (ph (2 * x.v03[1].toNat) (x.v25[5].toNat) + ph (2 * x.v14[1].toNat) (x.v14[5].toNat))) * 128)) + ((((ph (2 * x.v03[5].toNat) (x.v25[1].toNat) + ph (2 * x.v14[5].toNat) 0) + (pl (x.v03[5].toNat) (x.v03[5].toNat) + pl (2 * x.v25[5].toNat) (x.v14[1].toNat) + pl (2 * x.v25[1].toNat) (x.v14[5].toNat))) + (ph (2 * x.v03[1].toNat) (x.v25[5].toNat) + ph (2 * x.v14[1].toNat) (x.v14[5].toNat))) * 24)
      = quadSqrLimb x 1 0 := by
  simp only [quadSqrLimb, sqLimb, sqCol, ph, pl, quadLimb, vlane,
    Fin.reduceCastAdd, Fin.reduceAddNat, Nat.mul_comm, Nat.mul_left_comm, Nat.zero_div, Nat.zero_mul]
  ring_nf

private theorem lane_2 (x : Quad) :
    (((0) + (pl (x.v03[2].toNat) (x.v03[2].toNat))) + ((((ph (2 * x.v03[6].toNat) (x.v25[2].toNat) + ph (2 * x.v14[6].toNat) 0) + (pl (x.v03[6].toNat) (x.v03[6].toNat) + pl (2 * x.v25[6].toNat) (x.v14[2].toNat) + pl (2 * x.v25[2].toNat) (x.v14[6].toNat))) + (ph (2 * x.v03[2].toNat) (x.v25[6].toNat) + ph (2 * x.v14[2].toNat) (x.v14[6].toNat))) * 128)) + ((((ph (2 * x.v03[6].toNat) (x.v25[2].toNat) + ph (2 * x.v14[6].toNat) 0) + (pl (x.v03[6].toNat) (x.v03[6].toNat) + pl (2 * x.v25[6].toNat) (x.v14[2].toNat) + pl (2 * x.v25[2].toNat) (x.v14[6].toNat))) + (ph (2 * x.v03[2].toNat) (x.v25[6].toNat) + ph (2 * x.v14[2].toNat) (x.v14[6].toNat))) * 24)
      = quadSqrLimb x 2 0 := by
  simp only [quadSqrLimb, sqLimb, sqCol, ph, pl, quadLimb, vlane,
    Fin.reduceCastAdd, Fin.reduceAddNat, Nat.mul_comm, Nat.mul_left_comm, Nat.zero_div, Nat.zero_mul]
  ring_nf

private theorem lane_3 (x : Quad) :
    (((0) + (pl (x.v03[3].toNat) (x.v03[3].toNat))) + ((((ph (2 * x.v03[7].toNat) (x.v25[3].toNat) + ph (2 * x.v14[7].toNat) 0) + (pl (x.v03[7].toNat) (x.v03[7].toNat) + pl (2 * x.v25[7].toNat) (x.v14[3].toNat) + pl (2 * x.v25[3].toNat) (x.v14[7].toNat))) + (ph (2 * x.v03[3].toNat) (x.v25[7].toNat) + ph (2 * x.v14[3].toNat) (x.v14[7].toNat))) * 128)) + ((((ph (2 * x.v03[7].toNat) (x.v25[3].toNat) + ph (2 * x.v14[7].toNat) 0) + (pl (x.v03[7].toNat) (x.v03[7].toNat) + pl (2 * x.v25[7].toNat) (x.v14[3].toNat) + pl (2 * x.v25[3].toNat) (x.v14[7].toNat))) + (ph (2 * x.v03[3].toNat) (x.v25[7].toNat) + ph (2 * x.v14[3].toNat) (x.v14[7].toNat))) * 24)
      = quadSqrLimb x 3 0 := by
  simp only [quadSqrLimb, sqLimb, sqCol, ph, pl, quadLimb, vlane,
    Fin.reduceCastAdd, Fin.reduceAddNat, Nat.mul_comm, Nat.mul_left_comm, Nat.zero_div, Nat.zero_mul]
  ring_nf

private theorem lane_4 (x : Quad) :
    (((ph (x.v14[0].toNat) (x.v14[0].toNat) + ph (2 * x.v03[0].toNat) (x.v25[0].toNat)) + (pl (2 * x.v03[0].toNat) (x.v03[4].toNat) + pl (2 * x.v14[0].toNat) (x.v25[0].toNat))) + ((((ph (x.v14[4].toNat) (x.v14[4].toNat) + ph (2 * x.v03[4].toNat) (x.v25[4].toNat)) + (pl (2 * x.v25[4].toNat) (x.v14[4].toNat))) + (0)) * 128)) + ((((ph (x.v14[4].toNat) (x.v14[4].toNat) + ph (2 * x.v03[4].toNat) (x.v25[4].toNat)) + (pl (2 * x.v25[4].toNat) (x.v14[4].toNat))) + (0)) * 24)
      = quadSqrLimb x 0 3 := by
  simp only [quadSqrLimb, sqLimb, sqCol, ph, pl, quadLimb, vlane,
    Fin.reduceCastAdd, Fin.reduceAddNat, Nat.mul_comm, Nat.mul_left_comm]
  ring_nf

private theorem lane_5 (x : Quad) :
    (((ph (x.v14[1].toNat) (x.v14[1].toNat) + ph (2 * x.v03[1].toNat) (x.v25[1].toNat)) + (pl (2 * x.v03[1].toNat) (x.v03[5].toNat) + pl (2 * x.v14[1].toNat) (x.v25[1].toNat))) + ((((ph (x.v14[5].toNat) (x.v14[5].toNat) + ph (2 * x.v03[5].toNat) (x.v25[5].toNat)) + (pl (2 * x.v25[5].toNat) (x.v14[5].toNat))) + (0)) * 128)) + ((((ph (x.v14[5].toNat) (x.v14[5].toNat) + ph (2 * x.v03[5].toNat) (x.v25[5].toNat)) + (pl (2 * x.v25[5].toNat) (x.v14[5].toNat))) + (0)) * 24)
      = quadSqrLimb x 1 3 := by
  simp only [quadSqrLimb, sqLimb, sqCol, ph, pl, quadLimb, vlane,
    Fin.reduceCastAdd, Fin.reduceAddNat, Nat.mul_comm, Nat.mul_left_comm]
  ring_nf

private theorem lane_6 (x : Quad) :
    (((ph (x.v14[2].toNat) (x.v14[2].toNat) + ph (2 * x.v03[2].toNat) (x.v25[2].toNat)) + (pl (2 * x.v03[2].toNat) (x.v03[6].toNat) + pl (2 * x.v14[2].toNat) (x.v25[2].toNat))) + ((((ph (x.v14[6].toNat) (x.v14[6].toNat) + ph (2 * x.v03[6].toNat) (x.v25[6].toNat)) + (pl (2 * x.v25[6].toNat) (x.v14[6].toNat))) + (0)) * 128)) + ((((ph (x.v14[6].toNat) (x.v14[6].toNat) + ph (2 * x.v03[6].toNat) (x.v25[6].toNat)) + (pl (2 * x.v25[6].toNat) (x.v14[6].toNat))) + (0)) * 24)
      = quadSqrLimb x 2 3 := by
  simp only [quadSqrLimb, sqLimb, sqCol, ph, pl, quadLimb, vlane,
    Fin.reduceCastAdd, Fin.reduceAddNat, Nat.mul_comm, Nat.mul_left_comm]
  ring_nf

private theorem lane_7 (x : Quad) :
    (((ph (x.v14[3].toNat) (x.v14[3].toNat) + ph (2 * x.v03[3].toNat) (x.v25[3].toNat)) + (pl (2 * x.v03[3].toNat) (x.v03[7].toNat) + pl (2 * x.v14[3].toNat) (x.v25[3].toNat))) + ((((ph (x.v14[7].toNat) (x.v14[7].toNat) + ph (2 * x.v03[7].toNat) (x.v25[7].toNat)) + (pl (2 * x.v25[7].toNat) (x.v14[7].toNat))) + (0)) * 128)) + ((((ph (x.v14[7].toNat) (x.v14[7].toNat) + ph (2 * x.v03[7].toNat) (x.v25[7].toNat)) + (pl (2 * x.v25[7].toNat) (x.v14[7].toNat))) + (0)) * 24)
      = quadSqrLimb x 3 3 := by
  simp only [quadSqrLimb, sqLimb, sqCol, ph, pl, quadLimb, vlane,
    Fin.reduceCastAdd, Fin.reduceAddNat, Nat.mul_comm, Nat.mul_left_comm]
  ring_nf

private theorem lane_8 (x : Quad) :
    (((ph (x.v03[0].toNat) (x.v03[0].toNat)) + (pl (2 * x.v03[0].toNat) (x.v14[0].toNat))) + (((ph (x.v03[4].toNat) (x.v03[4].toNat) + ph (2 * x.v25[4].toNat) (x.v14[0].toNat) + ph (2 * x.v25[0].toNat) (x.v14[4].toNat)) + (pl (2 * x.v03[4].toNat) (x.v14[4].toNat) + pl (2 * x.v25[0].toNat) (x.v25[4].toNat))) * 128)) + (((ph (x.v03[4].toNat) (x.v03[4].toNat) + ph (2 * x.v25[4].toNat) (x.v14[0].toNat) + ph (2 * x.v25[0].toNat) (x.v14[4].toNat)) + (pl (2 * x.v03[4].toNat) (x.v14[4].toNat) + pl (2 * x.v25[0].toNat) (x.v25[4].toNat))) * 24)
      = quadSqrLimb x 0 1 := by
  simp only [quadSqrLimb, sqLimb, sqCol, ph, pl, quadLimb, vlane,
    Fin.reduceCastAdd, Fin.reduceAddNat, Nat.mul_comm, Nat.mul_left_comm]
  ring_nf

private theorem lane_9 (x : Quad) :
    (((ph (x.v03[1].toNat) (x.v03[1].toNat)) + (pl (2 * x.v03[1].toNat) (x.v14[1].toNat))) + (((ph (x.v03[5].toNat) (x.v03[5].toNat) + ph (2 * x.v25[5].toNat) (x.v14[1].toNat) + ph (2 * x.v25[1].toNat) (x.v14[5].toNat)) + (pl (2 * x.v03[5].toNat) (x.v14[5].toNat) + pl (2 * x.v25[1].toNat) (x.v25[5].toNat))) * 128)) + (((ph (x.v03[5].toNat) (x.v03[5].toNat) + ph (2 * x.v25[5].toNat) (x.v14[1].toNat) + ph (2 * x.v25[1].toNat) (x.v14[5].toNat)) + (pl (2 * x.v03[5].toNat) (x.v14[5].toNat) + pl (2 * x.v25[1].toNat) (x.v25[5].toNat))) * 24)
      = quadSqrLimb x 1 1 := by
  simp only [quadSqrLimb, sqLimb, sqCol, ph, pl, quadLimb, vlane,
    Fin.reduceCastAdd, Fin.reduceAddNat, Nat.mul_comm, Nat.mul_left_comm]
  ring_nf

private theorem lane_10 (x : Quad) :
    (((ph (x.v03[2].toNat) (x.v03[2].toNat)) + (pl (2 * x.v03[2].toNat) (x.v14[2].toNat))) + (((ph (x.v03[6].toNat) (x.v03[6].toNat) + ph (2 * x.v25[6].toNat) (x.v14[2].toNat) + ph (2 * x.v25[2].toNat) (x.v14[6].toNat)) + (pl (2 * x.v03[6].toNat) (x.v14[6].toNat) + pl (2 * x.v25[2].toNat) (x.v25[6].toNat))) * 128)) + (((ph (x.v03[6].toNat) (x.v03[6].toNat) + ph (2 * x.v25[6].toNat) (x.v14[2].toNat) + ph (2 * x.v25[2].toNat) (x.v14[6].toNat)) + (pl (2 * x.v03[6].toNat) (x.v14[6].toNat) + pl (2 * x.v25[2].toNat) (x.v25[6].toNat))) * 24)
      = quadSqrLimb x 2 1 := by
  simp only [quadSqrLimb, sqLimb, sqCol, ph, pl, quadLimb, vlane,
    Fin.reduceCastAdd, Fin.reduceAddNat, Nat.mul_comm, Nat.mul_left_comm]
  ring_nf

private theorem lane_11 (x : Quad) :
    (((ph (x.v03[3].toNat) (x.v03[3].toNat)) + (pl (2 * x.v03[3].toNat) (x.v14[3].toNat))) + (((ph (x.v03[7].toNat) (x.v03[7].toNat) + ph (2 * x.v25[7].toNat) (x.v14[3].toNat) + ph (2 * x.v25[3].toNat) (x.v14[7].toNat)) + (pl (2 * x.v03[7].toNat) (x.v14[7].toNat) + pl (2 * x.v25[3].toNat) (x.v25[7].toNat))) * 128)) + (((ph (x.v03[7].toNat) (x.v03[7].toNat) + ph (2 * x.v25[7].toNat) (x.v14[3].toNat) + ph (2 * x.v25[3].toNat) (x.v14[7].toNat)) + (pl (2 * x.v03[7].toNat) (x.v14[7].toNat) + pl (2 * x.v25[3].toNat) (x.v25[7].toNat))) * 24)
      = quadSqrLimb x 3 1 := by
  simp only [quadSqrLimb, sqLimb, sqCol, ph, pl, quadLimb, vlane,
    Fin.reduceCastAdd, Fin.reduceAddNat, Nat.mul_comm, Nat.mul_left_comm]
  ring_nf

private theorem lane_12 (x : Quad) :
    (((ph (2 * x.v03[0].toNat) (x.v03[4].toNat) + ph (2 * x.v14[0].toNat) (x.v25[0].toNat)) + (pl (x.v25[0].toNat) (x.v25[0].toNat) + pl (2 * x.v03[0].toNat) (x.v14[4].toNat) + pl (2 * x.v14[0].toNat) (x.v03[4].toNat))) + (((ph (2 * x.v25[4].toNat) (x.v14[4].toNat)) + (pl (x.v25[4].toNat) (x.v25[4].toNat))) * 128)) + (((ph (2 * x.v25[4].toNat) (x.v14[4].toNat)) + (pl (x.v25[4].toNat) (x.v25[4].toNat))) * 24)
      = quadSqrLimb x 0 4 := by
  simp only [quadSqrLimb, sqLimb, sqCol, ph, pl, quadLimb, vlane,
    Fin.reduceCastAdd, Fin.reduceAddNat, Nat.mul_comm, Nat.mul_left_comm]
  ring_nf

private theorem lane_13 (x : Quad) :
    (((ph (2 * x.v03[1].toNat) (x.v03[5].toNat) + ph (2 * x.v14[1].toNat) (x.v25[1].toNat)) + (pl (x.v25[1].toNat) (x.v25[1].toNat) + pl (2 * x.v03[1].toNat) (x.v14[5].toNat) + pl (2 * x.v14[1].toNat) (x.v03[5].toNat))) + (((ph (2 * x.v25[5].toNat) (x.v14[5].toNat)) + (pl (x.v25[5].toNat) (x.v25[5].toNat))) * 128)) + (((ph (2 * x.v25[5].toNat) (x.v14[5].toNat)) + (pl (x.v25[5].toNat) (x.v25[5].toNat))) * 24)
      = quadSqrLimb x 1 4 := by
  simp only [quadSqrLimb, sqLimb, sqCol, ph, pl, quadLimb, vlane,
    Fin.reduceCastAdd, Fin.reduceAddNat, Nat.mul_comm, Nat.mul_left_comm]
  ring_nf

private theorem lane_14 (x : Quad) :
    (((ph (2 * x.v03[2].toNat) (x.v03[6].toNat) + ph (2 * x.v14[2].toNat) (x.v25[2].toNat)) + (pl (x.v25[2].toNat) (x.v25[2].toNat) + pl (2 * x.v03[2].toNat) (x.v14[6].toNat) + pl (2 * x.v14[2].toNat) (x.v03[6].toNat))) + (((ph (2 * x.v25[6].toNat) (x.v14[6].toNat)) + (pl (x.v25[6].toNat) (x.v25[6].toNat))) * 128)) + (((ph (2 * x.v25[6].toNat) (x.v14[6].toNat)) + (pl (x.v25[6].toNat) (x.v25[6].toNat))) * 24)
      = quadSqrLimb x 2 4 := by
  simp only [quadSqrLimb, sqLimb, sqCol, ph, pl, quadLimb, vlane,
    Fin.reduceCastAdd, Fin.reduceAddNat, Nat.mul_comm, Nat.mul_left_comm]
  ring_nf

private theorem lane_15 (x : Quad) :
    (((ph (2 * x.v03[3].toNat) (x.v03[7].toNat) + ph (2 * x.v14[3].toNat) (x.v25[3].toNat)) + (pl (x.v25[3].toNat) (x.v25[3].toNat) + pl (2 * x.v03[3].toNat) (x.v14[7].toNat) + pl (2 * x.v14[3].toNat) (x.v03[7].toNat))) + (((ph (2 * x.v25[7].toNat) (x.v14[7].toNat)) + (pl (x.v25[7].toNat) (x.v25[7].toNat))) * 128)) + (((ph (2 * x.v25[7].toNat) (x.v14[7].toNat)) + (pl (x.v25[7].toNat) (x.v25[7].toNat))) * 24)
      = quadSqrLimb x 3 4 := by
  simp only [quadSqrLimb, sqLimb, sqCol, ph, pl, quadLimb, vlane,
    Fin.reduceCastAdd, Fin.reduceAddNat, Nat.mul_comm, Nat.mul_left_comm]
  ring_nf

private theorem lane_16 (x : Quad) :
    ((((0) + (pl (x.v14[0].toNat) (x.v14[0].toNat) + pl (2 * x.v03[0].toNat) (x.v25[0].toNat))) + (((ph (2 * x.v03[4].toNat) (x.v14[4].toNat) + ph (2 * x.v25[0].toNat) (x.v25[4].toNat)) + (pl (x.v14[4].toNat) (x.v14[4].toNat) + pl (2 * x.v03[4].toNat) (x.v25[4].toNat))) * 128)) + (((ph (2 * x.v03[4].toNat) (x.v14[4].toNat) + ph (2 * x.v25[0].toNat) (x.v25[4].toNat)) + (pl (x.v14[4].toNat) (x.v14[4].toNat) + pl (2 * x.v03[4].toNat) (x.v25[4].toNat))) * 24)) + (ph (2 * x.v03[0].toNat) (x.v14[0].toNat))
      = quadSqrLimb x 0 2 := by
  simp only [quadSqrLimb, sqLimb, sqCol, ph, pl, quadLimb, vlane,
    Fin.reduceCastAdd, Fin.reduceAddNat, Nat.mul_comm, Nat.mul_left_comm]
  ring_nf

private theorem lane_17 (x : Quad) :
    ((((0) + (pl (x.v14[1].toNat) (x.v14[1].toNat) + pl (2 * x.v03[1].toNat) (x.v25[1].toNat))) + (((ph (2 * x.v03[5].toNat) (x.v14[5].toNat) + ph (2 * x.v25[1].toNat) (x.v25[5].toNat)) + (pl (x.v14[5].toNat) (x.v14[5].toNat) + pl (2 * x.v03[5].toNat) (x.v25[5].toNat))) * 128)) + (((ph (2 * x.v03[5].toNat) (x.v14[5].toNat) + ph (2 * x.v25[1].toNat) (x.v25[5].toNat)) + (pl (x.v14[5].toNat) (x.v14[5].toNat) + pl (2 * x.v03[5].toNat) (x.v25[5].toNat))) * 24)) + (ph (2 * x.v03[1].toNat) (x.v14[1].toNat))
      = quadSqrLimb x 1 2 := by
  simp only [quadSqrLimb, sqLimb, sqCol, ph, pl, quadLimb, vlane,
    Fin.reduceCastAdd, Fin.reduceAddNat, Nat.mul_comm, Nat.mul_left_comm]
  ring_nf

private theorem lane_18 (x : Quad) :
    ((((0) + (pl (x.v14[2].toNat) (x.v14[2].toNat) + pl (2 * x.v03[2].toNat) (x.v25[2].toNat))) + (((ph (2 * x.v03[6].toNat) (x.v14[6].toNat) + ph (2 * x.v25[2].toNat) (x.v25[6].toNat)) + (pl (x.v14[6].toNat) (x.v14[6].toNat) + pl (2 * x.v03[6].toNat) (x.v25[6].toNat))) * 128)) + (((ph (2 * x.v03[6].toNat) (x.v14[6].toNat) + ph (2 * x.v25[2].toNat) (x.v25[6].toNat)) + (pl (x.v14[6].toNat) (x.v14[6].toNat) + pl (2 * x.v03[6].toNat) (x.v25[6].toNat))) * 24)) + (ph (2 * x.v03[2].toNat) (x.v14[2].toNat))
      = quadSqrLimb x 2 2 := by
  simp only [quadSqrLimb, sqLimb, sqCol, ph, pl, quadLimb, vlane,
    Fin.reduceCastAdd, Fin.reduceAddNat, Nat.mul_comm, Nat.mul_left_comm]
  ring_nf

private theorem lane_19 (x : Quad) :
    ((((0) + (pl (x.v14[3].toNat) (x.v14[3].toNat) + pl (2 * x.v03[3].toNat) (x.v25[3].toNat))) + (((ph (2 * x.v03[7].toNat) (x.v14[7].toNat) + ph (2 * x.v25[3].toNat) (x.v25[7].toNat)) + (pl (x.v14[7].toNat) (x.v14[7].toNat) + pl (2 * x.v03[7].toNat) (x.v25[7].toNat))) * 128)) + (((ph (2 * x.v03[7].toNat) (x.v14[7].toNat) + ph (2 * x.v25[3].toNat) (x.v25[7].toNat)) + (pl (x.v14[7].toNat) (x.v14[7].toNat) + pl (2 * x.v03[7].toNat) (x.v25[7].toNat))) * 24)) + (ph (2 * x.v03[3].toNat) (x.v14[3].toNat))
      = quadSqrLimb x 3 2 := by
  simp only [quadSqrLimb, sqLimb, sqCol, ph, pl, quadLimb, vlane,
    Fin.reduceCastAdd, Fin.reduceAddNat, Nat.mul_comm, Nat.mul_left_comm]
  ring_nf

private theorem lane_20 (x : Quad) :
    ((((pl (2 * x.v03[4].toNat) (x.v25[0].toNat) + pl (2 * x.v14[4].toNat) 0) + (pl (2 * x.v03[0].toNat) (x.v25[4].toNat) + pl (2 * x.v14[0].toNat) (x.v14[4].toNat))) + (((ph (x.v25[4].toNat) (x.v25[4].toNat)) + (0)) * 128)) + (((ph (x.v25[4].toNat) (x.v25[4].toNat)) + (0)) * 24)) + (ph (x.v25[0].toNat) (x.v25[0].toNat) + ph (2 * x.v03[0].toNat) (x.v14[4].toNat) + ph (2 * x.v14[0].toNat) (x.v03[4].toNat))
      = quadSqrLimb x 0 5 := by
  simp only [quadSqrLimb, sqLimb, sqCol, ph, pl, quadLimb, vlane,
    Fin.reduceCastAdd, Fin.reduceAddNat, Nat.mul_comm, Nat.mul_left_comm, Nat.zero_mul]
  ring_nf

private theorem lane_21 (x : Quad) :
    ((((pl (2 * x.v03[5].toNat) (x.v25[1].toNat) + pl (2 * x.v14[5].toNat) 0) + (pl (2 * x.v03[1].toNat) (x.v25[5].toNat) + pl (2 * x.v14[1].toNat) (x.v14[5].toNat))) + (((ph (x.v25[5].toNat) (x.v25[5].toNat)) + (0)) * 128)) + (((ph (x.v25[5].toNat) (x.v25[5].toNat)) + (0)) * 24)) + (ph (x.v25[1].toNat) (x.v25[1].toNat) + ph (2 * x.v03[1].toNat) (x.v14[5].toNat) + ph (2 * x.v14[1].toNat) (x.v03[5].toNat))
      = quadSqrLimb x 1 5 := by
  simp only [quadSqrLimb, sqLimb, sqCol, ph, pl, quadLimb, vlane,
    Fin.reduceCastAdd, Fin.reduceAddNat, Nat.mul_comm, Nat.mul_left_comm, Nat.zero_mul]
  ring_nf

private theorem lane_22 (x : Quad) :
    ((((pl (2 * x.v03[6].toNat) (x.v25[2].toNat) + pl (2 * x.v14[6].toNat) 0) + (pl (2 * x.v03[2].toNat) (x.v25[6].toNat) + pl (2 * x.v14[2].toNat) (x.v14[6].toNat))) + (((ph (x.v25[6].toNat) (x.v25[6].toNat)) + (0)) * 128)) + (((ph (x.v25[6].toNat) (x.v25[6].toNat)) + (0)) * 24)) + (ph (x.v25[2].toNat) (x.v25[2].toNat) + ph (2 * x.v03[2].toNat) (x.v14[6].toNat) + ph (2 * x.v14[2].toNat) (x.v03[6].toNat))
      = quadSqrLimb x 2 5 := by
  simp only [quadSqrLimb, sqLimb, sqCol, ph, pl, quadLimb, vlane,
    Fin.reduceCastAdd, Fin.reduceAddNat, Nat.mul_comm, Nat.mul_left_comm, Nat.zero_mul]
  ring_nf

private theorem lane_23 (x : Quad) :
    ((((pl (2 * x.v03[7].toNat) (x.v25[3].toNat) + pl (2 * x.v14[7].toNat) 0) + (pl (2 * x.v03[3].toNat) (x.v25[7].toNat) + pl (2 * x.v14[3].toNat) (x.v14[7].toNat))) + (((ph (x.v25[7].toNat) (x.v25[7].toNat)) + (0)) * 128)) + (((ph (x.v25[7].toNat) (x.v25[7].toNat)) + (0)) * 24)) + (ph (x.v25[3].toNat) (x.v25[3].toNat) + ph (2 * x.v03[3].toNat) (x.v14[7].toNat) + ph (2 * x.v14[3].toNat) (x.v03[7].toNat))
      = quadSqrLimb x 3 5 := by
  simp only [quadSqrLimb, sqLimb, sqCol, ph, pl, quadLimb, vlane,
    Fin.reduceCastAdd, Fin.reduceAddNat, Nat.mul_comm, Nat.mul_left_comm, Nat.zero_mul]
  ring_nf

/-! ## The derivation

The bound facts `quad_vpmadd52` needs, for the plain and the doubled operands
alike -- a `vpmadd52h` lane is `phRaw u v` only when both operands are already
below `2^52`, and `u47` inputs are, doubled or not. -/

local macro "quad_shuffle " h:term " with " ns:Lean.Parser.Tactic.simpLemma,* : tactic =>
  `(tactic| denote_shuffle $h with quadValMem, quadLimb, vlane, $ns,*)

local macro "quad_madd52 " h:term " with " ns:Lean.Parser.Tactic.simpLemma,* : tactic =>
  `(tactic| quad_vpmadd52 $h with quadValMem,
      $(Lean.mkIdent `bx03):term, $(Lean.mkIdent `bx14):term, $(Lean.mkIdent `bx25):term,
      $(Lean.mkIdent `b2x03):term, $(Lean.mkIdent `b2x14):term, $(Lean.mkIdent `b2x25):term, $ns,*)


set_option maxHeartbeats 40000000 in
set_option maxRecDepth 100000 in
/-- **Limb derivation**: on unreduced inputs the region denotes to exactly
three whole-vector stores, of the three vectors the specification predicts,
through the three pointer parameters in declaration order. All 115
instructions are carried through at the N level. -/
theorem denote_fd_r43x6_quad_sqr_fast (x : Quad)
    (hx03 : R43x6.U47 x.v03) (hx14 : R43x6.U47 x.v14) (hx25 : R43x6.U47 x.v25)
    (p₀ p₁ p₂ : SLLVM.Ptr) :
    fd_r43x6_quad_sqr_fast.denote (quadValMem p₀ p₁ p₂ x) =
      (do storeVec p₀ ((quadSqrResult x).v03.map PoisonOr.value)
          storeVec p₁ ((quadSqrResult x).v14.map PoisonOr.value)
          storeVec p₂ ((quadSqrResult x).v25.map PoisonOr.value)
          pure (HVector.nil :
            HVector TyDenote.toType ([] : List SLLVM.Ty))) := by
  have bx03 : ∀ (i : ℕ) (h : i < 8),
      (x.v03[i]'h).toNat % 4503599627370496 = (x.v03[i]'h).toNat := fun i h =>
    Nat.mod_eq_of_lt (by
      have : (x.v03[i]'h).toNat < 2 ^ 47 := unn_toNat x.v03 47 (by omega) hx03 ⟨i, h⟩; omega)
  have b2x03 : ∀ (i : ℕ) (h : i < 8),
      2 * (x.v03[i]'h).toNat % 4503599627370496 = 2 * (x.v03[i]'h).toNat := fun i h =>
    Nat.mod_eq_of_lt (by
      have : (x.v03[i]'h).toNat < 2 ^ 47 := unn_toNat x.v03 47 (by omega) hx03 ⟨i, h⟩; omega)
  have bx14 : ∀ (i : ℕ) (h : i < 8),
      (x.v14[i]'h).toNat % 4503599627370496 = (x.v14[i]'h).toNat := fun i h =>
    Nat.mod_eq_of_lt (by
      have : (x.v14[i]'h).toNat < 2 ^ 47 := unn_toNat x.v14 47 (by omega) hx14 ⟨i, h⟩; omega)
  have b2x14 : ∀ (i : ℕ) (h : i < 8),
      2 * (x.v14[i]'h).toNat % 4503599627370496 = 2 * (x.v14[i]'h).toNat := fun i h =>
    Nat.mod_eq_of_lt (by
      have : (x.v14[i]'h).toNat < 2 ^ 47 := unn_toNat x.v14 47 (by omega) hx14 ⟨i, h⟩; omega)
  have bx25 : ∀ (i : ℕ) (h : i < 8),
      (x.v25[i]'h).toNat % 4503599627370496 = (x.v25[i]'h).toNat := fun i h =>
    Nat.mod_eq_of_lt (by
      have : (x.v25[i]'h).toNat < 2 ^ 47 := unn_toNat x.v25 47 (by omega) hx25 ⟨i, h⟩; omega)
  have b2x25 : ∀ (i : ℕ) (h : i < 8),
      2 * (x.v25[i]'h).toNat % 4503599627370496 = 2 * (x.v25[i]'h).toNat := fun i h =>
    Nat.mod_eq_of_lt (by
      have : (x.v25[i]'h).toNat < 2 ^ 47 := unn_toNat x.v25 47 (by omega) hx25 ⟨i, h⟩; omega)
  unfold fd_r43x6_quad_sqr_fast
  let X : Fin 4 → Fin 6 → ℕ := quadLimb x.v03 x.v14 x.v25

  -- the constants, including the two `insertelement` chains that build a
  -- half-zero half-poison mask; the poison half is never selected
  denote_step_all v 41
  let zeroBVP : PoisonOr (BitVec 64) := .value 0
  have hz64 : v2 = zeroBVP := by
    simp only [hv2, Expr.denoteOp1, Expr.denoteOpPure]; simp_peephole
    simp only [HVector.head]; rfl
  have hpoison : v1 = PoisonOr.poison := by
    simp only [hv1]; simp_peephole; rfl
  subst hz64 hpoison
  let zero4_p4 : Vector (PoisonOr (BitVec 64)) 8 :=
    (Vector.replicate 4 (.value (BitVec.zero 64))).append (Vector.replicate 4 .poison)
  let p4_zero4 : Vector (PoisonOr (BitVec 64)) 8 :=
    (Vector.replicate 4 .poison).append (Vector.replicate 4 (.value (BitVec.zero 64)))
  have hzlo : v19 = zero4_p4 := by
    denote_eval v 3 19
    denote_expand v 3 19
    simp [LLVM.Ty.insertelement, LLVM.Ty.poison, LLVM.const?]
    rfl
  have hzhi : v39 = p4_zero4 := by
    denote_eval v 23 39
    denote_expand v 23 39
    simp [LLVM.Ty.insertelement, LLVM.Ty.poison, LLVM.const?]
    rfl
  subst hzlo hzhi
  denote_clear v 3 18
  denote_clear v 23 38
  let oneVec := toBitVecValue 64 (Vector.replicate 8 1)
  let zeroVec := toBitVecValue 64 (Vector.replicate 8 0)
  let nineVec := toBitVecValue 64 (Vector.replicate 8 9)
  let sevenVec := toBitVecValue 64 (Vector.replicate 8 7)
  let tf4Vec := toBitVecValue 64 (Vector.replicate 8 24)
  have h1 : v20 = oneVec := by denote_dense hv20
  have hzz : v21 = zeroVec := by denote_dense hv21
  have h9 : v22 = nineVec := by denote_dense hv22
  have h7 : v40 = sevenVec := by denote_dense hv40
  have h24 : v41 = tf4Vec := by denote_dense hv41
  subst h1 hzz h9 h7 h24

  -- x05 .. x4z and the doubled operands
  denote_step_all v 42
  -- x05: `wwl_pack_h0_h1( x03, x25 )`: limb 0 in the low half, limb 5 in the high
  let x05 := toBitVecValue 64 #v[(X 0 0), (X 1 0), (X 2 0), (X 3 0), (X 0 5), (X 1 5), (X 2 5), (X 3 5)]
  have hx05 : v42 = x05 := by quad_shuffle hv42 with x05
  subst hx05
  denote_clear v 42 42
  denote_step_all v 43
  -- x12: limbs 1 and 2
  let x12 := toBitVecValue 64 #v[(X 0 1), (X 1 1), (X 2 1), (X 3 1), (X 0 2), (X 1 2), (X 2 2), (X 3 2)]
  have hx12 : v43 = x12 := by quad_shuffle hv43 with x12
  subst hx12
  denote_clear v 43 43
  denote_step_all v 44
  -- x34: limbs 3 and 4
  let x34 := toBitVecValue 64 #v[(X 0 3), (X 1 3), (X 2 3), (X 3 3), (X 0 4), (X 1 4), (X 2 4), (X 3 4)]
  have hx34 : v44 = x34 := by quad_shuffle hv44 with x34
  subst hx34
  denote_clear v 44 44
  denote_step_all v 45
  -- x41: limbs 4 and 1
  let x41 := toBitVecValue 64 #v[(X 0 4), (X 1 4), (X 2 4), (X 3 4), (X 0 1), (X 1 1), (X 2 1), (X 3 1)]
  have hx41 : v45 = x41 := by quad_shuffle hv45 with x41
  subst hx41
  denote_clear v 45 45
  denote_step_all v 46
  -- x23: limbs 2 and 3
  let x23 := toBitVecValue 64 #v[(X 0 2), (X 1 2), (X 2 2), (X 3 2), (X 0 3), (X 1 3), (X 2 3), (X 3 3)]
  have hx23 : v46 = x23 := by quad_shuffle hv46 with x23
  subst hx23
  denote_clear v 46 46
  denote_step_all v 47
  -- x52: limbs 5 and 2
  let x52 := toBitVecValue 64 #v[(X 0 5), (X 1 5), (X 2 5), (X 3 5), (X 0 2), (X 1 2), (X 2 2), (X 3 2)]
  have hx52 : v47 = x52 := by quad_shuffle hv47 with x52
  subst hx52
  denote_clear v 47 47
  denote_step_all v 48
  -- x4z: limb 4 and a zero -- the kernel's own constant, so that the mirrored schedule has a partner for `2*p41l`
  let x4z := toBitVecValue 64 #v[(X 0 4), (X 1 4), (X 2 4), (X 3 4), 0, 0, 0, 0]
  have hx4z : v48 = x4z := by quad_shuffle hv48 with x4z
  subst hx4z
  denote_clear v 48 48
  denote_step_all v 49
  let two_x03 := toBitVecValue 64 #v[2 * (X 0 0), 2 * (X 1 0), 2 * (X 2 0), 2 * (X 3 0), 2 * (X 0 3), 2 * (X 1 3), 2 * (X 2 3), 2 * (X 3 3)]
  have htwo_x03 : v49 = two_x03 := by quad_vecbin_ring hv49 with quadValMem, shl_lane, two_x03
  subst htwo_x03
  denote_clear v 49 49
  denote_step_all v 50
  let two_x14 := toBitVecValue 64 #v[2 * (X 0 1), 2 * (X 1 1), 2 * (X 2 1), 2 * (X 3 1), 2 * (X 0 4), 2 * (X 1 4), 2 * (X 2 4), 2 * (X 3 4)]
  have htwo_x14 : v50 = two_x14 := by quad_vecbin_ring hv50 with quadValMem, shl_lane, two_x14
  subst htwo_x14
  denote_clear v 50 50
  denote_step_all v 51
  let two_x05 := toBitVecValue 64 #v[2 * (X 0 0), 2 * (X 1 0), 2 * (X 2 0), 2 * (X 3 0), 2 * (X 0 5), 2 * (X 1 5), 2 * (X 2 5), 2 * (X 3 5)]
  have htwo_x05 : v51 = two_x05 := by quad_vecbin_ring hv51 with quadValMem, two_x05, x05
  subst htwo_x05
  denote_clear v 51 51
  denote_step_all v 52
  let two_x12 := toBitVecValue 64 #v[2 * (X 0 1), 2 * (X 1 1), 2 * (X 2 1), 2 * (X 3 1), 2 * (X 0 2), 2 * (X 1 2), 2 * (X 2 2), 2 * (X 3 2)]
  have htwo_x12 : v52 = two_x12 := by quad_vecbin_ring hv52 with quadValMem, two_x12, x12
  subst htwo_x12
  denote_clear v 52 52

  -- p0a .. p55 and q1b .. q66: the 21 products per element
  denote_step_all v 53
  -- p0a: columns 0 and 10
  let p0a := toBitVecValue 64 #v[pl (X 0 0) (X 0 0), pl (X 1 0) (X 1 0), pl (X 2 0) (X 2 0), pl (X 3 0) (X 3 0), pl (X 0 5) (X 0 5), pl (X 1 5) (X 1 5), pl (X 2 5) (X 2 5), pl (X 3 5) (X 3 5)]
  have hp0a : v53 = p0a := by quad_madd52 hv53 with p0a, x05
  subst hp0a
  denote_clear v 53 53
  denote_step_all v 54
  -- p19: columns 1 and 9
  let p19 := toBitVecValue 64 #v[pl (2 * X 0 0) (X 0 1), pl (2 * X 1 0) (X 1 1), pl (2 * X 2 0) (X 2 1), pl (2 * X 3 0) (X 3 1), pl (2 * X 0 5) (X 0 4), pl (2 * X 1 5) (X 1 4), pl (2 * X 2 5) (X 2 4), pl (2 * X 3 5) (X 3 4)]
  have hp19 : v54 = p19 := by quad_madd52 hv54 with p19, two_x05
  subst hp19
  denote_clear v 54 54
  denote_step_all v 55
  let p28_lo1 := toBitVecValue 64 #v[pl (X 0 1) (X 0 1), pl (X 1 1) (X 1 1), pl (X 2 1) (X 2 1), pl (X 3 1) (X 3 1), pl (X 0 4) (X 0 4), pl (X 1 4) (X 1 4), pl (X 2 4) (X 2 4), pl (X 3 4) (X 3 4)]
  have hp28_lo1 : v55 = p28_lo1 := by quad_madd52 hv55 with p28_lo1
  subst hp28_lo1
  denote_clear v 55 55
  denote_step_all v 56
  -- p28: columns 2 and 8
  let p28 := toBitVecValue 64 #v[pl (X 0 1) (X 0 1) + pl (2 * X 0 0) (X 0 2), pl (X 1 1) (X 1 1) + pl (2 * X 1 0) (X 1 2), pl (X 2 1) (X 2 1) + pl (2 * X 2 0) (X 2 2), pl (X 3 1) (X 3 1) + pl (2 * X 3 0) (X 3 2), pl (X 0 4) (X 0 4) + pl (2 * X 0 3) (X 0 5), pl (X 1 4) (X 1 4) + pl (2 * X 1 3) (X 1 5), pl (X 2 4) (X 2 4) + pl (2 * X 2 3) (X 2 5), pl (X 3 4) (X 3 4) + pl (2 * X 3 3) (X 3 5)]
  have hp28 : v56 = p28 := by quad_madd52 hv56 with p28, p28_lo1, two_x03
  subst hp28
  denote_clear v 56 56
  denote_step_all v 57
  let p37_lo1 := toBitVecValue 64 #v[pl (2 * X 0 0) (X 0 3), pl (2 * X 1 0) (X 1 3), pl (2 * X 2 0) (X 2 3), pl (2 * X 3 0) (X 3 3), pl (2 * X 0 3) (X 0 4), pl (2 * X 1 3) (X 1 4), pl (2 * X 2 3) (X 2 4), pl (2 * X 3 3) (X 3 4)]
  have hp37_lo1 : v57 = p37_lo1 := by quad_madd52 hv57 with p37_lo1, two_x03, x34
  subst hp37_lo1
  denote_clear v 57 57
  denote_step_all v 58
  -- p37: columns 3 and 7
  let p37 := toBitVecValue 64 #v[pl (2 * X 0 0) (X 0 3) + pl (2 * X 0 1) (X 0 2), pl (2 * X 1 0) (X 1 3) + pl (2 * X 1 1) (X 1 2), pl (2 * X 2 0) (X 2 3) + pl (2 * X 2 1) (X 2 2), pl (2 * X 3 0) (X 3 3) + pl (2 * X 3 1) (X 3 2), pl (2 * X 0 3) (X 0 4) + pl (2 * X 0 2) (X 0 5), pl (2 * X 1 3) (X 1 4) + pl (2 * X 1 2) (X 1 5), pl (2 * X 2 3) (X 2 4) + pl (2 * X 2 2) (X 2 5), pl (2 * X 3 3) (X 3 4) + pl (2 * X 3 2) (X 3 5)]
  have hp37 : v58 = p37 := by quad_madd52 hv58 with p37, p37_lo1, two_x12
  subst hp37
  denote_clear v 58 58
  denote_step_all v 59
  let p46_lo1 := toBitVecValue 64 #v[pl (X 0 2) (X 0 2), pl (X 1 2) (X 1 2), pl (X 2 2) (X 2 2), pl (X 3 2) (X 3 2), pl (X 0 3) (X 0 3), pl (X 1 3) (X 1 3), pl (X 2 3) (X 2 3), pl (X 3 3) (X 3 3)]
  have hp46_lo1 : v59 = p46_lo1 := by quad_madd52 hv59 with p46_lo1, x23
  subst hp46_lo1
  denote_clear v 59 59
  denote_step_all v 60
  let p46_lo2 := toBitVecValue 64 #v[pl (X 0 2) (X 0 2) + pl (2 * X 0 0) (X 0 4), pl (X 1 2) (X 1 2) + pl (2 * X 1 0) (X 1 4), pl (X 2 2) (X 2 2) + pl (2 * X 2 0) (X 2 4), pl (X 3 2) (X 3 2) + pl (2 * X 3 0) (X 3 4), pl (X 0 3) (X 0 3) + pl (2 * X 0 5) (X 0 1), pl (X 1 3) (X 1 3) + pl (2 * X 1 5) (X 1 1), pl (X 2 3) (X 2 3) + pl (2 * X 2 5) (X 2 1), pl (X 3 3) (X 3 3) + pl (2 * X 3 5) (X 3 1)]
  have hp46_lo2 : v60 = p46_lo2 := by quad_madd52 hv60 with p46_lo1, p46_lo2, two_x05, x41
  subst hp46_lo2
  denote_clear v 60 60
  denote_step_all v 61
  -- p46: columns 4 and 6
  let p46 := toBitVecValue 64 #v[pl (X 0 2) (X 0 2) + pl (2 * X 0 0) (X 0 4) + pl (2 * X 0 1) (X 0 3), pl (X 1 2) (X 1 2) + pl (2 * X 1 0) (X 1 4) + pl (2 * X 1 1) (X 1 3), pl (X 2 2) (X 2 2) + pl (2 * X 2 0) (X 2 4) + pl (2 * X 2 1) (X 2 3), pl (X 3 2) (X 3 2) + pl (2 * X 3 0) (X 3 4) + pl (2 * X 3 1) (X 3 3), pl (X 0 3) (X 0 3) + pl (2 * X 0 5) (X 0 1) + pl (2 * X 0 2) (X 0 4), pl (X 1 3) (X 1 3) + pl (2 * X 1 5) (X 1 1) + pl (2 * X 1 2) (X 1 4), pl (X 2 3) (X 2 3) + pl (2 * X 2 5) (X 2 1) + pl (2 * X 2 2) (X 2 4), pl (X 3 3) (X 3 3) + pl (2 * X 3 5) (X 3 1) + pl (2 * X 3 2) (X 3 4)]
  have hp46 : v61 = p46 := by quad_madd52 hv61 with p46, p46_lo2, two_x12, x34
  subst hp46
  denote_clear v 61 61
  denote_step_all v 62
  let p55_lo1 := toBitVecValue 64 #v[pl (2 * X 0 0) (X 0 5), pl (2 * X 1 0) (X 1 5), pl (2 * X 2 0) (X 2 5), pl (2 * X 3 0) (X 3 5), pl (2 * X 0 3) (X 0 2), pl (2 * X 1 3) (X 1 2), pl (2 * X 2 3) (X 2 2), pl (2 * X 3 3) (X 3 2)]
  have hp55_lo1 : v62 = p55_lo1 := by quad_madd52 hv62 with p55_lo1, two_x03, x52
  subst hp55_lo1
  denote_clear v 62 62
  denote_step_all v 63
  -- p55: column 5, split across *both* halves; they are re-joined below
  let p55 := toBitVecValue 64 #v[pl (2 * X 0 0) (X 0 5) + pl (2 * X 0 1) (X 0 4), pl (2 * X 1 0) (X 1 5) + pl (2 * X 1 1) (X 1 4), pl (2 * X 2 0) (X 2 5) + pl (2 * X 2 1) (X 2 4), pl (2 * X 3 0) (X 3 5) + pl (2 * X 3 1) (X 3 4), pl (2 * X 0 3) (X 0 2) + pl (2 * X 0 4) 0, pl (2 * X 1 3) (X 1 2) + pl (2 * X 1 4) 0, pl (2 * X 2 3) (X 2 2) + pl (2 * X 2 4) 0, pl (2 * X 3 3) (X 3 2) + pl (2 * X 3 4) 0]
  have hp55 : v63 = p55 := by quad_madd52 hv63 with p55, p55_lo1, two_x14, x4z
  subst hp55
  denote_clear v 63 63
  denote_step_all v 64
  let q1b_raw := toBitVecValue 64 #v[phRaw (X 0 0) (X 0 0), phRaw (X 1 0) (X 1 0), phRaw (X 2 0) (X 2 0), phRaw (X 3 0) (X 3 0), phRaw (X 0 5) (X 0 5), phRaw (X 1 5) (X 1 5), phRaw (X 2 5) (X 2 5), phRaw (X 3 5) (X 3 5)]
  have hq1b_raw : v64 = q1b_raw := by quad_madd52 hv64 with q1b_raw, x05
  subst hq1b_raw
  denote_clear v 64 64
  denote_step_all v 65
  -- q1b: columns 1 and 11
  let q1b := toBitVecValue 64 #v[ph (X 0 0) (X 0 0), ph (X 1 0) (X 1 0), ph (X 2 0) (X 2 0), ph (X 3 0) (X 3 0), ph (X 0 5) (X 0 5), ph (X 1 5) (X 1 5), ph (X 2 5) (X 2 5), ph (X 3 5) (X 3 5)]
  have hq1b : v65 = q1b := by quad_vecbin_ring hv65 with quadValMem, q1b, q1b_raw
  subst hq1b
  denote_clear v 65 65
  denote_step_all v 66
  let q2a_raw := toBitVecValue 64 #v[phRaw (2 * X 0 0) (X 0 1), phRaw (2 * X 1 0) (X 1 1), phRaw (2 * X 2 0) (X 2 1), phRaw (2 * X 3 0) (X 3 1), phRaw (2 * X 0 5) (X 0 4), phRaw (2 * X 1 5) (X 1 4), phRaw (2 * X 2 5) (X 2 4), phRaw (2 * X 3 5) (X 3 4)]
  have hq2a_raw : v66 = q2a_raw := by quad_madd52 hv66 with q2a_raw, two_x05
  subst hq2a_raw
  denote_clear v 66 66
  denote_step_all v 67
  -- q2a: columns 2 and 10
  let q2a := toBitVecValue 64 #v[ph (2 * X 0 0) (X 0 1), ph (2 * X 1 0) (X 1 1), ph (2 * X 2 0) (X 2 1), ph (2 * X 3 0) (X 3 1), ph (2 * X 0 5) (X 0 4), ph (2 * X 1 5) (X 1 4), ph (2 * X 2 5) (X 2 4), ph (2 * X 3 5) (X 3 4)]
  have hq2a : v67 = q2a := by quad_vecbin_ring hv67 with quadValMem, q2a, q2a_raw
  subst hq2a
  denote_clear v 67 67
  denote_step_all v 68
  let q39_raw1 := toBitVecValue 64 #v[phRaw (X 0 1) (X 0 1), phRaw (X 1 1) (X 1 1), phRaw (X 2 1) (X 2 1), phRaw (X 3 1) (X 3 1), phRaw (X 0 4) (X 0 4), phRaw (X 1 4) (X 1 4), phRaw (X 2 4) (X 2 4), phRaw (X 3 4) (X 3 4)]
  have hq39_raw1 : v68 = q39_raw1 := by quad_madd52 hv68 with q39_raw1
  subst hq39_raw1
  denote_clear v 68 68
  denote_step_all v 69
  let q39_raw := toBitVecValue 64 #v[phRaw (X 0 1) (X 0 1) + phRaw (2 * X 0 0) (X 0 2), phRaw (X 1 1) (X 1 1) + phRaw (2 * X 1 0) (X 1 2), phRaw (X 2 1) (X 2 1) + phRaw (2 * X 2 0) (X 2 2), phRaw (X 3 1) (X 3 1) + phRaw (2 * X 3 0) (X 3 2), phRaw (X 0 4) (X 0 4) + phRaw (2 * X 0 3) (X 0 5), phRaw (X 1 4) (X 1 4) + phRaw (2 * X 1 3) (X 1 5), phRaw (X 2 4) (X 2 4) + phRaw (2 * X 2 3) (X 2 5), phRaw (X 3 4) (X 3 4) + phRaw (2 * X 3 3) (X 3 5)]
  have hq39_raw : v69 = q39_raw := by quad_madd52 hv69 with q39_raw, q39_raw1, two_x03
  subst hq39_raw
  denote_clear v 69 69
  denote_step_all v 70
  -- q39: columns 3 and 9
  let q39 := toBitVecValue 64 #v[ph (X 0 1) (X 0 1) + ph (2 * X 0 0) (X 0 2), ph (X 1 1) (X 1 1) + ph (2 * X 1 0) (X 1 2), ph (X 2 1) (X 2 1) + ph (2 * X 2 0) (X 2 2), ph (X 3 1) (X 3 1) + ph (2 * X 3 0) (X 3 2), ph (X 0 4) (X 0 4) + ph (2 * X 0 3) (X 0 5), ph (X 1 4) (X 1 4) + ph (2 * X 1 3) (X 1 5), ph (X 2 4) (X 2 4) + ph (2 * X 2 3) (X 2 5), ph (X 3 4) (X 3 4) + ph (2 * X 3 3) (X 3 5)]
  have hq39 : v70 = q39 := by quad_vecbin_ring hv70 with quadValMem, q39, q39_raw
  subst hq39
  denote_clear v 70 70
  denote_step_all v 71
  let q48_raw1 := toBitVecValue 64 #v[phRaw (2 * X 0 0) (X 0 3), phRaw (2 * X 1 0) (X 1 3), phRaw (2 * X 2 0) (X 2 3), phRaw (2 * X 3 0) (X 3 3), phRaw (2 * X 0 3) (X 0 4), phRaw (2 * X 1 3) (X 1 4), phRaw (2 * X 2 3) (X 2 4), phRaw (2 * X 3 3) (X 3 4)]
  have hq48_raw1 : v71 = q48_raw1 := by quad_madd52 hv71 with q48_raw1, two_x03, x34
  subst hq48_raw1
  denote_clear v 71 71
  denote_step_all v 72
  let q48_raw := toBitVecValue 64 #v[phRaw (2 * X 0 0) (X 0 3) + phRaw (2 * X 0 1) (X 0 2), phRaw (2 * X 1 0) (X 1 3) + phRaw (2 * X 1 1) (X 1 2), phRaw (2 * X 2 0) (X 2 3) + phRaw (2 * X 2 1) (X 2 2), phRaw (2 * X 3 0) (X 3 3) + phRaw (2 * X 3 1) (X 3 2), phRaw (2 * X 0 3) (X 0 4) + phRaw (2 * X 0 2) (X 0 5), phRaw (2 * X 1 3) (X 1 4) + phRaw (2 * X 1 2) (X 1 5), phRaw (2 * X 2 3) (X 2 4) + phRaw (2 * X 2 2) (X 2 5), phRaw (2 * X 3 3) (X 3 4) + phRaw (2 * X 3 2) (X 3 5)]
  have hq48_raw : v72 = q48_raw := by quad_madd52 hv72 with q48_raw, q48_raw1, two_x12
  subst hq48_raw
  denote_clear v 72 72
  denote_step_all v 73
  -- q48: columns 4 and 8
  let q48 := toBitVecValue 64 #v[ph (2 * X 0 0) (X 0 3) + ph (2 * X 0 1) (X 0 2), ph (2 * X 1 0) (X 1 3) + ph (2 * X 1 1) (X 1 2), ph (2 * X 2 0) (X 2 3) + ph (2 * X 2 1) (X 2 2), ph (2 * X 3 0) (X 3 3) + ph (2 * X 3 1) (X 3 2), ph (2 * X 0 3) (X 0 4) + ph (2 * X 0 2) (X 0 5), ph (2 * X 1 3) (X 1 4) + ph (2 * X 1 2) (X 1 5), ph (2 * X 2 3) (X 2 4) + ph (2 * X 2 2) (X 2 5), ph (2 * X 3 3) (X 3 4) + ph (2 * X 3 2) (X 3 5)]
  have hq48 : v73 = q48 := by quad_vecbin_ring hv73 with quadValMem, q48, q48_raw
  subst hq48
  denote_clear v 73 73
  denote_step_all v 74
  let q57_raw1 := toBitVecValue 64 #v[phRaw (X 0 2) (X 0 2), phRaw (X 1 2) (X 1 2), phRaw (X 2 2) (X 2 2), phRaw (X 3 2) (X 3 2), phRaw (X 0 3) (X 0 3), phRaw (X 1 3) (X 1 3), phRaw (X 2 3) (X 2 3), phRaw (X 3 3) (X 3 3)]
  have hq57_raw1 : v74 = q57_raw1 := by quad_madd52 hv74 with q57_raw1, x23
  subst hq57_raw1
  denote_clear v 74 74
  denote_step_all v 75
  let q57_raw2 := toBitVecValue 64 #v[phRaw (X 0 2) (X 0 2) + phRaw (2 * X 0 0) (X 0 4), phRaw (X 1 2) (X 1 2) + phRaw (2 * X 1 0) (X 1 4), phRaw (X 2 2) (X 2 2) + phRaw (2 * X 2 0) (X 2 4), phRaw (X 3 2) (X 3 2) + phRaw (2 * X 3 0) (X 3 4), phRaw (X 0 3) (X 0 3) + phRaw (2 * X 0 5) (X 0 1), phRaw (X 1 3) (X 1 3) + phRaw (2 * X 1 5) (X 1 1), phRaw (X 2 3) (X 2 3) + phRaw (2 * X 2 5) (X 2 1), phRaw (X 3 3) (X 3 3) + phRaw (2 * X 3 5) (X 3 1)]
  have hq57_raw2 : v75 = q57_raw2 := by quad_madd52 hv75 with q57_raw1, q57_raw2, two_x05, x41
  subst hq57_raw2
  denote_clear v 75 75
  denote_step_all v 76
  let q57_raw := toBitVecValue 64 #v[phRaw (X 0 2) (X 0 2) + phRaw (2 * X 0 0) (X 0 4) + phRaw (2 * X 0 1) (X 0 3), phRaw (X 1 2) (X 1 2) + phRaw (2 * X 1 0) (X 1 4) + phRaw (2 * X 1 1) (X 1 3), phRaw (X 2 2) (X 2 2) + phRaw (2 * X 2 0) (X 2 4) + phRaw (2 * X 2 1) (X 2 3), phRaw (X 3 2) (X 3 2) + phRaw (2 * X 3 0) (X 3 4) + phRaw (2 * X 3 1) (X 3 3), phRaw (X 0 3) (X 0 3) + phRaw (2 * X 0 5) (X 0 1) + phRaw (2 * X 0 2) (X 0 4), phRaw (X 1 3) (X 1 3) + phRaw (2 * X 1 5) (X 1 1) + phRaw (2 * X 1 2) (X 1 4), phRaw (X 2 3) (X 2 3) + phRaw (2 * X 2 5) (X 2 1) + phRaw (2 * X 2 2) (X 2 4), phRaw (X 3 3) (X 3 3) + phRaw (2 * X 3 5) (X 3 1) + phRaw (2 * X 3 2) (X 3 4)]
  have hq57_raw : v76 = q57_raw := by quad_madd52 hv76 with q57_raw, q57_raw2, two_x12, x34
  subst hq57_raw
  denote_clear v 76 76
  denote_step_all v 77
  -- q57: columns 5 and 7
  let q57 := toBitVecValue 64 #v[ph (X 0 2) (X 0 2) + ph (2 * X 0 0) (X 0 4) + ph (2 * X 0 1) (X 0 3), ph (X 1 2) (X 1 2) + ph (2 * X 1 0) (X 1 4) + ph (2 * X 1 1) (X 1 3), ph (X 2 2) (X 2 2) + ph (2 * X 2 0) (X 2 4) + ph (2 * X 2 1) (X 2 3), ph (X 3 2) (X 3 2) + ph (2 * X 3 0) (X 3 4) + ph (2 * X 3 1) (X 3 3), ph (X 0 3) (X 0 3) + ph (2 * X 0 5) (X 0 1) + ph (2 * X 0 2) (X 0 4), ph (X 1 3) (X 1 3) + ph (2 * X 1 5) (X 1 1) + ph (2 * X 1 2) (X 1 4), ph (X 2 3) (X 2 3) + ph (2 * X 2 5) (X 2 1) + ph (2 * X 2 2) (X 2 4), ph (X 3 3) (X 3 3) + ph (2 * X 3 5) (X 3 1) + ph (2 * X 3 2) (X 3 4)]
  have hq57 : v77 = q57 := by quad_vecbin_ring hv77 with quadValMem, q57, q57_raw
  subst hq57
  denote_clear v 77 77
  denote_step_all v 78
  let q66_raw1 := toBitVecValue 64 #v[phRaw (2 * X 0 0) (X 0 5), phRaw (2 * X 1 0) (X 1 5), phRaw (2 * X 2 0) (X 2 5), phRaw (2 * X 3 0) (X 3 5), phRaw (2 * X 0 3) (X 0 2), phRaw (2 * X 1 3) (X 1 2), phRaw (2 * X 2 3) (X 2 2), phRaw (2 * X 3 3) (X 3 2)]
  have hq66_raw1 : v78 = q66_raw1 := by quad_madd52 hv78 with q66_raw1, two_x03, x52
  subst hq66_raw1
  denote_clear v 78 78
  denote_step_all v 79
  let q66_raw := toBitVecValue 64 #v[phRaw (2 * X 0 0) (X 0 5) + phRaw (2 * X 0 1) (X 0 4), phRaw (2 * X 1 0) (X 1 5) + phRaw (2 * X 1 1) (X 1 4), phRaw (2 * X 2 0) (X 2 5) + phRaw (2 * X 2 1) (X 2 4), phRaw (2 * X 3 0) (X 3 5) + phRaw (2 * X 3 1) (X 3 4), phRaw (2 * X 0 3) (X 0 2) + phRaw (2 * X 0 4) 0, phRaw (2 * X 1 3) (X 1 2) + phRaw (2 * X 1 4) 0, phRaw (2 * X 2 3) (X 2 2) + phRaw (2 * X 2 4) 0, phRaw (2 * X 3 3) (X 3 2) + phRaw (2 * X 3 4) 0]
  have hq66_raw : v79 = q66_raw := by quad_madd52 hv79 with q66_raw, q66_raw1, two_x14, x4z
  subst hq66_raw
  denote_clear v 79 79
  denote_step_all v 80
  -- q66: column 6, likewise split across both halves
  let q66 := toBitVecValue 64 #v[ph (2 * X 0 0) (X 0 5) + ph (2 * X 0 1) (X 0 4), ph (2 * X 1 0) (X 1 5) + ph (2 * X 1 1) (X 1 4), ph (2 * X 2 0) (X 2 5) + ph (2 * X 2 1) (X 2 4), ph (2 * X 3 0) (X 3 5) + ph (2 * X 3 1) (X 3 4), ph (2 * X 0 3) (X 0 2) + ph (2 * X 0 4) 0, ph (2 * X 1 3) (X 1 2) + ph (2 * X 1 4) 0, ph (2 * X 2 3) (X 2 2) + ph (2 * X 2 4) 0, ph (2 * X 3 3) (X 3 2) + ph (2 * X 3 4) 0]
  have hq66 : v80 = q66 := by quad_vecbin_ring hv80 with quadValMem, q66, q66_raw
  subst hq66
  denote_clear v 80 80

  -- za03 .. zb25 and the `za + 152*zb` fold
  denote_step_all v 81
  let za03_p := toBitVecValue 64 #v[pl (X 0 0) (X 0 0), pl (X 1 0) (X 1 0), pl (X 2 0) (X 2 0), pl (X 3 0) (X 3 0), pl (2 * X 0 0) (X 0 3) + pl (2 * X 0 1) (X 0 2), pl (2 * X 1 0) (X 1 3) + pl (2 * X 1 1) (X 1 2), pl (2 * X 2 0) (X 2 3) + pl (2 * X 2 1) (X 2 2), pl (2 * X 3 0) (X 3 3) + pl (2 * X 3 1) (X 3 2)]
  have hza03_p : v81 = za03_p := by quad_shuffle hv81 with p0a, p37, za03_p
  subst hza03_p
  denote_clear v 81 81
  denote_step_all v 82
  let za03_q := toBitVecValue 64 #v[0, 0, 0, 0, ph (X 0 1) (X 0 1) + ph (2 * X 0 0) (X 0 2), ph (X 1 1) (X 1 1) + ph (2 * X 1 0) (X 1 2), ph (X 2 1) (X 2 1) + ph (2 * X 2 0) (X 2 2), ph (X 3 1) (X 3 1) + ph (2 * X 3 0) (X 3 2)]
  have hza03_q : v82 = za03_q := by quad_shuffle hv82 with q39, za03_q
  subst hza03_q
  denote_clear v 82 82
  denote_step_all v 83
  -- za03: columns 0 and 3
  let za03 := toBitVecValue 64 #v[(0) + (pl (X 0 0) (X 0 0)), (0) + (pl (X 1 0) (X 1 0)), (0) + (pl (X 2 0) (X 2 0)), (0) + (pl (X 3 0) (X 3 0)), (ph (X 0 1) (X 0 1) + ph (2 * X 0 0) (X 0 2)) + (pl (2 * X 0 0) (X 0 3) + pl (2 * X 0 1) (X 0 2)), (ph (X 1 1) (X 1 1) + ph (2 * X 1 0) (X 1 2)) + (pl (2 * X 1 0) (X 1 3) + pl (2 * X 1 1) (X 1 2)), (ph (X 2 1) (X 2 1) + ph (2 * X 2 0) (X 2 2)) + (pl (2 * X 2 0) (X 2 3) + pl (2 * X 2 1) (X 2 2)), (ph (X 3 1) (X 3 1) + ph (2 * X 3 0) (X 3 2)) + (pl (2 * X 3 0) (X 3 3) + pl (2 * X 3 1) (X 3 2))]
  have hza03 : v83 = za03 := by quad_vecbin hv83 with quadValMem, za03, za03_p, za03_q
  subst hza03
  denote_clear v 83 83
  denote_step_all v 84
  let za14_p := toBitVecValue 64 #v[pl (2 * X 0 0) (X 0 1), pl (2 * X 1 0) (X 1 1), pl (2 * X 2 0) (X 2 1), pl (2 * X 3 0) (X 3 1), pl (X 0 2) (X 0 2) + pl (2 * X 0 0) (X 0 4) + pl (2 * X 0 1) (X 0 3), pl (X 1 2) (X 1 2) + pl (2 * X 1 0) (X 1 4) + pl (2 * X 1 1) (X 1 3), pl (X 2 2) (X 2 2) + pl (2 * X 2 0) (X 2 4) + pl (2 * X 2 1) (X 2 3), pl (X 3 2) (X 3 2) + pl (2 * X 3 0) (X 3 4) + pl (2 * X 3 1) (X 3 3)]
  have hza14_p : v84 = za14_p := by quad_shuffle hv84 with p19, p46, za14_p
  subst hza14_p
  denote_clear v 84 84
  denote_step_all v 85
  let za14_q := toBitVecValue 64 #v[ph (X 0 0) (X 0 0), ph (X 1 0) (X 1 0), ph (X 2 0) (X 2 0), ph (X 3 0) (X 3 0), ph (2 * X 0 0) (X 0 3) + ph (2 * X 0 1) (X 0 2), ph (2 * X 1 0) (X 1 3) + ph (2 * X 1 1) (X 1 2), ph (2 * X 2 0) (X 2 3) + ph (2 * X 2 1) (X 2 2), ph (2 * X 3 0) (X 3 3) + ph (2 * X 3 1) (X 3 2)]
  have hza14_q : v85 = za14_q := by quad_shuffle hv85 with q1b, q48, za14_q
  subst hza14_q
  denote_clear v 85 85
  denote_step_all v 86
  -- za14: columns 1 and 4
  let za14 := toBitVecValue 64 #v[(ph (X 0 0) (X 0 0)) + (pl (2 * X 0 0) (X 0 1)), (ph (X 1 0) (X 1 0)) + (pl (2 * X 1 0) (X 1 1)), (ph (X 2 0) (X 2 0)) + (pl (2 * X 2 0) (X 2 1)), (ph (X 3 0) (X 3 0)) + (pl (2 * X 3 0) (X 3 1)), (ph (2 * X 0 0) (X 0 3) + ph (2 * X 0 1) (X 0 2)) + (pl (X 0 2) (X 0 2) + pl (2 * X 0 0) (X 0 4) + pl (2 * X 0 1) (X 0 3)), (ph (2 * X 1 0) (X 1 3) + ph (2 * X 1 1) (X 1 2)) + (pl (X 1 2) (X 1 2) + pl (2 * X 1 0) (X 1 4) + pl (2 * X 1 1) (X 1 3)), (ph (2 * X 2 0) (X 2 3) + ph (2 * X 2 1) (X 2 2)) + (pl (X 2 2) (X 2 2) + pl (2 * X 2 0) (X 2 4) + pl (2 * X 2 1) (X 2 3)), (ph (2 * X 3 0) (X 3 3) + ph (2 * X 3 1) (X 3 2)) + (pl (X 3 2) (X 3 2) + pl (2 * X 3 0) (X 3 4) + pl (2 * X 3 1) (X 3 3))]
  have hza14 : v86 = za14 := by quad_vecbin hv86 with quadValMem, za14, za14_p, za14_q
  subst hza14
  denote_clear v 86 86
  denote_step_all v 87
  let za25_p := toBitVecValue 64 #v[pl (X 0 1) (X 0 1) + pl (2 * X 0 0) (X 0 2), pl (X 1 1) (X 1 1) + pl (2 * X 1 0) (X 1 2), pl (X 2 1) (X 2 1) + pl (2 * X 2 0) (X 2 2), pl (X 3 1) (X 3 1) + pl (2 * X 3 0) (X 3 2), pl (2 * X 0 0) (X 0 5) + pl (2 * X 0 1) (X 0 4), pl (2 * X 1 0) (X 1 5) + pl (2 * X 1 1) (X 1 4), pl (2 * X 2 0) (X 2 5) + pl (2 * X 2 1) (X 2 4), pl (2 * X 3 0) (X 3 5) + pl (2 * X 3 1) (X 3 4)]
  have hza25_p : v87 = za25_p := by quad_shuffle hv87 with p28, p55, za25_p
  subst hza25_p
  denote_clear v 87 87
  denote_step_all v 88
  let za25_q := toBitVecValue 64 #v[ph (2 * X 0 0) (X 0 1), ph (2 * X 1 0) (X 1 1), ph (2 * X 2 0) (X 2 1), ph (2 * X 3 0) (X 3 1), ph (X 0 2) (X 0 2) + ph (2 * X 0 0) (X 0 4) + ph (2 * X 0 1) (X 0 3), ph (X 1 2) (X 1 2) + ph (2 * X 1 0) (X 1 4) + ph (2 * X 1 1) (X 1 3), ph (X 2 2) (X 2 2) + ph (2 * X 2 0) (X 2 4) + ph (2 * X 2 1) (X 2 3), ph (X 3 2) (X 3 2) + ph (2 * X 3 0) (X 3 4) + ph (2 * X 3 1) (X 3 3)]
  have hza25_q : v88 = za25_q := by quad_shuffle hv88 with q2a, q57, za25_q
  subst hza25_q
  denote_clear v 88 88
  denote_step_all v 89
  let za25_hi := toBitVecValue 64 #v[0, 0, 0, 0, pl (2 * X 0 3) (X 0 2) + pl (2 * X 0 4) 0, pl (2 * X 1 3) (X 1 2) + pl (2 * X 1 4) 0, pl (2 * X 2 3) (X 2 2) + pl (2 * X 2 4) 0, pl (2 * X 3 3) (X 3 2) + pl (2 * X 3 4) 0]
  have hza25_hi : v89 = za25_hi := by quad_shuffle hv89 with p55, za25_hi
  subst hza25_hi
  denote_clear v 89 89
  denote_step_all v 90
  let zb03_p := toBitVecValue 64 #v[pl (X 0 3) (X 0 3) + pl (2 * X 0 5) (X 0 1) + pl (2 * X 0 2) (X 0 4), pl (X 1 3) (X 1 3) + pl (2 * X 1 5) (X 1 1) + pl (2 * X 1 2) (X 1 4), pl (X 2 3) (X 2 3) + pl (2 * X 2 5) (X 2 1) + pl (2 * X 2 2) (X 2 4), pl (X 3 3) (X 3 3) + pl (2 * X 3 5) (X 3 1) + pl (2 * X 3 2) (X 3 4), pl (2 * X 0 5) (X 0 4), pl (2 * X 1 5) (X 1 4), pl (2 * X 2 5) (X 2 4), pl (2 * X 3 5) (X 3 4)]
  have hzb03_p : v90 = zb03_p := by quad_shuffle hv90 with p19, p46, zb03_p
  subst hzb03_p
  denote_clear v 90 90
  denote_step_all v 91
  let zb03_q := toBitVecValue 64 #v[ph (2 * X 0 3) (X 0 2) + ph (2 * X 0 4) 0, ph (2 * X 1 3) (X 1 2) + ph (2 * X 1 4) 0, ph (2 * X 2 3) (X 2 2) + ph (2 * X 2 4) 0, ph (2 * X 3 3) (X 3 2) + ph (2 * X 3 4) 0, ph (X 0 4) (X 0 4) + ph (2 * X 0 3) (X 0 5), ph (X 1 4) (X 1 4) + ph (2 * X 1 3) (X 1 5), ph (X 2 4) (X 2 4) + ph (2 * X 2 3) (X 2 5), ph (X 3 4) (X 3 4) + ph (2 * X 3 3) (X 3 5)]
  have hzb03_q : v91 = zb03_q := by quad_shuffle hv91 with q39, q66, zb03_q
  subst hzb03_q
  denote_clear v 91 91
  denote_step_all v 92
  let zb03_pq := toBitVecValue 64 #v[(ph (2 * X 0 3) (X 0 2) + ph (2 * X 0 4) 0) + (pl (X 0 3) (X 0 3) + pl (2 * X 0 5) (X 0 1) + pl (2 * X 0 2) (X 0 4)), (ph (2 * X 1 3) (X 1 2) + ph (2 * X 1 4) 0) + (pl (X 1 3) (X 1 3) + pl (2 * X 1 5) (X 1 1) + pl (2 * X 1 2) (X 1 4)), (ph (2 * X 2 3) (X 2 2) + ph (2 * X 2 4) 0) + (pl (X 2 3) (X 2 3) + pl (2 * X 2 5) (X 2 1) + pl (2 * X 2 2) (X 2 4)), (ph (2 * X 3 3) (X 3 2) + ph (2 * X 3 4) 0) + (pl (X 3 3) (X 3 3) + pl (2 * X 3 5) (X 3 1) + pl (2 * X 3 2) (X 3 4)), (ph (X 0 4) (X 0 4) + ph (2 * X 0 3) (X 0 5)) + (pl (2 * X 0 5) (X 0 4)), (ph (X 1 4) (X 1 4) + ph (2 * X 1 3) (X 1 5)) + (pl (2 * X 1 5) (X 1 4)), (ph (X 2 4) (X 2 4) + ph (2 * X 2 3) (X 2 5)) + (pl (2 * X 2 5) (X 2 4)), (ph (X 3 4) (X 3 4) + ph (2 * X 3 3) (X 3 5)) + (pl (2 * X 3 5) (X 3 4))]
  have hzb03_pq : v92 = zb03_pq := by quad_vecbin hv92 with quadValMem, zb03_p, zb03_pq, zb03_q
  subst hzb03_pq
  denote_clear v 92 92
  denote_step_all v 93
  let zb03_lo := toBitVecValue 64 #v[ph (2 * X 0 0) (X 0 5) + ph (2 * X 0 1) (X 0 4), ph (2 * X 1 0) (X 1 5) + ph (2 * X 1 1) (X 1 4), ph (2 * X 2 0) (X 2 5) + ph (2 * X 2 1) (X 2 4), ph (2 * X 3 0) (X 3 5) + ph (2 * X 3 1) (X 3 4), 0, 0, 0, 0]
  have hzb03_lo : v93 = zb03_lo := by quad_shuffle hv93 with q66, zb03_lo
  subst hzb03_lo
  denote_clear v 93 93
  denote_step_all v 94
  -- zb03: columns 6 and 9
  let zb03 := toBitVecValue 64 #v[((ph (2 * X 0 3) (X 0 2) + ph (2 * X 0 4) 0) + (pl (X 0 3) (X 0 3) + pl (2 * X 0 5) (X 0 1) + pl (2 * X 0 2) (X 0 4))) + (ph (2 * X 0 0) (X 0 5) + ph (2 * X 0 1) (X 0 4)), ((ph (2 * X 1 3) (X 1 2) + ph (2 * X 1 4) 0) + (pl (X 1 3) (X 1 3) + pl (2 * X 1 5) (X 1 1) + pl (2 * X 1 2) (X 1 4))) + (ph (2 * X 1 0) (X 1 5) + ph (2 * X 1 1) (X 1 4)), ((ph (2 * X 2 3) (X 2 2) + ph (2 * X 2 4) 0) + (pl (X 2 3) (X 2 3) + pl (2 * X 2 5) (X 2 1) + pl (2 * X 2 2) (X 2 4))) + (ph (2 * X 2 0) (X 2 5) + ph (2 * X 2 1) (X 2 4)), ((ph (2 * X 3 3) (X 3 2) + ph (2 * X 3 4) 0) + (pl (X 3 3) (X 3 3) + pl (2 * X 3 5) (X 3 1) + pl (2 * X 3 2) (X 3 4))) + (ph (2 * X 3 0) (X 3 5) + ph (2 * X 3 1) (X 3 4)), ((ph (X 0 4) (X 0 4) + ph (2 * X 0 3) (X 0 5)) + (pl (2 * X 0 5) (X 0 4))) + (0), ((ph (X 1 4) (X 1 4) + ph (2 * X 1 3) (X 1 5)) + (pl (2 * X 1 5) (X 1 4))) + (0), ((ph (X 2 4) (X 2 4) + ph (2 * X 2 3) (X 2 5)) + (pl (2 * X 2 5) (X 2 4))) + (0), ((ph (X 3 4) (X 3 4) + ph (2 * X 3 3) (X 3 5)) + (pl (2 * X 3 5) (X 3 4))) + (0)]
  have hzb03 : v94 = zb03 := by quad_vecbin hv94 with quadValMem, zb03, zb03_lo, zb03_pq
  subst hzb03
  denote_clear v 94 94
  denote_step_all v 95
  let zb14_p := toBitVecValue 64 #v[pl (2 * X 0 3) (X 0 4) + pl (2 * X 0 2) (X 0 5), pl (2 * X 1 3) (X 1 4) + pl (2 * X 1 2) (X 1 5), pl (2 * X 2 3) (X 2 4) + pl (2 * X 2 2) (X 2 5), pl (2 * X 3 3) (X 3 4) + pl (2 * X 3 2) (X 3 5), pl (X 0 5) (X 0 5), pl (X 1 5) (X 1 5), pl (X 2 5) (X 2 5), pl (X 3 5) (X 3 5)]
  have hzb14_p : v95 = zb14_p := by quad_shuffle hv95 with p0a, p37, zb14_p
  subst hzb14_p
  denote_clear v 95 95
  denote_step_all v 96
  let zb14_q := toBitVecValue 64 #v[ph (X 0 3) (X 0 3) + ph (2 * X 0 5) (X 0 1) + ph (2 * X 0 2) (X 0 4), ph (X 1 3) (X 1 3) + ph (2 * X 1 5) (X 1 1) + ph (2 * X 1 2) (X 1 4), ph (X 2 3) (X 2 3) + ph (2 * X 2 5) (X 2 1) + ph (2 * X 2 2) (X 2 4), ph (X 3 3) (X 3 3) + ph (2 * X 3 5) (X 3 1) + ph (2 * X 3 2) (X 3 4), ph (2 * X 0 5) (X 0 4), ph (2 * X 1 5) (X 1 4), ph (2 * X 2 5) (X 2 4), ph (2 * X 3 5) (X 3 4)]
  have hzb14_q : v96 = zb14_q := by quad_shuffle hv96 with q2a, q57, zb14_q
  subst hzb14_q
  denote_clear v 96 96
  denote_step_all v 97
  -- zb14: columns 7 and 10
  let zb14 := toBitVecValue 64 #v[(ph (X 0 3) (X 0 3) + ph (2 * X 0 5) (X 0 1) + ph (2 * X 0 2) (X 0 4)) + (pl (2 * X 0 3) (X 0 4) + pl (2 * X 0 2) (X 0 5)), (ph (X 1 3) (X 1 3) + ph (2 * X 1 5) (X 1 1) + ph (2 * X 1 2) (X 1 4)) + (pl (2 * X 1 3) (X 1 4) + pl (2 * X 1 2) (X 1 5)), (ph (X 2 3) (X 2 3) + ph (2 * X 2 5) (X 2 1) + ph (2 * X 2 2) (X 2 4)) + (pl (2 * X 2 3) (X 2 4) + pl (2 * X 2 2) (X 2 5)), (ph (X 3 3) (X 3 3) + ph (2 * X 3 5) (X 3 1) + ph (2 * X 3 2) (X 3 4)) + (pl (2 * X 3 3) (X 3 4) + pl (2 * X 3 2) (X 3 5)), (ph (2 * X 0 5) (X 0 4)) + (pl (X 0 5) (X 0 5)), (ph (2 * X 1 5) (X 1 4)) + (pl (X 1 5) (X 1 5)), (ph (2 * X 2 5) (X 2 4)) + (pl (X 2 5) (X 2 5)), (ph (2 * X 3 5) (X 3 4)) + (pl (X 3 5) (X 3 5))]
  have hzb14 : v97 = zb14 := by quad_vecbin hv97 with quadValMem, zb14, zb14_p, zb14_q
  subst hzb14
  denote_clear v 97 97
  denote_step_all v 98
  let zb25_p := toBitVecValue 64 #v[pl (X 0 4) (X 0 4) + pl (2 * X 0 3) (X 0 5), pl (X 1 4) (X 1 4) + pl (2 * X 1 3) (X 1 5), pl (X 2 4) (X 2 4) + pl (2 * X 2 3) (X 2 5), pl (X 3 4) (X 3 4) + pl (2 * X 3 3) (X 3 5), 0, 0, 0, 0]
  have hzb25_p : v98 = zb25_p := by quad_shuffle hv98 with p28, zb25_p
  subst hzb25_p
  denote_clear v 98 98
  denote_step_all v 99
  let zb25_q := toBitVecValue 64 #v[ph (2 * X 0 3) (X 0 4) + ph (2 * X 0 2) (X 0 5), ph (2 * X 1 3) (X 1 4) + ph (2 * X 1 2) (X 1 5), ph (2 * X 2 3) (X 2 4) + ph (2 * X 2 2) (X 2 5), ph (2 * X 3 3) (X 3 4) + ph (2 * X 3 2) (X 3 5), ph (X 0 5) (X 0 5), ph (X 1 5) (X 1 5), ph (X 2 5) (X 2 5), ph (X 3 5) (X 3 5)]
  have hzb25_q : v99 = zb25_q := by quad_shuffle hv99 with q1b, q48, zb25_q
  subst hzb25_q
  denote_clear v 99 99
  denote_step_all v 100
  -- zb25: columns 8 and 11
  let zb25 := toBitVecValue 64 #v[(ph (2 * X 0 3) (X 0 4) + ph (2 * X 0 2) (X 0 5)) + (pl (X 0 4) (X 0 4) + pl (2 * X 0 3) (X 0 5)), (ph (2 * X 1 3) (X 1 4) + ph (2 * X 1 2) (X 1 5)) + (pl (X 1 4) (X 1 4) + pl (2 * X 1 3) (X 1 5)), (ph (2 * X 2 3) (X 2 4) + ph (2 * X 2 2) (X 2 5)) + (pl (X 2 4) (X 2 4) + pl (2 * X 2 3) (X 2 5)), (ph (2 * X 3 3) (X 3 4) + ph (2 * X 3 2) (X 3 5)) + (pl (X 3 4) (X 3 4) + pl (2 * X 3 3) (X 3 5)), (ph (X 0 5) (X 0 5)) + (0), (ph (X 1 5) (X 1 5)) + (0), (ph (X 2 5) (X 2 5)) + (0), (ph (X 3 5) (X 3 5)) + (0)]
  have hzb25 : v100 = zb25 := by quad_vecbin hv100 with quadValMem, zb25, zb25_p, zb25_q
  subst hzb25
  denote_clear v 100 100
  denote_step_all v 101
  let zb03_shl7 := toBitVecValue 64 #v[(((ph (2 * X 0 3) (X 0 2) + ph (2 * X 0 4) 0) + (pl (X 0 3) (X 0 3) + pl (2 * X 0 5) (X 0 1) + pl (2 * X 0 2) (X 0 4))) + (ph (2 * X 0 0) (X 0 5) + ph (2 * X 0 1) (X 0 4))) * 128, (((ph (2 * X 1 3) (X 1 2) + ph (2 * X 1 4) 0) + (pl (X 1 3) (X 1 3) + pl (2 * X 1 5) (X 1 1) + pl (2 * X 1 2) (X 1 4))) + (ph (2 * X 1 0) (X 1 5) + ph (2 * X 1 1) (X 1 4))) * 128, (((ph (2 * X 2 3) (X 2 2) + ph (2 * X 2 4) 0) + (pl (X 2 3) (X 2 3) + pl (2 * X 2 5) (X 2 1) + pl (2 * X 2 2) (X 2 4))) + (ph (2 * X 2 0) (X 2 5) + ph (2 * X 2 1) (X 2 4))) * 128, (((ph (2 * X 3 3) (X 3 2) + ph (2 * X 3 4) 0) + (pl (X 3 3) (X 3 3) + pl (2 * X 3 5) (X 3 1) + pl (2 * X 3 2) (X 3 4))) + (ph (2 * X 3 0) (X 3 5) + ph (2 * X 3 1) (X 3 4))) * 128, (((ph (X 0 4) (X 0 4) + ph (2 * X 0 3) (X 0 5)) + (pl (2 * X 0 5) (X 0 4))) + (0)) * 128, (((ph (X 1 4) (X 1 4) + ph (2 * X 1 3) (X 1 5)) + (pl (2 * X 1 5) (X 1 4))) + (0)) * 128, (((ph (X 2 4) (X 2 4) + ph (2 * X 2 3) (X 2 5)) + (pl (2 * X 2 5) (X 2 4))) + (0)) * 128, (((ph (X 3 4) (X 3 4) + ph (2 * X 3 3) (X 3 5)) + (pl (2 * X 3 5) (X 3 4))) + (0)) * 128]
  have hzb03_shl7 : v101 = zb03_shl7 := by quad_vecbin hv101 with quadValMem, zb03, zb03_shl7
  subst hzb03_shl7
  denote_clear v 101 101
  denote_step_all v 102
  let z03_part := toBitVecValue 64 #v[((0) + (pl (X 0 0) (X 0 0))) + ((((ph (2 * X 0 3) (X 0 2) + ph (2 * X 0 4) 0) + (pl (X 0 3) (X 0 3) + pl (2 * X 0 5) (X 0 1) + pl (2 * X 0 2) (X 0 4))) + (ph (2 * X 0 0) (X 0 5) + ph (2 * X 0 1) (X 0 4))) * 128), ((0) + (pl (X 1 0) (X 1 0))) + ((((ph (2 * X 1 3) (X 1 2) + ph (2 * X 1 4) 0) + (pl (X 1 3) (X 1 3) + pl (2 * X 1 5) (X 1 1) + pl (2 * X 1 2) (X 1 4))) + (ph (2 * X 1 0) (X 1 5) + ph (2 * X 1 1) (X 1 4))) * 128), ((0) + (pl (X 2 0) (X 2 0))) + ((((ph (2 * X 2 3) (X 2 2) + ph (2 * X 2 4) 0) + (pl (X 2 3) (X 2 3) + pl (2 * X 2 5) (X 2 1) + pl (2 * X 2 2) (X 2 4))) + (ph (2 * X 2 0) (X 2 5) + ph (2 * X 2 1) (X 2 4))) * 128), ((0) + (pl (X 3 0) (X 3 0))) + ((((ph (2 * X 3 3) (X 3 2) + ph (2 * X 3 4) 0) + (pl (X 3 3) (X 3 3) + pl (2 * X 3 5) (X 3 1) + pl (2 * X 3 2) (X 3 4))) + (ph (2 * X 3 0) (X 3 5) + ph (2 * X 3 1) (X 3 4))) * 128), ((ph (X 0 1) (X 0 1) + ph (2 * X 0 0) (X 0 2)) + (pl (2 * X 0 0) (X 0 3) + pl (2 * X 0 1) (X 0 2))) + ((((ph (X 0 4) (X 0 4) + ph (2 * X 0 3) (X 0 5)) + (pl (2 * X 0 5) (X 0 4))) + (0)) * 128), ((ph (X 1 1) (X 1 1) + ph (2 * X 1 0) (X 1 2)) + (pl (2 * X 1 0) (X 1 3) + pl (2 * X 1 1) (X 1 2))) + ((((ph (X 1 4) (X 1 4) + ph (2 * X 1 3) (X 1 5)) + (pl (2 * X 1 5) (X 1 4))) + (0)) * 128), ((ph (X 2 1) (X 2 1) + ph (2 * X 2 0) (X 2 2)) + (pl (2 * X 2 0) (X 2 3) + pl (2 * X 2 1) (X 2 2))) + ((((ph (X 2 4) (X 2 4) + ph (2 * X 2 3) (X 2 5)) + (pl (2 * X 2 5) (X 2 4))) + (0)) * 128), ((ph (X 3 1) (X 3 1) + ph (2 * X 3 0) (X 3 2)) + (pl (2 * X 3 0) (X 3 3) + pl (2 * X 3 1) (X 3 2))) + ((((ph (X 3 4) (X 3 4) + ph (2 * X 3 3) (X 3 5)) + (pl (2 * X 3 5) (X 3 4))) + (0)) * 128)]
  have hz03_part : v102 = z03_part := by quad_vecbin hv102 with quadValMem, z03_part, za03, zb03_shl7
  subst hz03_part
  denote_clear v 102 102
  denote_step_all v 103
  let zb03_mul24 := toBitVecValue 64 #v[(((ph (2 * X 0 3) (X 0 2) + ph (2 * X 0 4) 0) + (pl (X 0 3) (X 0 3) + pl (2 * X 0 5) (X 0 1) + pl (2 * X 0 2) (X 0 4))) + (ph (2 * X 0 0) (X 0 5) + ph (2 * X 0 1) (X 0 4))) * 24, (((ph (2 * X 1 3) (X 1 2) + ph (2 * X 1 4) 0) + (pl (X 1 3) (X 1 3) + pl (2 * X 1 5) (X 1 1) + pl (2 * X 1 2) (X 1 4))) + (ph (2 * X 1 0) (X 1 5) + ph (2 * X 1 1) (X 1 4))) * 24, (((ph (2 * X 2 3) (X 2 2) + ph (2 * X 2 4) 0) + (pl (X 2 3) (X 2 3) + pl (2 * X 2 5) (X 2 1) + pl (2 * X 2 2) (X 2 4))) + (ph (2 * X 2 0) (X 2 5) + ph (2 * X 2 1) (X 2 4))) * 24, (((ph (2 * X 3 3) (X 3 2) + ph (2 * X 3 4) 0) + (pl (X 3 3) (X 3 3) + pl (2 * X 3 5) (X 3 1) + pl (2 * X 3 2) (X 3 4))) + (ph (2 * X 3 0) (X 3 5) + ph (2 * X 3 1) (X 3 4))) * 24, (((ph (X 0 4) (X 0 4) + ph (2 * X 0 3) (X 0 5)) + (pl (2 * X 0 5) (X 0 4))) + (0)) * 24, (((ph (X 1 4) (X 1 4) + ph (2 * X 1 3) (X 1 5)) + (pl (2 * X 1 5) (X 1 4))) + (0)) * 24, (((ph (X 2 4) (X 2 4) + ph (2 * X 2 3) (X 2 5)) + (pl (2 * X 2 5) (X 2 4))) + (0)) * 24, (((ph (X 3 4) (X 3 4) + ph (2 * X 3 3) (X 3 5)) + (pl (2 * X 3 5) (X 3 4))) + (0)) * 24]
  have hzb03_mul24 : v103 = zb03_mul24 := by quad_vecbin hv103 with quadValMem, zb03, zb03_mul24
  subst hzb03_mul24
  denote_clear v 103 103
  denote_step_all v 104
  -- z03: `za03 + 152*zb03`, limbs 0 and 3 of all four elements
  let z03 := toBitVecValue 64 #v[(((0) + (pl (X 0 0) (X 0 0))) + ((((ph (2 * X 0 3) (X 0 2) + ph (2 * X 0 4) 0) + (pl (X 0 3) (X 0 3) + pl (2 * X 0 5) (X 0 1) + pl (2 * X 0 2) (X 0 4))) + (ph (2 * X 0 0) (X 0 5) + ph (2 * X 0 1) (X 0 4))) * 128)) + ((((ph (2 * X 0 3) (X 0 2) + ph (2 * X 0 4) 0) + (pl (X 0 3) (X 0 3) + pl (2 * X 0 5) (X 0 1) + pl (2 * X 0 2) (X 0 4))) + (ph (2 * X 0 0) (X 0 5) + ph (2 * X 0 1) (X 0 4))) * 24), (((0) + (pl (X 1 0) (X 1 0))) + ((((ph (2 * X 1 3) (X 1 2) + ph (2 * X 1 4) 0) + (pl (X 1 3) (X 1 3) + pl (2 * X 1 5) (X 1 1) + pl (2 * X 1 2) (X 1 4))) + (ph (2 * X 1 0) (X 1 5) + ph (2 * X 1 1) (X 1 4))) * 128)) + ((((ph (2 * X 1 3) (X 1 2) + ph (2 * X 1 4) 0) + (pl (X 1 3) (X 1 3) + pl (2 * X 1 5) (X 1 1) + pl (2 * X 1 2) (X 1 4))) + (ph (2 * X 1 0) (X 1 5) + ph (2 * X 1 1) (X 1 4))) * 24), (((0) + (pl (X 2 0) (X 2 0))) + ((((ph (2 * X 2 3) (X 2 2) + ph (2 * X 2 4) 0) + (pl (X 2 3) (X 2 3) + pl (2 * X 2 5) (X 2 1) + pl (2 * X 2 2) (X 2 4))) + (ph (2 * X 2 0) (X 2 5) + ph (2 * X 2 1) (X 2 4))) * 128)) + ((((ph (2 * X 2 3) (X 2 2) + ph (2 * X 2 4) 0) + (pl (X 2 3) (X 2 3) + pl (2 * X 2 5) (X 2 1) + pl (2 * X 2 2) (X 2 4))) + (ph (2 * X 2 0) (X 2 5) + ph (2 * X 2 1) (X 2 4))) * 24), (((0) + (pl (X 3 0) (X 3 0))) + ((((ph (2 * X 3 3) (X 3 2) + ph (2 * X 3 4) 0) + (pl (X 3 3) (X 3 3) + pl (2 * X 3 5) (X 3 1) + pl (2 * X 3 2) (X 3 4))) + (ph (2 * X 3 0) (X 3 5) + ph (2 * X 3 1) (X 3 4))) * 128)) + ((((ph (2 * X 3 3) (X 3 2) + ph (2 * X 3 4) 0) + (pl (X 3 3) (X 3 3) + pl (2 * X 3 5) (X 3 1) + pl (2 * X 3 2) (X 3 4))) + (ph (2 * X 3 0) (X 3 5) + ph (2 * X 3 1) (X 3 4))) * 24), (((ph (X 0 1) (X 0 1) + ph (2 * X 0 0) (X 0 2)) + (pl (2 * X 0 0) (X 0 3) + pl (2 * X 0 1) (X 0 2))) + ((((ph (X 0 4) (X 0 4) + ph (2 * X 0 3) (X 0 5)) + (pl (2 * X 0 5) (X 0 4))) + (0)) * 128)) + ((((ph (X 0 4) (X 0 4) + ph (2 * X 0 3) (X 0 5)) + (pl (2 * X 0 5) (X 0 4))) + (0)) * 24), (((ph (X 1 1) (X 1 1) + ph (2 * X 1 0) (X 1 2)) + (pl (2 * X 1 0) (X 1 3) + pl (2 * X 1 1) (X 1 2))) + ((((ph (X 1 4) (X 1 4) + ph (2 * X 1 3) (X 1 5)) + (pl (2 * X 1 5) (X 1 4))) + (0)) * 128)) + ((((ph (X 1 4) (X 1 4) + ph (2 * X 1 3) (X 1 5)) + (pl (2 * X 1 5) (X 1 4))) + (0)) * 24), (((ph (X 2 1) (X 2 1) + ph (2 * X 2 0) (X 2 2)) + (pl (2 * X 2 0) (X 2 3) + pl (2 * X 2 1) (X 2 2))) + ((((ph (X 2 4) (X 2 4) + ph (2 * X 2 3) (X 2 5)) + (pl (2 * X 2 5) (X 2 4))) + (0)) * 128)) + ((((ph (X 2 4) (X 2 4) + ph (2 * X 2 3) (X 2 5)) + (pl (2 * X 2 5) (X 2 4))) + (0)) * 24), (((ph (X 3 1) (X 3 1) + ph (2 * X 3 0) (X 3 2)) + (pl (2 * X 3 0) (X 3 3) + pl (2 * X 3 1) (X 3 2))) + ((((ph (X 3 4) (X 3 4) + ph (2 * X 3 3) (X 3 5)) + (pl (2 * X 3 5) (X 3 4))) + (0)) * 128)) + ((((ph (X 3 4) (X 3 4) + ph (2 * X 3 3) (X 3 5)) + (pl (2 * X 3 5) (X 3 4))) + (0)) * 24)]
  have hz03 : v104 = z03 := by quad_vecbin hv104 with quadValMem, z03, z03_part, zb03_mul24
  subst hz03
  denote_clear v 104 104
  denote_step_all v 105
  let zb14_shl7 := toBitVecValue 64 #v[((ph (X 0 3) (X 0 3) + ph (2 * X 0 5) (X 0 1) + ph (2 * X 0 2) (X 0 4)) + (pl (2 * X 0 3) (X 0 4) + pl (2 * X 0 2) (X 0 5))) * 128, ((ph (X 1 3) (X 1 3) + ph (2 * X 1 5) (X 1 1) + ph (2 * X 1 2) (X 1 4)) + (pl (2 * X 1 3) (X 1 4) + pl (2 * X 1 2) (X 1 5))) * 128, ((ph (X 2 3) (X 2 3) + ph (2 * X 2 5) (X 2 1) + ph (2 * X 2 2) (X 2 4)) + (pl (2 * X 2 3) (X 2 4) + pl (2 * X 2 2) (X 2 5))) * 128, ((ph (X 3 3) (X 3 3) + ph (2 * X 3 5) (X 3 1) + ph (2 * X 3 2) (X 3 4)) + (pl (2 * X 3 3) (X 3 4) + pl (2 * X 3 2) (X 3 5))) * 128, ((ph (2 * X 0 5) (X 0 4)) + (pl (X 0 5) (X 0 5))) * 128, ((ph (2 * X 1 5) (X 1 4)) + (pl (X 1 5) (X 1 5))) * 128, ((ph (2 * X 2 5) (X 2 4)) + (pl (X 2 5) (X 2 5))) * 128, ((ph (2 * X 3 5) (X 3 4)) + (pl (X 3 5) (X 3 5))) * 128]
  have hzb14_shl7 : v105 = zb14_shl7 := by quad_vecbin hv105 with quadValMem, zb14, zb14_shl7
  subst hzb14_shl7
  denote_clear v 105 105
  denote_step_all v 106
  let z14_part := toBitVecValue 64 #v[((ph (X 0 0) (X 0 0)) + (pl (2 * X 0 0) (X 0 1))) + (((ph (X 0 3) (X 0 3) + ph (2 * X 0 5) (X 0 1) + ph (2 * X 0 2) (X 0 4)) + (pl (2 * X 0 3) (X 0 4) + pl (2 * X 0 2) (X 0 5))) * 128), ((ph (X 1 0) (X 1 0)) + (pl (2 * X 1 0) (X 1 1))) + (((ph (X 1 3) (X 1 3) + ph (2 * X 1 5) (X 1 1) + ph (2 * X 1 2) (X 1 4)) + (pl (2 * X 1 3) (X 1 4) + pl (2 * X 1 2) (X 1 5))) * 128), ((ph (X 2 0) (X 2 0)) + (pl (2 * X 2 0) (X 2 1))) + (((ph (X 2 3) (X 2 3) + ph (2 * X 2 5) (X 2 1) + ph (2 * X 2 2) (X 2 4)) + (pl (2 * X 2 3) (X 2 4) + pl (2 * X 2 2) (X 2 5))) * 128), ((ph (X 3 0) (X 3 0)) + (pl (2 * X 3 0) (X 3 1))) + (((ph (X 3 3) (X 3 3) + ph (2 * X 3 5) (X 3 1) + ph (2 * X 3 2) (X 3 4)) + (pl (2 * X 3 3) (X 3 4) + pl (2 * X 3 2) (X 3 5))) * 128), ((ph (2 * X 0 0) (X 0 3) + ph (2 * X 0 1) (X 0 2)) + (pl (X 0 2) (X 0 2) + pl (2 * X 0 0) (X 0 4) + pl (2 * X 0 1) (X 0 3))) + (((ph (2 * X 0 5) (X 0 4)) + (pl (X 0 5) (X 0 5))) * 128), ((ph (2 * X 1 0) (X 1 3) + ph (2 * X 1 1) (X 1 2)) + (pl (X 1 2) (X 1 2) + pl (2 * X 1 0) (X 1 4) + pl (2 * X 1 1) (X 1 3))) + (((ph (2 * X 1 5) (X 1 4)) + (pl (X 1 5) (X 1 5))) * 128), ((ph (2 * X 2 0) (X 2 3) + ph (2 * X 2 1) (X 2 2)) + (pl (X 2 2) (X 2 2) + pl (2 * X 2 0) (X 2 4) + pl (2 * X 2 1) (X 2 3))) + (((ph (2 * X 2 5) (X 2 4)) + (pl (X 2 5) (X 2 5))) * 128), ((ph (2 * X 3 0) (X 3 3) + ph (2 * X 3 1) (X 3 2)) + (pl (X 3 2) (X 3 2) + pl (2 * X 3 0) (X 3 4) + pl (2 * X 3 1) (X 3 3))) + (((ph (2 * X 3 5) (X 3 4)) + (pl (X 3 5) (X 3 5))) * 128)]
  have hz14_part : v106 = z14_part := by quad_vecbin hv106 with quadValMem, z14_part, za14, zb14_shl7
  subst hz14_part
  denote_clear v 106 106
  denote_step_all v 107
  let zb14_mul24 := toBitVecValue 64 #v[((ph (X 0 3) (X 0 3) + ph (2 * X 0 5) (X 0 1) + ph (2 * X 0 2) (X 0 4)) + (pl (2 * X 0 3) (X 0 4) + pl (2 * X 0 2) (X 0 5))) * 24, ((ph (X 1 3) (X 1 3) + ph (2 * X 1 5) (X 1 1) + ph (2 * X 1 2) (X 1 4)) + (pl (2 * X 1 3) (X 1 4) + pl (2 * X 1 2) (X 1 5))) * 24, ((ph (X 2 3) (X 2 3) + ph (2 * X 2 5) (X 2 1) + ph (2 * X 2 2) (X 2 4)) + (pl (2 * X 2 3) (X 2 4) + pl (2 * X 2 2) (X 2 5))) * 24, ((ph (X 3 3) (X 3 3) + ph (2 * X 3 5) (X 3 1) + ph (2 * X 3 2) (X 3 4)) + (pl (2 * X 3 3) (X 3 4) + pl (2 * X 3 2) (X 3 5))) * 24, ((ph (2 * X 0 5) (X 0 4)) + (pl (X 0 5) (X 0 5))) * 24, ((ph (2 * X 1 5) (X 1 4)) + (pl (X 1 5) (X 1 5))) * 24, ((ph (2 * X 2 5) (X 2 4)) + (pl (X 2 5) (X 2 5))) * 24, ((ph (2 * X 3 5) (X 3 4)) + (pl (X 3 5) (X 3 5))) * 24]
  have hzb14_mul24 : v107 = zb14_mul24 := by quad_vecbin hv107 with quadValMem, zb14, zb14_mul24
  subst hzb14_mul24
  denote_clear v 107 107
  denote_step_all v 108
  -- z14: limbs 1 and 4
  let z14 := toBitVecValue 64 #v[(((ph (X 0 0) (X 0 0)) + (pl (2 * X 0 0) (X 0 1))) + (((ph (X 0 3) (X 0 3) + ph (2 * X 0 5) (X 0 1) + ph (2 * X 0 2) (X 0 4)) + (pl (2 * X 0 3) (X 0 4) + pl (2 * X 0 2) (X 0 5))) * 128)) + (((ph (X 0 3) (X 0 3) + ph (2 * X 0 5) (X 0 1) + ph (2 * X 0 2) (X 0 4)) + (pl (2 * X 0 3) (X 0 4) + pl (2 * X 0 2) (X 0 5))) * 24), (((ph (X 1 0) (X 1 0)) + (pl (2 * X 1 0) (X 1 1))) + (((ph (X 1 3) (X 1 3) + ph (2 * X 1 5) (X 1 1) + ph (2 * X 1 2) (X 1 4)) + (pl (2 * X 1 3) (X 1 4) + pl (2 * X 1 2) (X 1 5))) * 128)) + (((ph (X 1 3) (X 1 3) + ph (2 * X 1 5) (X 1 1) + ph (2 * X 1 2) (X 1 4)) + (pl (2 * X 1 3) (X 1 4) + pl (2 * X 1 2) (X 1 5))) * 24), (((ph (X 2 0) (X 2 0)) + (pl (2 * X 2 0) (X 2 1))) + (((ph (X 2 3) (X 2 3) + ph (2 * X 2 5) (X 2 1) + ph (2 * X 2 2) (X 2 4)) + (pl (2 * X 2 3) (X 2 4) + pl (2 * X 2 2) (X 2 5))) * 128)) + (((ph (X 2 3) (X 2 3) + ph (2 * X 2 5) (X 2 1) + ph (2 * X 2 2) (X 2 4)) + (pl (2 * X 2 3) (X 2 4) + pl (2 * X 2 2) (X 2 5))) * 24), (((ph (X 3 0) (X 3 0)) + (pl (2 * X 3 0) (X 3 1))) + (((ph (X 3 3) (X 3 3) + ph (2 * X 3 5) (X 3 1) + ph (2 * X 3 2) (X 3 4)) + (pl (2 * X 3 3) (X 3 4) + pl (2 * X 3 2) (X 3 5))) * 128)) + (((ph (X 3 3) (X 3 3) + ph (2 * X 3 5) (X 3 1) + ph (2 * X 3 2) (X 3 4)) + (pl (2 * X 3 3) (X 3 4) + pl (2 * X 3 2) (X 3 5))) * 24), (((ph (2 * X 0 0) (X 0 3) + ph (2 * X 0 1) (X 0 2)) + (pl (X 0 2) (X 0 2) + pl (2 * X 0 0) (X 0 4) + pl (2 * X 0 1) (X 0 3))) + (((ph (2 * X 0 5) (X 0 4)) + (pl (X 0 5) (X 0 5))) * 128)) + (((ph (2 * X 0 5) (X 0 4)) + (pl (X 0 5) (X 0 5))) * 24), (((ph (2 * X 1 0) (X 1 3) + ph (2 * X 1 1) (X 1 2)) + (pl (X 1 2) (X 1 2) + pl (2 * X 1 0) (X 1 4) + pl (2 * X 1 1) (X 1 3))) + (((ph (2 * X 1 5) (X 1 4)) + (pl (X 1 5) (X 1 5))) * 128)) + (((ph (2 * X 1 5) (X 1 4)) + (pl (X 1 5) (X 1 5))) * 24), (((ph (2 * X 2 0) (X 2 3) + ph (2 * X 2 1) (X 2 2)) + (pl (X 2 2) (X 2 2) + pl (2 * X 2 0) (X 2 4) + pl (2 * X 2 1) (X 2 3))) + (((ph (2 * X 2 5) (X 2 4)) + (pl (X 2 5) (X 2 5))) * 128)) + (((ph (2 * X 2 5) (X 2 4)) + (pl (X 2 5) (X 2 5))) * 24), (((ph (2 * X 3 0) (X 3 3) + ph (2 * X 3 1) (X 3 2)) + (pl (X 3 2) (X 3 2) + pl (2 * X 3 0) (X 3 4) + pl (2 * X 3 1) (X 3 3))) + (((ph (2 * X 3 5) (X 3 4)) + (pl (X 3 5) (X 3 5))) * 128)) + (((ph (2 * X 3 5) (X 3 4)) + (pl (X 3 5) (X 3 5))) * 24)]
  have hz14 : v108 = z14 := by quad_vecbin hv108 with quadValMem, z14, z14_part, zb14_mul24
  subst hz14
  denote_clear v 108 108
  denote_step_all v 109
  let zb25_shl7 := toBitVecValue 64 #v[((ph (2 * X 0 3) (X 0 4) + ph (2 * X 0 2) (X 0 5)) + (pl (X 0 4) (X 0 4) + pl (2 * X 0 3) (X 0 5))) * 128, ((ph (2 * X 1 3) (X 1 4) + ph (2 * X 1 2) (X 1 5)) + (pl (X 1 4) (X 1 4) + pl (2 * X 1 3) (X 1 5))) * 128, ((ph (2 * X 2 3) (X 2 4) + ph (2 * X 2 2) (X 2 5)) + (pl (X 2 4) (X 2 4) + pl (2 * X 2 3) (X 2 5))) * 128, ((ph (2 * X 3 3) (X 3 4) + ph (2 * X 3 2) (X 3 5)) + (pl (X 3 4) (X 3 4) + pl (2 * X 3 3) (X 3 5))) * 128, ((ph (X 0 5) (X 0 5)) + (0)) * 128, ((ph (X 1 5) (X 1 5)) + (0)) * 128, ((ph (X 2 5) (X 2 5)) + (0)) * 128, ((ph (X 3 5) (X 3 5)) + (0)) * 128]
  have hzb25_shl7 : v109 = zb25_shl7 := by quad_vecbin hv109 with quadValMem, zb25, zb25_shl7
  subst hzb25_shl7
  denote_clear v 109 109
  denote_step_all v 110
  let zb25_mul24 := toBitVecValue 64 #v[((ph (2 * X 0 3) (X 0 4) + ph (2 * X 0 2) (X 0 5)) + (pl (X 0 4) (X 0 4) + pl (2 * X 0 3) (X 0 5))) * 24, ((ph (2 * X 1 3) (X 1 4) + ph (2 * X 1 2) (X 1 5)) + (pl (X 1 4) (X 1 4) + pl (2 * X 1 3) (X 1 5))) * 24, ((ph (2 * X 2 3) (X 2 4) + ph (2 * X 2 2) (X 2 5)) + (pl (X 2 4) (X 2 4) + pl (2 * X 2 3) (X 2 5))) * 24, ((ph (2 * X 3 3) (X 3 4) + ph (2 * X 3 2) (X 3 5)) + (pl (X 3 4) (X 3 4) + pl (2 * X 3 3) (X 3 5))) * 24, ((ph (X 0 5) (X 0 5)) + (0)) * 24, ((ph (X 1 5) (X 1 5)) + (0)) * 24, ((ph (X 2 5) (X 2 5)) + (0)) * 24, ((ph (X 3 5) (X 3 5)) + (0)) * 24]
  have hzb25_mul24 : v110 = zb25_mul24 := by quad_vecbin hv110 with quadValMem, zb25, zb25_mul24
  subst hzb25_mul24
  denote_clear v 110 110
  denote_step_all v 111
  let za25_a := toBitVecValue 64 #v[(0) + (pl (X 0 1) (X 0 1) + pl (2 * X 0 0) (X 0 2)), (0) + (pl (X 1 1) (X 1 1) + pl (2 * X 1 0) (X 1 2)), (0) + (pl (X 2 1) (X 2 1) + pl (2 * X 2 0) (X 2 2)), (0) + (pl (X 3 1) (X 3 1) + pl (2 * X 3 0) (X 3 2)), (pl (2 * X 0 3) (X 0 2) + pl (2 * X 0 4) 0) + (pl (2 * X 0 0) (X 0 5) + pl (2 * X 0 1) (X 0 4)), (pl (2 * X 1 3) (X 1 2) + pl (2 * X 1 4) 0) + (pl (2 * X 1 0) (X 1 5) + pl (2 * X 1 1) (X 1 4)), (pl (2 * X 2 3) (X 2 2) + pl (2 * X 2 4) 0) + (pl (2 * X 2 0) (X 2 5) + pl (2 * X 2 1) (X 2 4)), (pl (2 * X 3 3) (X 3 2) + pl (2 * X 3 4) 0) + (pl (2 * X 3 0) (X 3 5) + pl (2 * X 3 1) (X 3 4))]
  have hza25_a : v111 = za25_a := by quad_vecbin hv111 with quadValMem, za25_a, za25_hi, za25_p
  subst hza25_a
  denote_clear v 111 111
  denote_step_all v 112
  let za25_b := toBitVecValue 64 #v[((0) + (pl (X 0 1) (X 0 1) + pl (2 * X 0 0) (X 0 2))) + (((ph (2 * X 0 3) (X 0 4) + ph (2 * X 0 2) (X 0 5)) + (pl (X 0 4) (X 0 4) + pl (2 * X 0 3) (X 0 5))) * 128), ((0) + (pl (X 1 1) (X 1 1) + pl (2 * X 1 0) (X 1 2))) + (((ph (2 * X 1 3) (X 1 4) + ph (2 * X 1 2) (X 1 5)) + (pl (X 1 4) (X 1 4) + pl (2 * X 1 3) (X 1 5))) * 128), ((0) + (pl (X 2 1) (X 2 1) + pl (2 * X 2 0) (X 2 2))) + (((ph (2 * X 2 3) (X 2 4) + ph (2 * X 2 2) (X 2 5)) + (pl (X 2 4) (X 2 4) + pl (2 * X 2 3) (X 2 5))) * 128), ((0) + (pl (X 3 1) (X 3 1) + pl (2 * X 3 0) (X 3 2))) + (((ph (2 * X 3 3) (X 3 4) + ph (2 * X 3 2) (X 3 5)) + (pl (X 3 4) (X 3 4) + pl (2 * X 3 3) (X 3 5))) * 128), ((pl (2 * X 0 3) (X 0 2) + pl (2 * X 0 4) 0) + (pl (2 * X 0 0) (X 0 5) + pl (2 * X 0 1) (X 0 4))) + (((ph (X 0 5) (X 0 5)) + (0)) * 128), ((pl (2 * X 1 3) (X 1 2) + pl (2 * X 1 4) 0) + (pl (2 * X 1 0) (X 1 5) + pl (2 * X 1 1) (X 1 4))) + (((ph (X 1 5) (X 1 5)) + (0)) * 128), ((pl (2 * X 2 3) (X 2 2) + pl (2 * X 2 4) 0) + (pl (2 * X 2 0) (X 2 5) + pl (2 * X 2 1) (X 2 4))) + (((ph (X 2 5) (X 2 5)) + (0)) * 128), ((pl (2 * X 3 3) (X 3 2) + pl (2 * X 3 4) 0) + (pl (2 * X 3 0) (X 3 5) + pl (2 * X 3 1) (X 3 4))) + (((ph (X 3 5) (X 3 5)) + (0)) * 128)]
  have hza25_b : v112 = za25_b := by quad_vecbin hv112 with quadValMem, za25_a, za25_b, zb25_shl7
  subst hza25_b
  denote_clear v 112 112
  denote_step_all v 113
  let za25_c := toBitVecValue 64 #v[(((0) + (pl (X 0 1) (X 0 1) + pl (2 * X 0 0) (X 0 2))) + (((ph (2 * X 0 3) (X 0 4) + ph (2 * X 0 2) (X 0 5)) + (pl (X 0 4) (X 0 4) + pl (2 * X 0 3) (X 0 5))) * 128)) + (((ph (2 * X 0 3) (X 0 4) + ph (2 * X 0 2) (X 0 5)) + (pl (X 0 4) (X 0 4) + pl (2 * X 0 3) (X 0 5))) * 24), (((0) + (pl (X 1 1) (X 1 1) + pl (2 * X 1 0) (X 1 2))) + (((ph (2 * X 1 3) (X 1 4) + ph (2 * X 1 2) (X 1 5)) + (pl (X 1 4) (X 1 4) + pl (2 * X 1 3) (X 1 5))) * 128)) + (((ph (2 * X 1 3) (X 1 4) + ph (2 * X 1 2) (X 1 5)) + (pl (X 1 4) (X 1 4) + pl (2 * X 1 3) (X 1 5))) * 24), (((0) + (pl (X 2 1) (X 2 1) + pl (2 * X 2 0) (X 2 2))) + (((ph (2 * X 2 3) (X 2 4) + ph (2 * X 2 2) (X 2 5)) + (pl (X 2 4) (X 2 4) + pl (2 * X 2 3) (X 2 5))) * 128)) + (((ph (2 * X 2 3) (X 2 4) + ph (2 * X 2 2) (X 2 5)) + (pl (X 2 4) (X 2 4) + pl (2 * X 2 3) (X 2 5))) * 24), (((0) + (pl (X 3 1) (X 3 1) + pl (2 * X 3 0) (X 3 2))) + (((ph (2 * X 3 3) (X 3 4) + ph (2 * X 3 2) (X 3 5)) + (pl (X 3 4) (X 3 4) + pl (2 * X 3 3) (X 3 5))) * 128)) + (((ph (2 * X 3 3) (X 3 4) + ph (2 * X 3 2) (X 3 5)) + (pl (X 3 4) (X 3 4) + pl (2 * X 3 3) (X 3 5))) * 24), (((pl (2 * X 0 3) (X 0 2) + pl (2 * X 0 4) 0) + (pl (2 * X 0 0) (X 0 5) + pl (2 * X 0 1) (X 0 4))) + (((ph (X 0 5) (X 0 5)) + (0)) * 128)) + (((ph (X 0 5) (X 0 5)) + (0)) * 24), (((pl (2 * X 1 3) (X 1 2) + pl (2 * X 1 4) 0) + (pl (2 * X 1 0) (X 1 5) + pl (2 * X 1 1) (X 1 4))) + (((ph (X 1 5) (X 1 5)) + (0)) * 128)) + (((ph (X 1 5) (X 1 5)) + (0)) * 24), (((pl (2 * X 2 3) (X 2 2) + pl (2 * X 2 4) 0) + (pl (2 * X 2 0) (X 2 5) + pl (2 * X 2 1) (X 2 4))) + (((ph (X 2 5) (X 2 5)) + (0)) * 128)) + (((ph (X 2 5) (X 2 5)) + (0)) * 24), (((pl (2 * X 3 3) (X 3 2) + pl (2 * X 3 4) 0) + (pl (2 * X 3 0) (X 3 5) + pl (2 * X 3 1) (X 3 4))) + (((ph (X 3 5) (X 3 5)) + (0)) * 128)) + (((ph (X 3 5) (X 3 5)) + (0)) * 24)]
  have hza25_c : v113 = za25_c := by quad_vecbin hv113 with quadValMem, za25_b, za25_c, zb25_mul24
  subst hza25_c
  denote_clear v 113 113
  denote_step_all v 114
  -- z25: limbs 2 and 5
  let z25 := toBitVecValue 64 #v[((((0) + (pl (X 0 1) (X 0 1) + pl (2 * X 0 0) (X 0 2))) + (((ph (2 * X 0 3) (X 0 4) + ph (2 * X 0 2) (X 0 5)) + (pl (X 0 4) (X 0 4) + pl (2 * X 0 3) (X 0 5))) * 128)) + (((ph (2 * X 0 3) (X 0 4) + ph (2 * X 0 2) (X 0 5)) + (pl (X 0 4) (X 0 4) + pl (2 * X 0 3) (X 0 5))) * 24)) + (ph (2 * X 0 0) (X 0 1)), ((((0) + (pl (X 1 1) (X 1 1) + pl (2 * X 1 0) (X 1 2))) + (((ph (2 * X 1 3) (X 1 4) + ph (2 * X 1 2) (X 1 5)) + (pl (X 1 4) (X 1 4) + pl (2 * X 1 3) (X 1 5))) * 128)) + (((ph (2 * X 1 3) (X 1 4) + ph (2 * X 1 2) (X 1 5)) + (pl (X 1 4) (X 1 4) + pl (2 * X 1 3) (X 1 5))) * 24)) + (ph (2 * X 1 0) (X 1 1)), ((((0) + (pl (X 2 1) (X 2 1) + pl (2 * X 2 0) (X 2 2))) + (((ph (2 * X 2 3) (X 2 4) + ph (2 * X 2 2) (X 2 5)) + (pl (X 2 4) (X 2 4) + pl (2 * X 2 3) (X 2 5))) * 128)) + (((ph (2 * X 2 3) (X 2 4) + ph (2 * X 2 2) (X 2 5)) + (pl (X 2 4) (X 2 4) + pl (2 * X 2 3) (X 2 5))) * 24)) + (ph (2 * X 2 0) (X 2 1)), ((((0) + (pl (X 3 1) (X 3 1) + pl (2 * X 3 0) (X 3 2))) + (((ph (2 * X 3 3) (X 3 4) + ph (2 * X 3 2) (X 3 5)) + (pl (X 3 4) (X 3 4) + pl (2 * X 3 3) (X 3 5))) * 128)) + (((ph (2 * X 3 3) (X 3 4) + ph (2 * X 3 2) (X 3 5)) + (pl (X 3 4) (X 3 4) + pl (2 * X 3 3) (X 3 5))) * 24)) + (ph (2 * X 3 0) (X 3 1)), ((((pl (2 * X 0 3) (X 0 2) + pl (2 * X 0 4) 0) + (pl (2 * X 0 0) (X 0 5) + pl (2 * X 0 1) (X 0 4))) + (((ph (X 0 5) (X 0 5)) + (0)) * 128)) + (((ph (X 0 5) (X 0 5)) + (0)) * 24)) + (ph (X 0 2) (X 0 2) + ph (2 * X 0 0) (X 0 4) + ph (2 * X 0 1) (X 0 3)), ((((pl (2 * X 1 3) (X 1 2) + pl (2 * X 1 4) 0) + (pl (2 * X 1 0) (X 1 5) + pl (2 * X 1 1) (X 1 4))) + (((ph (X 1 5) (X 1 5)) + (0)) * 128)) + (((ph (X 1 5) (X 1 5)) + (0)) * 24)) + (ph (X 1 2) (X 1 2) + ph (2 * X 1 0) (X 1 4) + ph (2 * X 1 1) (X 1 3)), ((((pl (2 * X 2 3) (X 2 2) + pl (2 * X 2 4) 0) + (pl (2 * X 2 0) (X 2 5) + pl (2 * X 2 1) (X 2 4))) + (((ph (X 2 5) (X 2 5)) + (0)) * 128)) + (((ph (X 2 5) (X 2 5)) + (0)) * 24)) + (ph (X 2 2) (X 2 2) + ph (2 * X 2 0) (X 2 4) + ph (2 * X 2 1) (X 2 3)), ((((pl (2 * X 3 3) (X 3 2) + pl (2 * X 3 4) 0) + (pl (2 * X 3 0) (X 3 5) + pl (2 * X 3 1) (X 3 4))) + (((ph (X 3 5) (X 3 5)) + (0)) * 128)) + (((ph (X 3 5) (X 3 5)) + (0)) * 24)) + (ph (X 3 2) (X 3 2) + ph (2 * X 3 0) (X 3 4) + ph (2 * X 3 1) (X 3 3))]
  have hz25 : v114 = z25 := by quad_vecbin hv114 with quadValMem, z25, za25_c, za25_q
  subst hz25
  denote_clear v 114 114

  -- the three stores. `denote_step_all` stops at %114: a store has an
  -- impure operation, so there is nothing left to push into the
  -- valuation. What remains is to identify the three stored values with
  -- the specification, which is the `lane_*` lemmas above, and then to
  -- read the stores off the denotation.
  have ez03 : z03 = (quadSqrResult x).v03.map PoisonOr.value := by
    apply Vector.ext
    intro i hi
    interval_cases i
    all_goals simp only [quadSqrResult, quadVec, toBitVecValue,
      z03, X, quadLimb, vlane, Fin.reduceCastAdd, Fin.reduceAddNat,
      Vector.getElem_map, Vector.getElem_mk, List.getElem_toArray,
      List.getElem_cons_zero, List.getElem_cons_succ,
      lane_0, lane_1, lane_2, lane_3, lane_4, lane_5, lane_6, lane_7]
  have ez14 : z14 = (quadSqrResult x).v14.map PoisonOr.value := by
    apply Vector.ext
    intro i hi
    interval_cases i
    all_goals simp only [quadSqrResult, quadVec, toBitVecValue,
      z14, X, quadLimb, vlane, Fin.reduceCastAdd, Fin.reduceAddNat,
      Vector.getElem_map, Vector.getElem_mk, List.getElem_toArray,
      List.getElem_cons_zero, List.getElem_cons_succ,
      lane_8, lane_9, lane_10, lane_11, lane_12, lane_13, lane_14, lane_15]
  have ez25 : z25 = (quadSqrResult x).v25.map PoisonOr.value := by
    apply Vector.ext
    intro i hi
    interval_cases i
    all_goals simp only [quadSqrResult, quadVec, toBitVecValue,
      z25, X, quadLimb, vlane, Fin.reduceCastAdd, Fin.reduceAddNat,
      Vector.getElem_map, Vector.getElem_mk, List.getElem_toArray,
      List.getElem_cons_zero, List.getElem_cons_succ,
      lane_16, lane_17, lane_18, lane_19, lane_20, lane_21, lane_22, lane_23]
  simp only [Com.denote_var, Expr.denote_unfold, Expr.denoteOp,
    EffectKind.liftEffect_rfl, simp_denote, storeVec, quadValMem,
    Function.comp_def, Ctxt.Valuation.nil_append, map_eq_pure_bind,
    bind_assoc, pure_bind, Ctxt.Valuation.cons_last, ez03, ez14, ez25]

/-! ## What the kernel writes

The derivation above says the region *is* three whole-vector stores. Combining
it with `Proof/Mem.lean` turns that into a statement about memory. Everything
about the *values* -- ring correctness and the width table -- follows below,
on the three vectors the kernel writes. -/

/-- **The kernel's effect on memory.** Given three live, big-enough
destinations, the region runs without UB and leaves exactly the three
specified vectors behind. No aliasing hypothesis is needed: if two
destinations coincide the later write wins, which is what the nested
`writeVec`s say. -/
theorem run_fd_r43x6_quad_sqr_fast (x : Quad)
    (hx03 : R43x6.U47 x.v03) (hx14 : R43x6.U47 x.v14) (hx25 : R43x6.U47 x.v25)
    (p₀ p₁ p₂ : Pointer) (s : GlobalState)
    (h₀ : Fits s.mem p₀ 512)
    (h₁ : Fits (s.mem.writeVec p₀ (quadSqrResult x).v03) p₁ 512)
    (h₂ : Fits ((s.mem.writeVec p₀ (quadSqrResult x).v03).writeVec p₁
      (quadSqrResult x).v14) p₂ 512) :
    (fd_r43x6_quad_sqr_fast.denote
        (quadValMem (.value p₀) (.value p₁) (.value p₂) x)).run s
      = .value (HVector.nil,
          { s with mem := ((s.mem.writeVec p₀ (quadSqrResult x).v03).writeVec p₁
              (quadSqrResult x).v14).writeVec p₂ (quadSqrResult x).v25 }) := by
  rw [denote_fd_r43x6_quad_sqr_fast x hx03 hx14 hx25]
  exact run_storeVec3 h₀ h₁ h₂

/-- **Correctness, against memory.** Given three live, big-enough and pairwise
distinct destinations, the region runs without UB and each pointer afterwards
addresses the vector the specification predicts for it.

The distinctness hypotheses are an assumption about the *caller*: the kernel's
pointer parameters carry `nocapture noundef writeonly` and not `noalias`, so
nothing in the IR rules out aliasing. At the one call site,
`FD_R43X6_QUAD_SQR_FAST` passes `&_R03, &_R14, &_R25` -- three distinct
locals. -/
theorem fd_r43x6_quad_sqr_fast_readback (x : Quad)
    (hx03 : R43x6.U47 x.v03) (hx14 : R43x6.U47 x.v14) (hx25 : R43x6.U47 x.v25)
    (p₀ p₁ p₂ : Pointer) (s : GlobalState)
    (h₀ : Fits s.mem p₀ 512) (h₁ : Fits s.mem p₁ 512) (h₂ : Fits s.mem p₂ 512)
    (d₀₁ : p₀.id ≠ p₁.id) (d₀₂ : p₀.id ≠ p₂.id) (d₁₂ : p₁.id ≠ p₂.id) :
    let m' := ((s.mem.writeVec p₀ (quadSqrResult x).v03).writeVec p₁
      (quadSqrResult x).v14).writeVec p₂ (quadSqrResult x).v25
    (fd_r43x6_quad_sqr_fast.denote
          (quadValMem (.value p₀) (.value p₁) (.value p₂) x)).run s
        = .value (HVector.nil, { s with mem := m' })
      ∧ (SLLVM.load (.value p₀) QVecTy).run m'
          = .value ((quadSqrResult x).v03.map PoisonOr.value, m')
      ∧ (SLLVM.load (.value p₁) QVecTy).run m'
          = .value ((quadSqrResult x).v14.map PoisonOr.value, m')
      ∧ (SLLVM.load (.value p₂) QVecTy).run m'
          = .value ((quadSqrResult x).v25.map PoisonOr.value, m') := by
  refine ⟨run_fd_r43x6_quad_sqr_fast x hx03 hx14 hx25 p₀ p₁ p₂ s h₀
      (fits_splice h₁) (fits_splice (fits_splice h₂)), ?_⟩
  exact storeVec3_readback h₀ h₁ h₂ d₀₁ d₀₂ d₁₂

/-! ## What the kernel computes

The QUAD the kernel writes is `quadSqrResult x`. What follows is about that
and is independent of how it reaches memory: the ring correctness and the
width table of `Spec/fd_r43x6_quad_sqr_fast.lean`, transported onto the
kernel's three outputs. Everything is stated per QUAD lane `j : Fin 4`, since
the kernel is four independent squarings. -/

/-- Reading element `j` back out of the result QUAD recovers the specified
limbs. -/
theorem quadSqr_limbs (x : Quad)
    (hx03 : R43x6.U47 x.v03) (hx14 : R43x6.U47 x.v14) (hx25 : R43x6.U47 x.v25)
    (j : Fin 4) (k : Fin 6) :
    quadLimb (quadSqrResult x).v03 (quadSqrResult x).v14 (quadSqrResult x).v25 j k
      = quadSqrLimb x j k :=
  quadLimb_quadVec (quadSqrLimb x) j k (fun i k' => by
    have := quadSqrLimb_lt_two_pow_63 x hx03 hx14 hx25 i k'
    omega)

/-- **Correctness.** In each of the four QUAD lanes, the limbs the kernel
produces decode to the square of the decoded input in `GF(2^255 - 19)`. -/
theorem quadSqr_zmod (x : Quad) (j : Fin 4) :
    ((decodeNat (quadSqrLimb x j) : ℕ) : ZMod p)
      = ((decodeNat (laneFunc (x.vector j)) : ℕ) : ZMod p) ^ 2 :=
  decodeLimbs_quadSqrLimb_zmod x j

/-! ## Output bounds

The `fd_r43x6.h` width table, on each of the three vectors the kernel writes. -/

private theorem quadSqr_bounds_of (x : Quad) (N : ℕ) (hN : N ≤ 2 ^ 63)
    (hb : ∀ (j : Fin 4) (k : Fin 6), quadSqrLimb x j k < N) :
    (R43x6.BoundedUpper ((N : Int) - 1) (quadSqrResult x).v03
      ∧ R43x6.BoundedLower 0 (quadSqrResult x).v03)
    ∧ (R43x6.BoundedUpper ((N : Int) - 1) (quadSqrResult x).v14
      ∧ R43x6.BoundedLower 0 (quadSqrResult x).v14)
    ∧ (R43x6.BoundedUpper ((N : Int) - 1) (quadSqrResult x).v25
      ∧ R43x6.BoundedLower 0 (quadSqrResult x).v25) :=
  ⟨quadVec_bounds _ 0 3 N hN (fun j => ⟨hb j 0, hb j 3⟩),
   quadVec_bounds _ 1 4 N hN (fun j => ⟨hb j 1, hb j 4⟩),
   quadVec_bounds _ 2 5 N hN (fun j => ⟨hb j 2, hb j 5⟩)⟩

/-- **`u47` in, `u62` out**, on every vector the kernel writes. -/
theorem quadSqr_u47_u62 (x : Quad)
    (hx03 : R43x6.U47 x.v03) (hx14 : R43x6.U47 x.v14) (hx25 : R43x6.U47 x.v25)
    :
    R43x6.U62 (quadSqrResult x).v03 ∧ R43x6.U62 (quadSqrResult x).v14
      ∧ R43x6.U62 (quadSqrResult x).v25 := by
  have := quadSqr_bounds_of x (2 ^ 62) (by omega)
    (fun j k => quadSqrLimb_lt_u47 x hx03 hx14 hx25 j k)
  exact_mod_cast this

/-- **`u44` in, `u61` out**, on every vector the kernel writes. -/
theorem quadSqr_u44_u61 (x : Quad)
    (hx03 : R43x6.U44 x.v03) (hx14 : R43x6.U44 x.v14) (hx25 : R43x6.U44 x.v25)
    :
    R43x6.U61 (quadSqrResult x).v03 ∧ R43x6.U61 (quadSqrResult x).v14
      ∧ R43x6.U61 (quadSqrResult x).v25 := by
  have := quadSqr_bounds_of x (2 ^ 61) (by omega)
    (fun j k => quadSqrLimb_lt_u44 x hx03 hx14 hx25 j k)
  exact_mod_cast this

end Firedancer.Avx512
