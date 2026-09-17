/-
Released under Apache 2.0 license as described in the file LICENSE.
NOTE: the bulk of this file was machine-generated; the structure mirrors
the data flow of `fd_r43x6_quad_mul_fast`.
-/
module

public import SSA.Projects.Firedancer.Avx512.Mlir.Field.fd_r43x6_quad_mul_fast
public import SSA.Projects.Firedancer.Avx512.Proof.Mem
public import SSA.Projects.Firedancer.Avx512.Spec.Field.fd_r43x6_quad_mul_fast

/-!
# `fd_r43x6_quad_mul_fast` multiplies four field elements at once

This is the kernel lifted **verbatim** -- three `!llvm.ptr` out-parameters and
three `llvm.store`s, with no extraction probe. The derivation shows the region
denotes to exactly three whole-vector stores of the specified results;
`Proof/Mem.lean` turns that into a statement about memory.

The derivation runs at the N level throughout: each of the 92 instructions is
reduced to a vector of `BitVec.ofNat 64` applied to an expression over `pl`
and `ph` (`Spec/Common.lean`), so it lands directly on `quadMulResult`. Every
intermediate is introduced as a `let` at the point the program computes it,
under the name `fd_r43x6_inl.h` gives it, so the derivation reads against the C
line by line. Where LLVM split one C assignment across several instructions the
parts carry a suffix: `_lo`/`_hi` for the two `madd52` chains, `_hiRaw` for a
hi accumulator before the `wwl_shl( ..., 9 )` that scales it, and a digit for a
step of a chain.

Each step names in its `with` list exactly the values it reads; `simp only`
zeta-delta-unfolds those and leaves the rest folded, which is what keeps a
step's simp set small.

## Hypotheses

`R43x6.U47` on all six input vectors. There are no zero-lane hypotheses: a
QUAD has no ignored lanes, so every product the kernel forms stays inside one
lane and the four multiplications never mix (see `Spec/Quad.lean`).
-/

@[expose] public section

namespace Firedancer.Avx512
open LeanMLIR SLLVM
open InstCombine (LLVM)

/-! ## The result lanes, against the specification

One lemma per lane of the result, in the vocabulary the derivation
leaves behind: its `let`s are zeta-unfolded down to lanes, while the
specification still reads `quadMulLimb … j`. Proving these separately
keeps the last step of the derivation a rewrite rather than a
twenty-four-fold re-normalisation of the whole result. -/

private theorem lane_0 (x y : Quad) :
    (((((ph (x.v25[4].toNat) (y.v03[0].toNat) + ph (x.v14[4].toNat) (y.v14[0].toNat) + ph (x.v03[4].toNat) (y.v25[0].toNat)) + (pl (x.v25[4].toNat) (y.v14[0].toNat) + pl (x.v14[4].toNat) (y.v25[0].toNat))) + ((ph (x.v25[0].toNat) (y.v03[4].toNat) + ph (x.v14[0].toNat) (y.v14[4].toNat) + ph (x.v03[0].toNat) (y.v25[4].toNat)) + (pl (x.v03[4].toNat) (y.v03[4].toNat) + pl (x.v25[0].toNat) (y.v14[4].toNat) + pl (x.v14[0].toNat) (y.v25[4].toNat)))) * 128) + (pl (x.v03[0].toNat) (y.v03[0].toNat))) + ((((ph (x.v25[4].toNat) (y.v03[0].toNat) + ph (x.v14[4].toNat) (y.v14[0].toNat) + ph (x.v03[4].toNat) (y.v25[0].toNat)) + (pl (x.v25[4].toNat) (y.v14[0].toNat) + pl (x.v14[4].toNat) (y.v25[0].toNat))) + ((ph (x.v25[0].toNat) (y.v03[4].toNat) + ph (x.v14[0].toNat) (y.v14[4].toNat) + ph (x.v03[0].toNat) (y.v25[4].toNat)) + (pl (x.v03[4].toNat) (y.v03[4].toNat) + pl (x.v25[0].toNat) (y.v14[4].toNat) + pl (x.v14[0].toNat) (y.v25[4].toNat)))) * 24)
      = quadMulLimb x y 0 0 := by
  simp only [quadMulLimb, limb, col, quadLimb, vlane, Fin.reduceCastAdd, Fin.reduceAddNat]
  ring

private theorem lane_1 (x y : Quad) :
    (((((ph (x.v25[5].toNat) (y.v03[1].toNat) + ph (x.v14[5].toNat) (y.v14[1].toNat) + ph (x.v03[5].toNat) (y.v25[1].toNat)) + (pl (x.v25[5].toNat) (y.v14[1].toNat) + pl (x.v14[5].toNat) (y.v25[1].toNat))) + ((ph (x.v25[1].toNat) (y.v03[5].toNat) + ph (x.v14[1].toNat) (y.v14[5].toNat) + ph (x.v03[1].toNat) (y.v25[5].toNat)) + (pl (x.v03[5].toNat) (y.v03[5].toNat) + pl (x.v25[1].toNat) (y.v14[5].toNat) + pl (x.v14[1].toNat) (y.v25[5].toNat)))) * 128) + (pl (x.v03[1].toNat) (y.v03[1].toNat))) + ((((ph (x.v25[5].toNat) (y.v03[1].toNat) + ph (x.v14[5].toNat) (y.v14[1].toNat) + ph (x.v03[5].toNat) (y.v25[1].toNat)) + (pl (x.v25[5].toNat) (y.v14[1].toNat) + pl (x.v14[5].toNat) (y.v25[1].toNat))) + ((ph (x.v25[1].toNat) (y.v03[5].toNat) + ph (x.v14[1].toNat) (y.v14[5].toNat) + ph (x.v03[1].toNat) (y.v25[5].toNat)) + (pl (x.v03[5].toNat) (y.v03[5].toNat) + pl (x.v25[1].toNat) (y.v14[5].toNat) + pl (x.v14[1].toNat) (y.v25[5].toNat)))) * 24)
      = quadMulLimb x y 1 0 := by
  simp only [quadMulLimb, limb, col, quadLimb, vlane, Fin.reduceCastAdd, Fin.reduceAddNat]
  ring

private theorem lane_2 (x y : Quad) :
    (((((ph (x.v25[6].toNat) (y.v03[2].toNat) + ph (x.v14[6].toNat) (y.v14[2].toNat) + ph (x.v03[6].toNat) (y.v25[2].toNat)) + (pl (x.v25[6].toNat) (y.v14[2].toNat) + pl (x.v14[6].toNat) (y.v25[2].toNat))) + ((ph (x.v25[2].toNat) (y.v03[6].toNat) + ph (x.v14[2].toNat) (y.v14[6].toNat) + ph (x.v03[2].toNat) (y.v25[6].toNat)) + (pl (x.v03[6].toNat) (y.v03[6].toNat) + pl (x.v25[2].toNat) (y.v14[6].toNat) + pl (x.v14[2].toNat) (y.v25[6].toNat)))) * 128) + (pl (x.v03[2].toNat) (y.v03[2].toNat))) + ((((ph (x.v25[6].toNat) (y.v03[2].toNat) + ph (x.v14[6].toNat) (y.v14[2].toNat) + ph (x.v03[6].toNat) (y.v25[2].toNat)) + (pl (x.v25[6].toNat) (y.v14[2].toNat) + pl (x.v14[6].toNat) (y.v25[2].toNat))) + ((ph (x.v25[2].toNat) (y.v03[6].toNat) + ph (x.v14[2].toNat) (y.v14[6].toNat) + ph (x.v03[2].toNat) (y.v25[6].toNat)) + (pl (x.v03[6].toNat) (y.v03[6].toNat) + pl (x.v25[2].toNat) (y.v14[6].toNat) + pl (x.v14[2].toNat) (y.v25[6].toNat)))) * 24)
      = quadMulLimb x y 2 0 := by
  simp only [quadMulLimb, limb, col, quadLimb, vlane, Fin.reduceCastAdd, Fin.reduceAddNat]
  ring

private theorem lane_3 (x y : Quad) :
    (((((ph (x.v25[7].toNat) (y.v03[3].toNat) + ph (x.v14[7].toNat) (y.v14[3].toNat) + ph (x.v03[7].toNat) (y.v25[3].toNat)) + (pl (x.v25[7].toNat) (y.v14[3].toNat) + pl (x.v14[7].toNat) (y.v25[3].toNat))) + ((ph (x.v25[3].toNat) (y.v03[7].toNat) + ph (x.v14[3].toNat) (y.v14[7].toNat) + ph (x.v03[3].toNat) (y.v25[7].toNat)) + (pl (x.v03[7].toNat) (y.v03[7].toNat) + pl (x.v25[3].toNat) (y.v14[7].toNat) + pl (x.v14[3].toNat) (y.v25[7].toNat)))) * 128) + (pl (x.v03[3].toNat) (y.v03[3].toNat))) + ((((ph (x.v25[7].toNat) (y.v03[3].toNat) + ph (x.v14[7].toNat) (y.v14[3].toNat) + ph (x.v03[7].toNat) (y.v25[3].toNat)) + (pl (x.v25[7].toNat) (y.v14[3].toNat) + pl (x.v14[7].toNat) (y.v25[3].toNat))) + ((ph (x.v25[3].toNat) (y.v03[7].toNat) + ph (x.v14[3].toNat) (y.v14[7].toNat) + ph (x.v03[3].toNat) (y.v25[7].toNat)) + (pl (x.v03[7].toNat) (y.v03[7].toNat) + pl (x.v25[3].toNat) (y.v14[7].toNat) + pl (x.v14[3].toNat) (y.v25[7].toNat)))) * 24)
      = quadMulLimb x y 3 0 := by
  simp only [quadMulLimb, limb, col, quadLimb, vlane, Fin.reduceCastAdd, Fin.reduceAddNat]
  ring

private theorem lane_4 (x y : Quad) :
    ((((ph (x.v25[4].toNat) (y.v03[4].toNat) + ph (x.v14[4].toNat) (y.v14[4].toNat) + ph (x.v03[4].toNat) (y.v25[4].toNat)) + (pl (x.v25[4].toNat) (y.v14[4].toNat) + pl (x.v14[4].toNat) (y.v25[4].toNat))) * 128) + (((ph (x.v25[0].toNat) (y.v03[0].toNat) + ph (x.v14[0].toNat) (y.v14[0].toNat) + ph (x.v03[0].toNat) (y.v25[0].toNat)) + (pl (x.v03[4].toNat) (y.v03[0].toNat) + pl (x.v25[0].toNat) (y.v14[0].toNat) + pl (x.v14[0].toNat) (y.v25[0].toNat))) + (pl (x.v03[0].toNat) (y.v03[4].toNat)))) + (((ph (x.v25[4].toNat) (y.v03[4].toNat) + ph (x.v14[4].toNat) (y.v14[4].toNat) + ph (x.v03[4].toNat) (y.v25[4].toNat)) + (pl (x.v25[4].toNat) (y.v14[4].toNat) + pl (x.v14[4].toNat) (y.v25[4].toNat))) * 24)
      = quadMulLimb x y 0 3 := by
  simp only [quadMulLimb, limb, col, quadLimb, vlane, Fin.reduceCastAdd, Fin.reduceAddNat]
  ring

private theorem lane_5 (x y : Quad) :
    ((((ph (x.v25[5].toNat) (y.v03[5].toNat) + ph (x.v14[5].toNat) (y.v14[5].toNat) + ph (x.v03[5].toNat) (y.v25[5].toNat)) + (pl (x.v25[5].toNat) (y.v14[5].toNat) + pl (x.v14[5].toNat) (y.v25[5].toNat))) * 128) + (((ph (x.v25[1].toNat) (y.v03[1].toNat) + ph (x.v14[1].toNat) (y.v14[1].toNat) + ph (x.v03[1].toNat) (y.v25[1].toNat)) + (pl (x.v03[5].toNat) (y.v03[1].toNat) + pl (x.v25[1].toNat) (y.v14[1].toNat) + pl (x.v14[1].toNat) (y.v25[1].toNat))) + (pl (x.v03[1].toNat) (y.v03[5].toNat)))) + (((ph (x.v25[5].toNat) (y.v03[5].toNat) + ph (x.v14[5].toNat) (y.v14[5].toNat) + ph (x.v03[5].toNat) (y.v25[5].toNat)) + (pl (x.v25[5].toNat) (y.v14[5].toNat) + pl (x.v14[5].toNat) (y.v25[5].toNat))) * 24)
      = quadMulLimb x y 1 3 := by
  simp only [quadMulLimb, limb, col, quadLimb, vlane, Fin.reduceCastAdd, Fin.reduceAddNat]
  ring

private theorem lane_6 (x y : Quad) :
    ((((ph (x.v25[6].toNat) (y.v03[6].toNat) + ph (x.v14[6].toNat) (y.v14[6].toNat) + ph (x.v03[6].toNat) (y.v25[6].toNat)) + (pl (x.v25[6].toNat) (y.v14[6].toNat) + pl (x.v14[6].toNat) (y.v25[6].toNat))) * 128) + (((ph (x.v25[2].toNat) (y.v03[2].toNat) + ph (x.v14[2].toNat) (y.v14[2].toNat) + ph (x.v03[2].toNat) (y.v25[2].toNat)) + (pl (x.v03[6].toNat) (y.v03[2].toNat) + pl (x.v25[2].toNat) (y.v14[2].toNat) + pl (x.v14[2].toNat) (y.v25[2].toNat))) + (pl (x.v03[2].toNat) (y.v03[6].toNat)))) + (((ph (x.v25[6].toNat) (y.v03[6].toNat) + ph (x.v14[6].toNat) (y.v14[6].toNat) + ph (x.v03[6].toNat) (y.v25[6].toNat)) + (pl (x.v25[6].toNat) (y.v14[6].toNat) + pl (x.v14[6].toNat) (y.v25[6].toNat))) * 24)
      = quadMulLimb x y 2 3 := by
  simp only [quadMulLimb, limb, col, quadLimb, vlane, Fin.reduceCastAdd, Fin.reduceAddNat]
  ring

private theorem lane_7 (x y : Quad) :
    ((((ph (x.v25[7].toNat) (y.v03[7].toNat) + ph (x.v14[7].toNat) (y.v14[7].toNat) + ph (x.v03[7].toNat) (y.v25[7].toNat)) + (pl (x.v25[7].toNat) (y.v14[7].toNat) + pl (x.v14[7].toNat) (y.v25[7].toNat))) * 128) + (((ph (x.v25[3].toNat) (y.v03[3].toNat) + ph (x.v14[3].toNat) (y.v14[3].toNat) + ph (x.v03[3].toNat) (y.v25[3].toNat)) + (pl (x.v03[7].toNat) (y.v03[3].toNat) + pl (x.v25[3].toNat) (y.v14[3].toNat) + pl (x.v14[3].toNat) (y.v25[3].toNat))) + (pl (x.v03[3].toNat) (y.v03[7].toNat)))) + (((ph (x.v25[7].toNat) (y.v03[7].toNat) + ph (x.v14[7].toNat) (y.v14[7].toNat) + ph (x.v03[7].toNat) (y.v25[7].toNat)) + (pl (x.v25[7].toNat) (y.v14[7].toNat) + pl (x.v14[7].toNat) (y.v25[7].toNat))) * 24)
      = quadMulLimb x y 3 3 := by
  simp only [quadMulLimb, limb, col, quadLimb, vlane, Fin.reduceCastAdd, Fin.reduceAddNat]
  ring

private theorem lane_8 (x y : Quad) :
    (((((ph (x.v25[4].toNat) (y.v14[0].toNat) + ph (x.v14[4].toNat) (y.v25[0].toNat)) + (pl (x.v25[4].toNat) (y.v25[0].toNat))) + ((ph (x.v03[4].toNat) (y.v03[4].toNat) + ph (x.v25[0].toNat) (y.v14[4].toNat) + ph (x.v14[0].toNat) (y.v25[4].toNat)) + (pl (x.v14[4].toNat) (y.v03[4].toNat) + pl (x.v03[4].toNat) (y.v14[4].toNat) + pl (x.v25[0].toNat) (y.v25[4].toNat)))) * 128) + ((ph (x.v03[0].toNat) (y.v03[0].toNat)) + (pl (x.v14[0].toNat) (y.v03[0].toNat) + pl (x.v03[0].toNat) (y.v14[0].toNat)))) + ((((ph (x.v25[4].toNat) (y.v14[0].toNat) + ph (x.v14[4].toNat) (y.v25[0].toNat)) + (pl (x.v25[4].toNat) (y.v25[0].toNat))) + ((ph (x.v03[4].toNat) (y.v03[4].toNat) + ph (x.v25[0].toNat) (y.v14[4].toNat) + ph (x.v14[0].toNat) (y.v25[4].toNat)) + (pl (x.v14[4].toNat) (y.v03[4].toNat) + pl (x.v03[4].toNat) (y.v14[4].toNat) + pl (x.v25[0].toNat) (y.v25[4].toNat)))) * 24)
      = quadMulLimb x y 0 1 := by
  simp only [quadMulLimb, limb, col, quadLimb, vlane, Fin.reduceCastAdd, Fin.reduceAddNat]
  ring

private theorem lane_9 (x y : Quad) :
    (((((ph (x.v25[5].toNat) (y.v14[1].toNat) + ph (x.v14[5].toNat) (y.v25[1].toNat)) + (pl (x.v25[5].toNat) (y.v25[1].toNat))) + ((ph (x.v03[5].toNat) (y.v03[5].toNat) + ph (x.v25[1].toNat) (y.v14[5].toNat) + ph (x.v14[1].toNat) (y.v25[5].toNat)) + (pl (x.v14[5].toNat) (y.v03[5].toNat) + pl (x.v03[5].toNat) (y.v14[5].toNat) + pl (x.v25[1].toNat) (y.v25[5].toNat)))) * 128) + ((ph (x.v03[1].toNat) (y.v03[1].toNat)) + (pl (x.v14[1].toNat) (y.v03[1].toNat) + pl (x.v03[1].toNat) (y.v14[1].toNat)))) + ((((ph (x.v25[5].toNat) (y.v14[1].toNat) + ph (x.v14[5].toNat) (y.v25[1].toNat)) + (pl (x.v25[5].toNat) (y.v25[1].toNat))) + ((ph (x.v03[5].toNat) (y.v03[5].toNat) + ph (x.v25[1].toNat) (y.v14[5].toNat) + ph (x.v14[1].toNat) (y.v25[5].toNat)) + (pl (x.v14[5].toNat) (y.v03[5].toNat) + pl (x.v03[5].toNat) (y.v14[5].toNat) + pl (x.v25[1].toNat) (y.v25[5].toNat)))) * 24)
      = quadMulLimb x y 1 1 := by
  simp only [quadMulLimb, limb, col, quadLimb, vlane, Fin.reduceCastAdd, Fin.reduceAddNat]
  ring

private theorem lane_10 (x y : Quad) :
    (((((ph (x.v25[6].toNat) (y.v14[2].toNat) + ph (x.v14[6].toNat) (y.v25[2].toNat)) + (pl (x.v25[6].toNat) (y.v25[2].toNat))) + ((ph (x.v03[6].toNat) (y.v03[6].toNat) + ph (x.v25[2].toNat) (y.v14[6].toNat) + ph (x.v14[2].toNat) (y.v25[6].toNat)) + (pl (x.v14[6].toNat) (y.v03[6].toNat) + pl (x.v03[6].toNat) (y.v14[6].toNat) + pl (x.v25[2].toNat) (y.v25[6].toNat)))) * 128) + ((ph (x.v03[2].toNat) (y.v03[2].toNat)) + (pl (x.v14[2].toNat) (y.v03[2].toNat) + pl (x.v03[2].toNat) (y.v14[2].toNat)))) + ((((ph (x.v25[6].toNat) (y.v14[2].toNat) + ph (x.v14[6].toNat) (y.v25[2].toNat)) + (pl (x.v25[6].toNat) (y.v25[2].toNat))) + ((ph (x.v03[6].toNat) (y.v03[6].toNat) + ph (x.v25[2].toNat) (y.v14[6].toNat) + ph (x.v14[2].toNat) (y.v25[6].toNat)) + (pl (x.v14[6].toNat) (y.v03[6].toNat) + pl (x.v03[6].toNat) (y.v14[6].toNat) + pl (x.v25[2].toNat) (y.v25[6].toNat)))) * 24)
      = quadMulLimb x y 2 1 := by
  simp only [quadMulLimb, limb, col, quadLimb, vlane, Fin.reduceCastAdd, Fin.reduceAddNat]
  ring

private theorem lane_11 (x y : Quad) :
    (((((ph (x.v25[7].toNat) (y.v14[3].toNat) + ph (x.v14[7].toNat) (y.v25[3].toNat)) + (pl (x.v25[7].toNat) (y.v25[3].toNat))) + ((ph (x.v03[7].toNat) (y.v03[7].toNat) + ph (x.v25[3].toNat) (y.v14[7].toNat) + ph (x.v14[3].toNat) (y.v25[7].toNat)) + (pl (x.v14[7].toNat) (y.v03[7].toNat) + pl (x.v03[7].toNat) (y.v14[7].toNat) + pl (x.v25[3].toNat) (y.v25[7].toNat)))) * 128) + ((ph (x.v03[3].toNat) (y.v03[3].toNat)) + (pl (x.v14[3].toNat) (y.v03[3].toNat) + pl (x.v03[3].toNat) (y.v14[3].toNat)))) + ((((ph (x.v25[7].toNat) (y.v14[3].toNat) + ph (x.v14[7].toNat) (y.v25[3].toNat)) + (pl (x.v25[7].toNat) (y.v25[3].toNat))) + ((ph (x.v03[7].toNat) (y.v03[7].toNat) + ph (x.v25[3].toNat) (y.v14[7].toNat) + ph (x.v14[3].toNat) (y.v25[7].toNat)) + (pl (x.v14[7].toNat) (y.v03[7].toNat) + pl (x.v03[7].toNat) (y.v14[7].toNat) + pl (x.v25[3].toNat) (y.v25[7].toNat)))) * 24)
      = quadMulLimb x y 3 1 := by
  simp only [quadMulLimb, limb, col, quadLimb, vlane, Fin.reduceCastAdd, Fin.reduceAddNat]
  ring

private theorem lane_12 (x y : Quad) :
    ((((ph (x.v25[4].toNat) (y.v14[4].toNat) + ph (x.v14[4].toNat) (y.v25[4].toNat)) + (pl (x.v25[4].toNat) (y.v25[4].toNat))) * 128) + (((ph (x.v03[4].toNat) (y.v03[0].toNat) + ph (x.v25[0].toNat) (y.v14[0].toNat) + ph (x.v14[0].toNat) (y.v25[0].toNat)) + (pl (x.v14[4].toNat) (y.v03[0].toNat) + pl (x.v03[4].toNat) (y.v14[0].toNat) + pl (x.v25[0].toNat) (y.v25[0].toNat))) + ((ph (x.v03[0].toNat) (y.v03[4].toNat)) + (pl (x.v14[0].toNat) (y.v03[4].toNat) + pl (x.v03[0].toNat) (y.v14[4].toNat))))) + (((ph (x.v25[4].toNat) (y.v14[4].toNat) + ph (x.v14[4].toNat) (y.v25[4].toNat)) + (pl (x.v25[4].toNat) (y.v25[4].toNat))) * 24)
      = quadMulLimb x y 0 4 := by
  simp only [quadMulLimb, limb, col, quadLimb, vlane, Fin.reduceCastAdd, Fin.reduceAddNat]
  ring

private theorem lane_13 (x y : Quad) :
    ((((ph (x.v25[5].toNat) (y.v14[5].toNat) + ph (x.v14[5].toNat) (y.v25[5].toNat)) + (pl (x.v25[5].toNat) (y.v25[5].toNat))) * 128) + (((ph (x.v03[5].toNat) (y.v03[1].toNat) + ph (x.v25[1].toNat) (y.v14[1].toNat) + ph (x.v14[1].toNat) (y.v25[1].toNat)) + (pl (x.v14[5].toNat) (y.v03[1].toNat) + pl (x.v03[5].toNat) (y.v14[1].toNat) + pl (x.v25[1].toNat) (y.v25[1].toNat))) + ((ph (x.v03[1].toNat) (y.v03[5].toNat)) + (pl (x.v14[1].toNat) (y.v03[5].toNat) + pl (x.v03[1].toNat) (y.v14[5].toNat))))) + (((ph (x.v25[5].toNat) (y.v14[5].toNat) + ph (x.v14[5].toNat) (y.v25[5].toNat)) + (pl (x.v25[5].toNat) (y.v25[5].toNat))) * 24)
      = quadMulLimb x y 1 4 := by
  simp only [quadMulLimb, limb, col, quadLimb, vlane, Fin.reduceCastAdd, Fin.reduceAddNat]
  ring

private theorem lane_14 (x y : Quad) :
    ((((ph (x.v25[6].toNat) (y.v14[6].toNat) + ph (x.v14[6].toNat) (y.v25[6].toNat)) + (pl (x.v25[6].toNat) (y.v25[6].toNat))) * 128) + (((ph (x.v03[6].toNat) (y.v03[2].toNat) + ph (x.v25[2].toNat) (y.v14[2].toNat) + ph (x.v14[2].toNat) (y.v25[2].toNat)) + (pl (x.v14[6].toNat) (y.v03[2].toNat) + pl (x.v03[6].toNat) (y.v14[2].toNat) + pl (x.v25[2].toNat) (y.v25[2].toNat))) + ((ph (x.v03[2].toNat) (y.v03[6].toNat)) + (pl (x.v14[2].toNat) (y.v03[6].toNat) + pl (x.v03[2].toNat) (y.v14[6].toNat))))) + (((ph (x.v25[6].toNat) (y.v14[6].toNat) + ph (x.v14[6].toNat) (y.v25[6].toNat)) + (pl (x.v25[6].toNat) (y.v25[6].toNat))) * 24)
      = quadMulLimb x y 2 4 := by
  simp only [quadMulLimb, limb, col, quadLimb, vlane, Fin.reduceCastAdd, Fin.reduceAddNat]
  ring

private theorem lane_15 (x y : Quad) :
    ((((ph (x.v25[7].toNat) (y.v14[7].toNat) + ph (x.v14[7].toNat) (y.v25[7].toNat)) + (pl (x.v25[7].toNat) (y.v25[7].toNat))) * 128) + (((ph (x.v03[7].toNat) (y.v03[3].toNat) + ph (x.v25[3].toNat) (y.v14[3].toNat) + ph (x.v14[3].toNat) (y.v25[3].toNat)) + (pl (x.v14[7].toNat) (y.v03[3].toNat) + pl (x.v03[7].toNat) (y.v14[3].toNat) + pl (x.v25[3].toNat) (y.v25[3].toNat))) + ((ph (x.v03[3].toNat) (y.v03[7].toNat)) + (pl (x.v14[3].toNat) (y.v03[7].toNat) + pl (x.v03[3].toNat) (y.v14[7].toNat))))) + (((ph (x.v25[7].toNat) (y.v14[7].toNat) + ph (x.v14[7].toNat) (y.v25[7].toNat)) + (pl (x.v25[7].toNat) (y.v25[7].toNat))) * 24)
      = quadMulLimb x y 3 4 := by
  simp only [quadMulLimb, limb, col, quadLimb, vlane, Fin.reduceCastAdd, Fin.reduceAddNat]
  ring

private theorem lane_16 (x y : Quad) :
    ((((ph (x.v25[4].toNat) (y.v25[0].toNat)) + ((ph (x.v14[4].toNat) (y.v03[4].toNat) + ph (x.v03[4].toNat) (y.v14[4].toNat) + ph (x.v25[0].toNat) (y.v25[4].toNat)) + (pl (x.v25[4].toNat) (y.v03[4].toNat) + pl (x.v14[4].toNat) (y.v14[4].toNat) + pl (x.v03[4].toNat) (y.v25[4].toNat)))) * 128) + ((ph (x.v14[0].toNat) (y.v03[0].toNat) + ph (x.v03[0].toNat) (y.v14[0].toNat)) + (pl (x.v25[0].toNat) (y.v03[0].toNat) + pl (x.v14[0].toNat) (y.v14[0].toNat) + pl (x.v03[0].toNat) (y.v25[0].toNat)))) + (((ph (x.v25[4].toNat) (y.v25[0].toNat)) + ((ph (x.v14[4].toNat) (y.v03[4].toNat) + ph (x.v03[4].toNat) (y.v14[4].toNat) + ph (x.v25[0].toNat) (y.v25[4].toNat)) + (pl (x.v25[4].toNat) (y.v03[4].toNat) + pl (x.v14[4].toNat) (y.v14[4].toNat) + pl (x.v03[4].toNat) (y.v25[4].toNat)))) * 24)
      = quadMulLimb x y 0 2 := by
  simp only [quadMulLimb, limb, col, quadLimb, vlane, Fin.reduceCastAdd, Fin.reduceAddNat]
  ring

private theorem lane_17 (x y : Quad) :
    ((((ph (x.v25[5].toNat) (y.v25[1].toNat)) + ((ph (x.v14[5].toNat) (y.v03[5].toNat) + ph (x.v03[5].toNat) (y.v14[5].toNat) + ph (x.v25[1].toNat) (y.v25[5].toNat)) + (pl (x.v25[5].toNat) (y.v03[5].toNat) + pl (x.v14[5].toNat) (y.v14[5].toNat) + pl (x.v03[5].toNat) (y.v25[5].toNat)))) * 128) + ((ph (x.v14[1].toNat) (y.v03[1].toNat) + ph (x.v03[1].toNat) (y.v14[1].toNat)) + (pl (x.v25[1].toNat) (y.v03[1].toNat) + pl (x.v14[1].toNat) (y.v14[1].toNat) + pl (x.v03[1].toNat) (y.v25[1].toNat)))) + (((ph (x.v25[5].toNat) (y.v25[1].toNat)) + ((ph (x.v14[5].toNat) (y.v03[5].toNat) + ph (x.v03[5].toNat) (y.v14[5].toNat) + ph (x.v25[1].toNat) (y.v25[5].toNat)) + (pl (x.v25[5].toNat) (y.v03[5].toNat) + pl (x.v14[5].toNat) (y.v14[5].toNat) + pl (x.v03[5].toNat) (y.v25[5].toNat)))) * 24)
      = quadMulLimb x y 1 2 := by
  simp only [quadMulLimb, limb, col, quadLimb, vlane, Fin.reduceCastAdd, Fin.reduceAddNat]
  ring

private theorem lane_18 (x y : Quad) :
    ((((ph (x.v25[6].toNat) (y.v25[2].toNat)) + ((ph (x.v14[6].toNat) (y.v03[6].toNat) + ph (x.v03[6].toNat) (y.v14[6].toNat) + ph (x.v25[2].toNat) (y.v25[6].toNat)) + (pl (x.v25[6].toNat) (y.v03[6].toNat) + pl (x.v14[6].toNat) (y.v14[6].toNat) + pl (x.v03[6].toNat) (y.v25[6].toNat)))) * 128) + ((ph (x.v14[2].toNat) (y.v03[2].toNat) + ph (x.v03[2].toNat) (y.v14[2].toNat)) + (pl (x.v25[2].toNat) (y.v03[2].toNat) + pl (x.v14[2].toNat) (y.v14[2].toNat) + pl (x.v03[2].toNat) (y.v25[2].toNat)))) + (((ph (x.v25[6].toNat) (y.v25[2].toNat)) + ((ph (x.v14[6].toNat) (y.v03[6].toNat) + ph (x.v03[6].toNat) (y.v14[6].toNat) + ph (x.v25[2].toNat) (y.v25[6].toNat)) + (pl (x.v25[6].toNat) (y.v03[6].toNat) + pl (x.v14[6].toNat) (y.v14[6].toNat) + pl (x.v03[6].toNat) (y.v25[6].toNat)))) * 24)
      = quadMulLimb x y 2 2 := by
  simp only [quadMulLimb, limb, col, quadLimb, vlane, Fin.reduceCastAdd, Fin.reduceAddNat]
  ring

private theorem lane_19 (x y : Quad) :
    ((((ph (x.v25[7].toNat) (y.v25[3].toNat)) + ((ph (x.v14[7].toNat) (y.v03[7].toNat) + ph (x.v03[7].toNat) (y.v14[7].toNat) + ph (x.v25[3].toNat) (y.v25[7].toNat)) + (pl (x.v25[7].toNat) (y.v03[7].toNat) + pl (x.v14[7].toNat) (y.v14[7].toNat) + pl (x.v03[7].toNat) (y.v25[7].toNat)))) * 128) + ((ph (x.v14[3].toNat) (y.v03[3].toNat) + ph (x.v03[3].toNat) (y.v14[3].toNat)) + (pl (x.v25[3].toNat) (y.v03[3].toNat) + pl (x.v14[3].toNat) (y.v14[3].toNat) + pl (x.v03[3].toNat) (y.v25[3].toNat)))) + (((ph (x.v25[7].toNat) (y.v25[3].toNat)) + ((ph (x.v14[7].toNat) (y.v03[7].toNat) + ph (x.v03[7].toNat) (y.v14[7].toNat) + ph (x.v25[3].toNat) (y.v25[7].toNat)) + (pl (x.v25[7].toNat) (y.v03[7].toNat) + pl (x.v14[7].toNat) (y.v14[7].toNat) + pl (x.v03[7].toNat) (y.v25[7].toNat)))) * 24)
      = quadMulLimb x y 3 2 := by
  simp only [quadMulLimb, limb, col, quadLimb, vlane, Fin.reduceCastAdd, Fin.reduceAddNat]
  ring

private theorem lane_20 (x y : Quad) :
    (((ph (x.v25[4].toNat) (y.v25[4].toNat)) * 128) + (((ph (x.v14[4].toNat) (y.v03[0].toNat) + ph (x.v03[4].toNat) (y.v14[0].toNat) + ph (x.v25[0].toNat) (y.v25[0].toNat)) + (pl (x.v25[4].toNat) (y.v03[0].toNat) + pl (x.v14[4].toNat) (y.v14[0].toNat) + pl (x.v03[4].toNat) (y.v25[0].toNat))) + ((ph (x.v14[0].toNat) (y.v03[4].toNat) + ph (x.v03[0].toNat) (y.v14[4].toNat)) + (pl (x.v25[0].toNat) (y.v03[4].toNat) + pl (x.v14[0].toNat) (y.v14[4].toNat) + pl (x.v03[0].toNat) (y.v25[4].toNat))))) + ((ph (x.v25[4].toNat) (y.v25[4].toNat)) * 24)
      = quadMulLimb x y 0 5 := by
  simp only [quadMulLimb, limb, col, ph, pl, quadLimb, vlane,
    Fin.reduceCastAdd, Fin.reduceAddNat, Nat.mul_comm, Nat.mul_left_comm]
  ring_nf

private theorem lane_21 (x y : Quad) :
    (((ph (x.v25[5].toNat) (y.v25[5].toNat)) * 128) + (((ph (x.v14[5].toNat) (y.v03[1].toNat) + ph (x.v03[5].toNat) (y.v14[1].toNat) + ph (x.v25[1].toNat) (y.v25[1].toNat)) + (pl (x.v25[5].toNat) (y.v03[1].toNat) + pl (x.v14[5].toNat) (y.v14[1].toNat) + pl (x.v03[5].toNat) (y.v25[1].toNat))) + ((ph (x.v14[1].toNat) (y.v03[5].toNat) + ph (x.v03[1].toNat) (y.v14[5].toNat)) + (pl (x.v25[1].toNat) (y.v03[5].toNat) + pl (x.v14[1].toNat) (y.v14[5].toNat) + pl (x.v03[1].toNat) (y.v25[5].toNat))))) + ((ph (x.v25[5].toNat) (y.v25[5].toNat)) * 24)
      = quadMulLimb x y 1 5 := by
  simp only [quadMulLimb, limb, col, ph, pl, quadLimb, vlane,
    Fin.reduceCastAdd, Fin.reduceAddNat, Nat.mul_comm, Nat.mul_left_comm]
  ring_nf

private theorem lane_22 (x y : Quad) :
    (((ph (x.v25[6].toNat) (y.v25[6].toNat)) * 128) + (((ph (x.v14[6].toNat) (y.v03[2].toNat) + ph (x.v03[6].toNat) (y.v14[2].toNat) + ph (x.v25[2].toNat) (y.v25[2].toNat)) + (pl (x.v25[6].toNat) (y.v03[2].toNat) + pl (x.v14[6].toNat) (y.v14[2].toNat) + pl (x.v03[6].toNat) (y.v25[2].toNat))) + ((ph (x.v14[2].toNat) (y.v03[6].toNat) + ph (x.v03[2].toNat) (y.v14[6].toNat)) + (pl (x.v25[2].toNat) (y.v03[6].toNat) + pl (x.v14[2].toNat) (y.v14[6].toNat) + pl (x.v03[2].toNat) (y.v25[6].toNat))))) + ((ph (x.v25[6].toNat) (y.v25[6].toNat)) * 24)
      = quadMulLimb x y 2 5 := by
  simp only [quadMulLimb, limb, col, ph, pl, quadLimb, vlane,
    Fin.reduceCastAdd, Fin.reduceAddNat, Nat.mul_comm, Nat.mul_left_comm]
  ring_nf

private theorem lane_23 (x y : Quad) :
    (((ph (x.v25[7].toNat) (y.v25[7].toNat)) * 128) + (((ph (x.v14[7].toNat) (y.v03[3].toNat) + ph (x.v03[7].toNat) (y.v14[3].toNat) + ph (x.v25[3].toNat) (y.v25[3].toNat)) + (pl (x.v25[7].toNat) (y.v03[3].toNat) + pl (x.v14[7].toNat) (y.v14[3].toNat) + pl (x.v03[7].toNat) (y.v25[3].toNat))) + ((ph (x.v14[3].toNat) (y.v03[7].toNat) + ph (x.v03[3].toNat) (y.v14[7].toNat)) + (pl (x.v25[3].toNat) (y.v03[7].toNat) + pl (x.v14[3].toNat) (y.v14[7].toNat) + pl (x.v03[3].toNat) (y.v25[7].toNat))))) + ((ph (x.v25[7].toNat) (y.v25[7].toNat)) * 24)
      = quadMulLimb x y 3 5 := by
  simp only [quadMulLimb, limb, col, ph, pl, quadLimb, vlane,
    Fin.reduceCastAdd, Fin.reduceAddNat, Nat.mul_comm, Nat.mul_left_comm]
  ring_nf

/-! ## The derivation

The bound facts `quad_vpmadd52` needs: a `vpmadd52h` lane reads
`(u % 2^52) * (v % 2^52) / 2^52`, which is `phRaw u v` only when both operands
are already below `2^52`, and `u47` inputs are. One quantified lemma per input
vector rather than one per lane keeps the simp set small.

`Lean.mkIdent` escapes macro hygiene so these refer to the `have`s of the
theorem below, which the generated body names by convention. -/

local macro "quad_shuffle " h:term " with " ns:Lean.Parser.Tactic.simpLemma,* : tactic =>
  `(tactic| denote_shuffle $h with quadDualValMem, quadLimb, vlane, $ns,*)

local macro "quad_madd52 " h:term " with " ns:Lean.Parser.Tactic.simpLemma,* : tactic =>
  `(tactic| quad_vpmadd52 $h with quadDualValMem,
      $(Lean.mkIdent `bx03):term, $(Lean.mkIdent `bx14):term, $(Lean.mkIdent `bx25):term,
      $(Lean.mkIdent `by03):term, $(Lean.mkIdent `by14):term, $(Lean.mkIdent `by25):term, $ns,*)


set_option maxHeartbeats 40000000 in
set_option maxRecDepth 100000 in
/-- **Limb derivation**: on unreduced inputs the region denotes to exactly
three whole-vector stores, of the three vectors the specification predicts,
through the three pointer parameters in declaration order. All 89
instructions are carried through at the N level. -/
theorem denote_fd_r43x6_quad_mul_fast (x y : Quad)
    (hx03 : R43x6.U47 x.v03) (hx14 : R43x6.U47 x.v14) (hx25 : R43x6.U47 x.v25)
    (hy03 : R43x6.U47 y.v03) (hy14 : R43x6.U47 y.v14) (hy25 : R43x6.U47 y.v25)
    (p₀ p₁ p₂ : SLLVM.Ptr) :
    fd_r43x6_quad_mul_fast.denote
        (quadDualValMem p₀ p₁ p₂ x y) =
      (do storeVec p₀ ((quadMulResult x y).v03.map PoisonOr.value)
          storeVec p₁ ((quadMulResult x y).v14.map PoisonOr.value)
          storeVec p₂ ((quadMulResult x y).v25.map PoisonOr.value)
          pure (HVector.nil :
            HVector TyDenote.toType ([] : List SLLVM.Ty))) := by
  have bx03 : ∀ (i : ℕ) (h : i < 8),
      (x.v03[i]'h).toNat % 4503599627370496 = (x.v03[i]'h).toNat := fun i h =>
    Nat.mod_eq_of_lt (by
      have : (x.v03[i]'h).toNat < 2 ^ 47 := unn_toNat x.v03 47 (by omega) hx03 ⟨i, h⟩; omega)
  have bx14 : ∀ (i : ℕ) (h : i < 8),
      (x.v14[i]'h).toNat % 4503599627370496 = (x.v14[i]'h).toNat := fun i h =>
    Nat.mod_eq_of_lt (by
      have : (x.v14[i]'h).toNat < 2 ^ 47 := unn_toNat x.v14 47 (by omega) hx14 ⟨i, h⟩; omega)
  have bx25 : ∀ (i : ℕ) (h : i < 8),
      (x.v25[i]'h).toNat % 4503599627370496 = (x.v25[i]'h).toNat := fun i h =>
    Nat.mod_eq_of_lt (by
      have : (x.v25[i]'h).toNat < 2 ^ 47 := unn_toNat x.v25 47 (by omega) hx25 ⟨i, h⟩; omega)
  have by03 : ∀ (i : ℕ) (h : i < 8),
      (y.v03[i]'h).toNat % 4503599627370496 = (y.v03[i]'h).toNat := fun i h =>
    Nat.mod_eq_of_lt (by
      have : (y.v03[i]'h).toNat < 2 ^ 47 := unn_toNat y.v03 47 (by omega) hy03 ⟨i, h⟩; omega)
  have by14 : ∀ (i : ℕ) (h : i < 8),
      (y.v14[i]'h).toNat % 4503599627370496 = (y.v14[i]'h).toNat := fun i h =>
    Nat.mod_eq_of_lt (by
      have : (y.v14[i]'h).toNat < 2 ^ 47 := unn_toNat y.v14 47 (by omega) hy14 ⟨i, h⟩; omega)
  have by25 : ∀ (i : ℕ) (h : i < 8),
      (y.v25[i]'h).toNat % 4503599627370496 = (y.v25[i]'h).toNat := fun i h =>
    Nat.mod_eq_of_lt (by
      have : (y.v25[i]'h).toNat < 2 ^ 47 := unn_toNat y.v25 47 (by omega) hy25 ⟨i, h⟩; omega)
  unfold fd_r43x6_quad_mul_fast
  let X : Fin 4 → Fin 6 → ℕ := quadLimb x.v03 x.v14 x.v25
  let Y : Fin 4 → Fin 6 → ℕ := quadLimb y.v03 y.v14 y.v25

  -- the constants: the `152 = 128 + 24` fold, the `wwl_shl` amounts and `_zz`
  denote_step_all v 4
  let zeroVec := toBitVecValue 64 (Vector.replicate 8 0)
  let nineVec := toBitVecValue 64 (Vector.replicate 8 9)
  let sevenVec := toBitVecValue 64 (Vector.replicate 8 7)
  let tf4Vec := toBitVecValue 64 (Vector.replicate 8 24)
  have h24 : v0 = tf4Vec := by denote_dense hv0
  have h7 : v1 = sevenVec := by denote_dense hv1
  have h9 : v2 = nineVec := by denote_dense hv2
  have hzz : v3 = zeroVec := by denote_dense hv3
  subst hzz h9 h7 h24

  -- x00 .. x55: `wwl_pack_halves( x03,0, x03,0 )` and friends
  denote_step_all v 5
  -- x00: limb 0 of each element, broadcast to both halves: `wwl_pack_halves( x03,0, x03,0 )`
  let x00 := toBitVecValue 64 #v[X 0 0, X 1 0, X 2 0, X 3 0, X 0 0, X 1 0, X 2 0, X 3 0]
  have hx00 : v5 = x00 := by quad_shuffle hv5 with x00
  subst hx00
  denote_clear v 5 5
  denote_step_all v 6
  -- x11: limb 1 broadcast
  let x11 := toBitVecValue 64 #v[X 0 1, X 1 1, X 2 1, X 3 1, X 0 1, X 1 1, X 2 1, X 3 1]
  have hx11 : v6 = x11 := by quad_shuffle hv6 with x11
  subst hx11
  denote_clear v 6 6
  denote_step_all v 7
  -- x22: limb 2 broadcast
  let x22 := toBitVecValue 64 #v[X 0 2, X 1 2, X 2 2, X 3 2, X 0 2, X 1 2, X 2 2, X 3 2]
  have hx22 : v7 = x22 := by quad_shuffle hv7 with x22
  subst hx22
  denote_clear v 7 7
  denote_step_all v 8
  -- x33: limb 3 broadcast
  let x33 := toBitVecValue 64 #v[X 0 3, X 1 3, X 2 3, X 3 3, X 0 3, X 1 3, X 2 3, X 3 3]
  have hx33 : v8 = x33 := by quad_shuffle hv8 with x33
  subst hx33
  denote_clear v 8 8
  denote_step_all v 9
  -- x44: limb 4 broadcast
  let x44 := toBitVecValue 64 #v[X 0 4, X 1 4, X 2 4, X 3 4, X 0 4, X 1 4, X 2 4, X 3 4]
  have hx44 : v9 = x44 := by quad_shuffle hv9 with x44
  subst hx44
  denote_clear v 9 9
  denote_step_all v 10
  -- x55: limb 5 broadcast
  let x55 := toBitVecValue 64 #v[X 0 5, X 1 5, X 2 5, X 3 5, X 0 5, X 1 5, X 2 5, X 3 5]
  have hx55 : v10 = x55 := by quad_shuffle hv10 with x55
  subst hx55
  denote_clear v 10 10

  -- p0_q3 .. p8_qb: the 36 madd52 products, column I low, column I+3 high
  denote_step_all v 11
  -- p0_q3: column 0 in the low half, part of column 3 in the high
  let p0_q3 := toBitVecValue 64 #v[pl (X 0 0) (Y 0 0), pl (X 1 0) (Y 1 0), pl (X 2 0) (Y 2 0), pl (X 3 0) (Y 3 0), pl (X 0 0) (Y 0 3), pl (X 1 0) (Y 1 3), pl (X 2 0) (Y 2 3), pl (X 3 0) (Y 3 3)]
  have hp0_q3 : v11 = p0_q3 := by quad_madd52 hv11 with p0_q3, x00
  subst hp0_q3
  denote_clear v 11 11
  denote_step_all v 12
  let p1_q4_lo1 := toBitVecValue 64 #v[pl (X 0 1) (Y 0 0), pl (X 1 1) (Y 1 0), pl (X 2 1) (Y 2 0), pl (X 3 1) (Y 3 0), pl (X 0 1) (Y 0 3), pl (X 1 1) (Y 1 3), pl (X 2 1) (Y 2 3), pl (X 3 1) (Y 3 3)]
  have hp1_q4_lo1 : v12 = p1_q4_lo1 := by quad_madd52 hv12 with p1_q4_lo1, x11
  subst hp1_q4_lo1
  denote_clear v 12 12
  denote_step_all v 13
  let p1_q4_lo := toBitVecValue 64 #v[pl (X 0 1) (Y 0 0) + pl (X 0 0) (Y 0 1), pl (X 1 1) (Y 1 0) + pl (X 1 0) (Y 1 1), pl (X 2 1) (Y 2 0) + pl (X 2 0) (Y 2 1), pl (X 3 1) (Y 3 0) + pl (X 3 0) (Y 3 1), pl (X 0 1) (Y 0 3) + pl (X 0 0) (Y 0 4), pl (X 1 1) (Y 1 3) + pl (X 1 0) (Y 1 4), pl (X 2 1) (Y 2 3) + pl (X 2 0) (Y 2 4), pl (X 3 1) (Y 3 3) + pl (X 3 0) (Y 3 4)]
  have hp1_q4_lo : v13 = p1_q4_lo := by quad_madd52 hv13 with p1_q4_lo, p1_q4_lo1, x00
  subst hp1_q4_lo
  denote_clear v 13 13
  denote_step_all v 14
  let p2_q5_lo1 := toBitVecValue 64 #v[pl (X 0 2) (Y 0 0), pl (X 1 2) (Y 1 0), pl (X 2 2) (Y 2 0), pl (X 3 2) (Y 3 0), pl (X 0 2) (Y 0 3), pl (X 1 2) (Y 1 3), pl (X 2 2) (Y 2 3), pl (X 3 2) (Y 3 3)]
  have hp2_q5_lo1 : v14 = p2_q5_lo1 := by quad_madd52 hv14 with p2_q5_lo1, x22
  subst hp2_q5_lo1
  denote_clear v 14 14
  denote_step_all v 15
  let p2_q5_lo2 := toBitVecValue 64 #v[pl (X 0 2) (Y 0 0) + pl (X 0 1) (Y 0 1), pl (X 1 2) (Y 1 0) + pl (X 1 1) (Y 1 1), pl (X 2 2) (Y 2 0) + pl (X 2 1) (Y 2 1), pl (X 3 2) (Y 3 0) + pl (X 3 1) (Y 3 1), pl (X 0 2) (Y 0 3) + pl (X 0 1) (Y 0 4), pl (X 1 2) (Y 1 3) + pl (X 1 1) (Y 1 4), pl (X 2 2) (Y 2 3) + pl (X 2 1) (Y 2 4), pl (X 3 2) (Y 3 3) + pl (X 3 1) (Y 3 4)]
  have hp2_q5_lo2 : v15 = p2_q5_lo2 := by quad_madd52 hv15 with p2_q5_lo1, p2_q5_lo2, x11
  subst hp2_q5_lo2
  denote_clear v 15 15
  denote_step_all v 16
  let p2_q5_lo := toBitVecValue 64 #v[pl (X 0 2) (Y 0 0) + pl (X 0 1) (Y 0 1) + pl (X 0 0) (Y 0 2), pl (X 1 2) (Y 1 0) + pl (X 1 1) (Y 1 1) + pl (X 1 0) (Y 1 2), pl (X 2 2) (Y 2 0) + pl (X 2 1) (Y 2 1) + pl (X 2 0) (Y 2 2), pl (X 3 2) (Y 3 0) + pl (X 3 1) (Y 3 1) + pl (X 3 0) (Y 3 2), pl (X 0 2) (Y 0 3) + pl (X 0 1) (Y 0 4) + pl (X 0 0) (Y 0 5), pl (X 1 2) (Y 1 3) + pl (X 1 1) (Y 1 4) + pl (X 1 0) (Y 1 5), pl (X 2 2) (Y 2 3) + pl (X 2 1) (Y 2 4) + pl (X 2 0) (Y 2 5), pl (X 3 2) (Y 3 3) + pl (X 3 1) (Y 3 4) + pl (X 3 0) (Y 3 5)]
  have hp2_q5_lo : v16 = p2_q5_lo := by quad_madd52 hv16 with p2_q5_lo, p2_q5_lo2, x00
  subst hp2_q5_lo
  denote_clear v 16 16
  denote_step_all v 17
  let p3_q6_lo1 := toBitVecValue 64 #v[pl (X 0 3) (Y 0 0), pl (X 1 3) (Y 1 0), pl (X 2 3) (Y 2 0), pl (X 3 3) (Y 3 0), pl (X 0 3) (Y 0 3), pl (X 1 3) (Y 1 3), pl (X 2 3) (Y 2 3), pl (X 3 3) (Y 3 3)]
  have hp3_q6_lo1 : v17 = p3_q6_lo1 := by quad_madd52 hv17 with p3_q6_lo1, x33
  subst hp3_q6_lo1
  denote_clear v 17 17
  denote_step_all v 18
  let p3_q6_lo2 := toBitVecValue 64 #v[pl (X 0 3) (Y 0 0) + pl (X 0 2) (Y 0 1), pl (X 1 3) (Y 1 0) + pl (X 1 2) (Y 1 1), pl (X 2 3) (Y 2 0) + pl (X 2 2) (Y 2 1), pl (X 3 3) (Y 3 0) + pl (X 3 2) (Y 3 1), pl (X 0 3) (Y 0 3) + pl (X 0 2) (Y 0 4), pl (X 1 3) (Y 1 3) + pl (X 1 2) (Y 1 4), pl (X 2 3) (Y 2 3) + pl (X 2 2) (Y 2 4), pl (X 3 3) (Y 3 3) + pl (X 3 2) (Y 3 4)]
  have hp3_q6_lo2 : v18 = p3_q6_lo2 := by quad_madd52 hv18 with p3_q6_lo1, p3_q6_lo2, x22
  subst hp3_q6_lo2
  denote_clear v 18 18
  denote_step_all v 19
  let p3_q6_lo := toBitVecValue 64 #v[pl (X 0 3) (Y 0 0) + pl (X 0 2) (Y 0 1) + pl (X 0 1) (Y 0 2), pl (X 1 3) (Y 1 0) + pl (X 1 2) (Y 1 1) + pl (X 1 1) (Y 1 2), pl (X 2 3) (Y 2 0) + pl (X 2 2) (Y 2 1) + pl (X 2 1) (Y 2 2), pl (X 3 3) (Y 3 0) + pl (X 3 2) (Y 3 1) + pl (X 3 1) (Y 3 2), pl (X 0 3) (Y 0 3) + pl (X 0 2) (Y 0 4) + pl (X 0 1) (Y 0 5), pl (X 1 3) (Y 1 3) + pl (X 1 2) (Y 1 4) + pl (X 1 1) (Y 1 5), pl (X 2 3) (Y 2 3) + pl (X 2 2) (Y 2 4) + pl (X 2 1) (Y 2 5), pl (X 3 3) (Y 3 3) + pl (X 3 2) (Y 3 4) + pl (X 3 1) (Y 3 5)]
  have hp3_q6_lo : v19 = p3_q6_lo := by quad_madd52 hv19 with p3_q6_lo, p3_q6_lo2, x11
  subst hp3_q6_lo
  denote_clear v 19 19
  denote_step_all v 20
  let p4_q7_lo1 := toBitVecValue 64 #v[pl (X 0 4) (Y 0 0), pl (X 1 4) (Y 1 0), pl (X 2 4) (Y 2 0), pl (X 3 4) (Y 3 0), pl (X 0 4) (Y 0 3), pl (X 1 4) (Y 1 3), pl (X 2 4) (Y 2 3), pl (X 3 4) (Y 3 3)]
  have hp4_q7_lo1 : v20 = p4_q7_lo1 := by quad_madd52 hv20 with p4_q7_lo1, x44
  subst hp4_q7_lo1
  denote_clear v 20 20
  denote_step_all v 21
  let p4_q7_lo2 := toBitVecValue 64 #v[pl (X 0 4) (Y 0 0) + pl (X 0 3) (Y 0 1), pl (X 1 4) (Y 1 0) + pl (X 1 3) (Y 1 1), pl (X 2 4) (Y 2 0) + pl (X 2 3) (Y 2 1), pl (X 3 4) (Y 3 0) + pl (X 3 3) (Y 3 1), pl (X 0 4) (Y 0 3) + pl (X 0 3) (Y 0 4), pl (X 1 4) (Y 1 3) + pl (X 1 3) (Y 1 4), pl (X 2 4) (Y 2 3) + pl (X 2 3) (Y 2 4), pl (X 3 4) (Y 3 3) + pl (X 3 3) (Y 3 4)]
  have hp4_q7_lo2 : v21 = p4_q7_lo2 := by quad_madd52 hv21 with p4_q7_lo1, p4_q7_lo2, x33
  subst hp4_q7_lo2
  denote_clear v 21 21
  denote_step_all v 22
  let p4_q7_lo := toBitVecValue 64 #v[pl (X 0 4) (Y 0 0) + pl (X 0 3) (Y 0 1) + pl (X 0 2) (Y 0 2), pl (X 1 4) (Y 1 0) + pl (X 1 3) (Y 1 1) + pl (X 1 2) (Y 1 2), pl (X 2 4) (Y 2 0) + pl (X 2 3) (Y 2 1) + pl (X 2 2) (Y 2 2), pl (X 3 4) (Y 3 0) + pl (X 3 3) (Y 3 1) + pl (X 3 2) (Y 3 2), pl (X 0 4) (Y 0 3) + pl (X 0 3) (Y 0 4) + pl (X 0 2) (Y 0 5), pl (X 1 4) (Y 1 3) + pl (X 1 3) (Y 1 4) + pl (X 1 2) (Y 1 5), pl (X 2 4) (Y 2 3) + pl (X 2 3) (Y 2 4) + pl (X 2 2) (Y 2 5), pl (X 3 4) (Y 3 3) + pl (X 3 3) (Y 3 4) + pl (X 3 2) (Y 3 5)]
  have hp4_q7_lo : v22 = p4_q7_lo := by quad_madd52 hv22 with p4_q7_lo, p4_q7_lo2, x22
  subst hp4_q7_lo
  denote_clear v 22 22
  denote_step_all v 23
  let p5_q8_lo1 := toBitVecValue 64 #v[pl (X 0 5) (Y 0 0), pl (X 1 5) (Y 1 0), pl (X 2 5) (Y 2 0), pl (X 3 5) (Y 3 0), pl (X 0 5) (Y 0 3), pl (X 1 5) (Y 1 3), pl (X 2 5) (Y 2 3), pl (X 3 5) (Y 3 3)]
  have hp5_q8_lo1 : v23 = p5_q8_lo1 := by quad_madd52 hv23 with p5_q8_lo1, x55
  subst hp5_q8_lo1
  denote_clear v 23 23
  denote_step_all v 24
  let p5_q8_lo2 := toBitVecValue 64 #v[pl (X 0 5) (Y 0 0) + pl (X 0 4) (Y 0 1), pl (X 1 5) (Y 1 0) + pl (X 1 4) (Y 1 1), pl (X 2 5) (Y 2 0) + pl (X 2 4) (Y 2 1), pl (X 3 5) (Y 3 0) + pl (X 3 4) (Y 3 1), pl (X 0 5) (Y 0 3) + pl (X 0 4) (Y 0 4), pl (X 1 5) (Y 1 3) + pl (X 1 4) (Y 1 4), pl (X 2 5) (Y 2 3) + pl (X 2 4) (Y 2 4), pl (X 3 5) (Y 3 3) + pl (X 3 4) (Y 3 4)]
  have hp5_q8_lo2 : v24 = p5_q8_lo2 := by quad_madd52 hv24 with p5_q8_lo1, p5_q8_lo2, x44
  subst hp5_q8_lo2
  denote_clear v 24 24
  denote_step_all v 25
  let p5_q8_lo := toBitVecValue 64 #v[pl (X 0 5) (Y 0 0) + pl (X 0 4) (Y 0 1) + pl (X 0 3) (Y 0 2), pl (X 1 5) (Y 1 0) + pl (X 1 4) (Y 1 1) + pl (X 1 3) (Y 1 2), pl (X 2 5) (Y 2 0) + pl (X 2 4) (Y 2 1) + pl (X 2 3) (Y 2 2), pl (X 3 5) (Y 3 0) + pl (X 3 4) (Y 3 1) + pl (X 3 3) (Y 3 2), pl (X 0 5) (Y 0 3) + pl (X 0 4) (Y 0 4) + pl (X 0 3) (Y 0 5), pl (X 1 5) (Y 1 3) + pl (X 1 4) (Y 1 4) + pl (X 1 3) (Y 1 5), pl (X 2 5) (Y 2 3) + pl (X 2 4) (Y 2 4) + pl (X 2 3) (Y 2 5), pl (X 3 5) (Y 3 3) + pl (X 3 4) (Y 3 4) + pl (X 3 3) (Y 3 5)]
  have hp5_q8_lo : v25 = p5_q8_lo := by quad_madd52 hv25 with p5_q8_lo, p5_q8_lo2, x33
  subst hp5_q8_lo
  denote_clear v 25 25
  denote_step_all v 26
  let p6_q9_lo1 := toBitVecValue 64 #v[pl (X 0 5) (Y 0 1), pl (X 1 5) (Y 1 1), pl (X 2 5) (Y 2 1), pl (X 3 5) (Y 3 1), pl (X 0 5) (Y 0 4), pl (X 1 5) (Y 1 4), pl (X 2 5) (Y 2 4), pl (X 3 5) (Y 3 4)]
  have hp6_q9_lo1 : v26 = p6_q9_lo1 := by quad_madd52 hv26 with p6_q9_lo1, x55
  subst hp6_q9_lo1
  denote_clear v 26 26
  denote_step_all v 27
  let p6_q9_lo := toBitVecValue 64 #v[pl (X 0 5) (Y 0 1) + pl (X 0 4) (Y 0 2), pl (X 1 5) (Y 1 1) + pl (X 1 4) (Y 1 2), pl (X 2 5) (Y 2 1) + pl (X 2 4) (Y 2 2), pl (X 3 5) (Y 3 1) + pl (X 3 4) (Y 3 2), pl (X 0 5) (Y 0 4) + pl (X 0 4) (Y 0 5), pl (X 1 5) (Y 1 4) + pl (X 1 4) (Y 1 5), pl (X 2 5) (Y 2 4) + pl (X 2 4) (Y 2 5), pl (X 3 5) (Y 3 4) + pl (X 3 4) (Y 3 5)]
  have hp6_q9_lo : v27 = p6_q9_lo := by quad_madd52 hv27 with p6_q9_lo, p6_q9_lo1, x44
  subst hp6_q9_lo
  denote_clear v 27 27
  denote_step_all v 28
  let p7_qa_lo := toBitVecValue 64 #v[pl (X 0 5) (Y 0 2), pl (X 1 5) (Y 1 2), pl (X 2 5) (Y 2 2), pl (X 3 5) (Y 3 2), pl (X 0 5) (Y 0 5), pl (X 1 5) (Y 1 5), pl (X 2 5) (Y 2 5), pl (X 3 5) (Y 3 5)]
  have hp7_qa_lo : v28 = p7_qa_lo := by quad_madd52 hv28 with p7_qa_lo, x55
  subst hp7_qa_lo
  denote_clear v 28 28
  denote_step_all v 29
  let p1_q4_hiRaw := toBitVecValue 64 #v[phRaw (X 0 0) (Y 0 0), phRaw (X 1 0) (Y 1 0), phRaw (X 2 0) (Y 2 0), phRaw (X 3 0) (Y 3 0), phRaw (X 0 0) (Y 0 3), phRaw (X 1 0) (Y 1 3), phRaw (X 2 0) (Y 2 3), phRaw (X 3 0) (Y 3 3)]
  have hp1_q4_hiRaw : v29 = p1_q4_hiRaw := by quad_madd52 hv29 with p1_q4_hiRaw, x00
  subst hp1_q4_hiRaw
  denote_clear v 29 29
  denote_step_all v 30
  let p1_q4_hi := toBitVecValue 64 #v[ph (X 0 0) (Y 0 0), ph (X 1 0) (Y 1 0), ph (X 2 0) (Y 2 0), ph (X 3 0) (Y 3 0), ph (X 0 0) (Y 0 3), ph (X 1 0) (Y 1 3), ph (X 2 0) (Y 2 3), ph (X 3 0) (Y 3 3)]
  have hp1_q4_hi : v30 = p1_q4_hi := by quad_vecbin_ring hv30 with quadDualValMem, p1_q4_hi, p1_q4_hiRaw
  subst hp1_q4_hi
  denote_clear v 30 30
  denote_step_all v 31
  let p1_q4 := toBitVecValue 64 #v[(ph (X 0 0) (Y 0 0)) + (pl (X 0 1) (Y 0 0) + pl (X 0 0) (Y 0 1)), (ph (X 1 0) (Y 1 0)) + (pl (X 1 1) (Y 1 0) + pl (X 1 0) (Y 1 1)), (ph (X 2 0) (Y 2 0)) + (pl (X 2 1) (Y 2 0) + pl (X 2 0) (Y 2 1)), (ph (X 3 0) (Y 3 0)) + (pl (X 3 1) (Y 3 0) + pl (X 3 0) (Y 3 1)), (ph (X 0 0) (Y 0 3)) + (pl (X 0 1) (Y 0 3) + pl (X 0 0) (Y 0 4)), (ph (X 1 0) (Y 1 3)) + (pl (X 1 1) (Y 1 3) + pl (X 1 0) (Y 1 4)), (ph (X 2 0) (Y 2 3)) + (pl (X 2 1) (Y 2 3) + pl (X 2 0) (Y 2 4)), (ph (X 3 0) (Y 3 3)) + (pl (X 3 1) (Y 3 3) + pl (X 3 0) (Y 3 4))]
  have hp1_q4 : v31 = p1_q4 := by quad_vecbin hv31 with quadDualValMem, p1_q4, p1_q4_hi, p1_q4_lo
  subst hp1_q4
  denote_clear v 31 31
  denote_step_all v 32
  let p2_q5_hiRaw1 := toBitVecValue 64 #v[phRaw (X 0 1) (Y 0 0), phRaw (X 1 1) (Y 1 0), phRaw (X 2 1) (Y 2 0), phRaw (X 3 1) (Y 3 0), phRaw (X 0 1) (Y 0 3), phRaw (X 1 1) (Y 1 3), phRaw (X 2 1) (Y 2 3), phRaw (X 3 1) (Y 3 3)]
  have hp2_q5_hiRaw1 : v32 = p2_q5_hiRaw1 := by quad_madd52 hv32 with p2_q5_hiRaw1, x11
  subst hp2_q5_hiRaw1
  denote_clear v 32 32
  denote_step_all v 33
  let p2_q5_hiRaw := toBitVecValue 64 #v[phRaw (X 0 1) (Y 0 0) + phRaw (X 0 0) (Y 0 1), phRaw (X 1 1) (Y 1 0) + phRaw (X 1 0) (Y 1 1), phRaw (X 2 1) (Y 2 0) + phRaw (X 2 0) (Y 2 1), phRaw (X 3 1) (Y 3 0) + phRaw (X 3 0) (Y 3 1), phRaw (X 0 1) (Y 0 3) + phRaw (X 0 0) (Y 0 4), phRaw (X 1 1) (Y 1 3) + phRaw (X 1 0) (Y 1 4), phRaw (X 2 1) (Y 2 3) + phRaw (X 2 0) (Y 2 4), phRaw (X 3 1) (Y 3 3) + phRaw (X 3 0) (Y 3 4)]
  have hp2_q5_hiRaw : v33 = p2_q5_hiRaw := by quad_madd52 hv33 with p2_q5_hiRaw, p2_q5_hiRaw1, x00
  subst hp2_q5_hiRaw
  denote_clear v 33 33
  denote_step_all v 34
  let p2_q5_hi := toBitVecValue 64 #v[ph (X 0 1) (Y 0 0) + ph (X 0 0) (Y 0 1), ph (X 1 1) (Y 1 0) + ph (X 1 0) (Y 1 1), ph (X 2 1) (Y 2 0) + ph (X 2 0) (Y 2 1), ph (X 3 1) (Y 3 0) + ph (X 3 0) (Y 3 1), ph (X 0 1) (Y 0 3) + ph (X 0 0) (Y 0 4), ph (X 1 1) (Y 1 3) + ph (X 1 0) (Y 1 4), ph (X 2 1) (Y 2 3) + ph (X 2 0) (Y 2 4), ph (X 3 1) (Y 3 3) + ph (X 3 0) (Y 3 4)]
  have hp2_q5_hi : v34 = p2_q5_hi := by quad_vecbin_ring hv34 with quadDualValMem, p2_q5_hi, p2_q5_hiRaw
  subst hp2_q5_hi
  denote_clear v 34 34
  denote_step_all v 35
  let p2_q5 := toBitVecValue 64 #v[(ph (X 0 1) (Y 0 0) + ph (X 0 0) (Y 0 1)) + (pl (X 0 2) (Y 0 0) + pl (X 0 1) (Y 0 1) + pl (X 0 0) (Y 0 2)), (ph (X 1 1) (Y 1 0) + ph (X 1 0) (Y 1 1)) + (pl (X 1 2) (Y 1 0) + pl (X 1 1) (Y 1 1) + pl (X 1 0) (Y 1 2)), (ph (X 2 1) (Y 2 0) + ph (X 2 0) (Y 2 1)) + (pl (X 2 2) (Y 2 0) + pl (X 2 1) (Y 2 1) + pl (X 2 0) (Y 2 2)), (ph (X 3 1) (Y 3 0) + ph (X 3 0) (Y 3 1)) + (pl (X 3 2) (Y 3 0) + pl (X 3 1) (Y 3 1) + pl (X 3 0) (Y 3 2)), (ph (X 0 1) (Y 0 3) + ph (X 0 0) (Y 0 4)) + (pl (X 0 2) (Y 0 3) + pl (X 0 1) (Y 0 4) + pl (X 0 0) (Y 0 5)), (ph (X 1 1) (Y 1 3) + ph (X 1 0) (Y 1 4)) + (pl (X 1 2) (Y 1 3) + pl (X 1 1) (Y 1 4) + pl (X 1 0) (Y 1 5)), (ph (X 2 1) (Y 2 3) + ph (X 2 0) (Y 2 4)) + (pl (X 2 2) (Y 2 3) + pl (X 2 1) (Y 2 4) + pl (X 2 0) (Y 2 5)), (ph (X 3 1) (Y 3 3) + ph (X 3 0) (Y 3 4)) + (pl (X 3 2) (Y 3 3) + pl (X 3 1) (Y 3 4) + pl (X 3 0) (Y 3 5))]
  have hp2_q5 : v35 = p2_q5 := by quad_vecbin hv35 with quadDualValMem, p2_q5, p2_q5_hi, p2_q5_lo
  subst hp2_q5
  denote_clear v 35 35
  denote_step_all v 36
  let p3_q6_hiRaw1 := toBitVecValue 64 #v[phRaw (X 0 2) (Y 0 0), phRaw (X 1 2) (Y 1 0), phRaw (X 2 2) (Y 2 0), phRaw (X 3 2) (Y 3 0), phRaw (X 0 2) (Y 0 3), phRaw (X 1 2) (Y 1 3), phRaw (X 2 2) (Y 2 3), phRaw (X 3 2) (Y 3 3)]
  have hp3_q6_hiRaw1 : v36 = p3_q6_hiRaw1 := by quad_madd52 hv36 with p3_q6_hiRaw1, x22
  subst hp3_q6_hiRaw1
  denote_clear v 36 36
  denote_step_all v 37
  let p3_q6_hiRaw2 := toBitVecValue 64 #v[phRaw (X 0 2) (Y 0 0) + phRaw (X 0 1) (Y 0 1), phRaw (X 1 2) (Y 1 0) + phRaw (X 1 1) (Y 1 1), phRaw (X 2 2) (Y 2 0) + phRaw (X 2 1) (Y 2 1), phRaw (X 3 2) (Y 3 0) + phRaw (X 3 1) (Y 3 1), phRaw (X 0 2) (Y 0 3) + phRaw (X 0 1) (Y 0 4), phRaw (X 1 2) (Y 1 3) + phRaw (X 1 1) (Y 1 4), phRaw (X 2 2) (Y 2 3) + phRaw (X 2 1) (Y 2 4), phRaw (X 3 2) (Y 3 3) + phRaw (X 3 1) (Y 3 4)]
  have hp3_q6_hiRaw2 : v37 = p3_q6_hiRaw2 := by quad_madd52 hv37 with p3_q6_hiRaw1, p3_q6_hiRaw2, x11
  subst hp3_q6_hiRaw2
  denote_clear v 37 37
  denote_step_all v 38
  let p3_q6_hiRaw := toBitVecValue 64 #v[phRaw (X 0 2) (Y 0 0) + phRaw (X 0 1) (Y 0 1) + phRaw (X 0 0) (Y 0 2), phRaw (X 1 2) (Y 1 0) + phRaw (X 1 1) (Y 1 1) + phRaw (X 1 0) (Y 1 2), phRaw (X 2 2) (Y 2 0) + phRaw (X 2 1) (Y 2 1) + phRaw (X 2 0) (Y 2 2), phRaw (X 3 2) (Y 3 0) + phRaw (X 3 1) (Y 3 1) + phRaw (X 3 0) (Y 3 2), phRaw (X 0 2) (Y 0 3) + phRaw (X 0 1) (Y 0 4) + phRaw (X 0 0) (Y 0 5), phRaw (X 1 2) (Y 1 3) + phRaw (X 1 1) (Y 1 4) + phRaw (X 1 0) (Y 1 5), phRaw (X 2 2) (Y 2 3) + phRaw (X 2 1) (Y 2 4) + phRaw (X 2 0) (Y 2 5), phRaw (X 3 2) (Y 3 3) + phRaw (X 3 1) (Y 3 4) + phRaw (X 3 0) (Y 3 5)]
  have hp3_q6_hiRaw : v38 = p3_q6_hiRaw := by quad_madd52 hv38 with p3_q6_hiRaw, p3_q6_hiRaw2, x00
  subst hp3_q6_hiRaw
  denote_clear v 38 38
  denote_step_all v 39
  let p3_q6_hi := toBitVecValue 64 #v[ph (X 0 2) (Y 0 0) + ph (X 0 1) (Y 0 1) + ph (X 0 0) (Y 0 2), ph (X 1 2) (Y 1 0) + ph (X 1 1) (Y 1 1) + ph (X 1 0) (Y 1 2), ph (X 2 2) (Y 2 0) + ph (X 2 1) (Y 2 1) + ph (X 2 0) (Y 2 2), ph (X 3 2) (Y 3 0) + ph (X 3 1) (Y 3 1) + ph (X 3 0) (Y 3 2), ph (X 0 2) (Y 0 3) + ph (X 0 1) (Y 0 4) + ph (X 0 0) (Y 0 5), ph (X 1 2) (Y 1 3) + ph (X 1 1) (Y 1 4) + ph (X 1 0) (Y 1 5), ph (X 2 2) (Y 2 3) + ph (X 2 1) (Y 2 4) + ph (X 2 0) (Y 2 5), ph (X 3 2) (Y 3 3) + ph (X 3 1) (Y 3 4) + ph (X 3 0) (Y 3 5)]
  have hp3_q6_hi : v39 = p3_q6_hi := by quad_vecbin_ring hv39 with quadDualValMem, p3_q6_hi, p3_q6_hiRaw
  subst hp3_q6_hi
  denote_clear v 39 39
  denote_step_all v 40
  let p3_q6 := toBitVecValue 64 #v[(ph (X 0 2) (Y 0 0) + ph (X 0 1) (Y 0 1) + ph (X 0 0) (Y 0 2)) + (pl (X 0 3) (Y 0 0) + pl (X 0 2) (Y 0 1) + pl (X 0 1) (Y 0 2)), (ph (X 1 2) (Y 1 0) + ph (X 1 1) (Y 1 1) + ph (X 1 0) (Y 1 2)) + (pl (X 1 3) (Y 1 0) + pl (X 1 2) (Y 1 1) + pl (X 1 1) (Y 1 2)), (ph (X 2 2) (Y 2 0) + ph (X 2 1) (Y 2 1) + ph (X 2 0) (Y 2 2)) + (pl (X 2 3) (Y 2 0) + pl (X 2 2) (Y 2 1) + pl (X 2 1) (Y 2 2)), (ph (X 3 2) (Y 3 0) + ph (X 3 1) (Y 3 1) + ph (X 3 0) (Y 3 2)) + (pl (X 3 3) (Y 3 0) + pl (X 3 2) (Y 3 1) + pl (X 3 1) (Y 3 2)), (ph (X 0 2) (Y 0 3) + ph (X 0 1) (Y 0 4) + ph (X 0 0) (Y 0 5)) + (pl (X 0 3) (Y 0 3) + pl (X 0 2) (Y 0 4) + pl (X 0 1) (Y 0 5)), (ph (X 1 2) (Y 1 3) + ph (X 1 1) (Y 1 4) + ph (X 1 0) (Y 1 5)) + (pl (X 1 3) (Y 1 3) + pl (X 1 2) (Y 1 4) + pl (X 1 1) (Y 1 5)), (ph (X 2 2) (Y 2 3) + ph (X 2 1) (Y 2 4) + ph (X 2 0) (Y 2 5)) + (pl (X 2 3) (Y 2 3) + pl (X 2 2) (Y 2 4) + pl (X 2 1) (Y 2 5)), (ph (X 3 2) (Y 3 3) + ph (X 3 1) (Y 3 4) + ph (X 3 0) (Y 3 5)) + (pl (X 3 3) (Y 3 3) + pl (X 3 2) (Y 3 4) + pl (X 3 1) (Y 3 5))]
  have hp3_q6 : v40 = p3_q6 := by quad_vecbin hv40 with quadDualValMem, p3_q6, p3_q6_hi, p3_q6_lo
  subst hp3_q6
  denote_clear v 40 40
  denote_step_all v 41
  let p4_q7_hiRaw1 := toBitVecValue 64 #v[phRaw (X 0 3) (Y 0 0), phRaw (X 1 3) (Y 1 0), phRaw (X 2 3) (Y 2 0), phRaw (X 3 3) (Y 3 0), phRaw (X 0 3) (Y 0 3), phRaw (X 1 3) (Y 1 3), phRaw (X 2 3) (Y 2 3), phRaw (X 3 3) (Y 3 3)]
  have hp4_q7_hiRaw1 : v41 = p4_q7_hiRaw1 := by quad_madd52 hv41 with p4_q7_hiRaw1, x33
  subst hp4_q7_hiRaw1
  denote_clear v 41 41
  denote_step_all v 42
  let p4_q7_hiRaw2 := toBitVecValue 64 #v[phRaw (X 0 3) (Y 0 0) + phRaw (X 0 2) (Y 0 1), phRaw (X 1 3) (Y 1 0) + phRaw (X 1 2) (Y 1 1), phRaw (X 2 3) (Y 2 0) + phRaw (X 2 2) (Y 2 1), phRaw (X 3 3) (Y 3 0) + phRaw (X 3 2) (Y 3 1), phRaw (X 0 3) (Y 0 3) + phRaw (X 0 2) (Y 0 4), phRaw (X 1 3) (Y 1 3) + phRaw (X 1 2) (Y 1 4), phRaw (X 2 3) (Y 2 3) + phRaw (X 2 2) (Y 2 4), phRaw (X 3 3) (Y 3 3) + phRaw (X 3 2) (Y 3 4)]
  have hp4_q7_hiRaw2 : v42 = p4_q7_hiRaw2 := by quad_madd52 hv42 with p4_q7_hiRaw1, p4_q7_hiRaw2, x22
  subst hp4_q7_hiRaw2
  denote_clear v 42 42
  denote_step_all v 43
  let p4_q7_hiRaw := toBitVecValue 64 #v[phRaw (X 0 3) (Y 0 0) + phRaw (X 0 2) (Y 0 1) + phRaw (X 0 1) (Y 0 2), phRaw (X 1 3) (Y 1 0) + phRaw (X 1 2) (Y 1 1) + phRaw (X 1 1) (Y 1 2), phRaw (X 2 3) (Y 2 0) + phRaw (X 2 2) (Y 2 1) + phRaw (X 2 1) (Y 2 2), phRaw (X 3 3) (Y 3 0) + phRaw (X 3 2) (Y 3 1) + phRaw (X 3 1) (Y 3 2), phRaw (X 0 3) (Y 0 3) + phRaw (X 0 2) (Y 0 4) + phRaw (X 0 1) (Y 0 5), phRaw (X 1 3) (Y 1 3) + phRaw (X 1 2) (Y 1 4) + phRaw (X 1 1) (Y 1 5), phRaw (X 2 3) (Y 2 3) + phRaw (X 2 2) (Y 2 4) + phRaw (X 2 1) (Y 2 5), phRaw (X 3 3) (Y 3 3) + phRaw (X 3 2) (Y 3 4) + phRaw (X 3 1) (Y 3 5)]
  have hp4_q7_hiRaw : v43 = p4_q7_hiRaw := by quad_madd52 hv43 with p4_q7_hiRaw, p4_q7_hiRaw2, x11
  subst hp4_q7_hiRaw
  denote_clear v 43 43
  denote_step_all v 44
  let p4_q7_hi := toBitVecValue 64 #v[ph (X 0 3) (Y 0 0) + ph (X 0 2) (Y 0 1) + ph (X 0 1) (Y 0 2), ph (X 1 3) (Y 1 0) + ph (X 1 2) (Y 1 1) + ph (X 1 1) (Y 1 2), ph (X 2 3) (Y 2 0) + ph (X 2 2) (Y 2 1) + ph (X 2 1) (Y 2 2), ph (X 3 3) (Y 3 0) + ph (X 3 2) (Y 3 1) + ph (X 3 1) (Y 3 2), ph (X 0 3) (Y 0 3) + ph (X 0 2) (Y 0 4) + ph (X 0 1) (Y 0 5), ph (X 1 3) (Y 1 3) + ph (X 1 2) (Y 1 4) + ph (X 1 1) (Y 1 5), ph (X 2 3) (Y 2 3) + ph (X 2 2) (Y 2 4) + ph (X 2 1) (Y 2 5), ph (X 3 3) (Y 3 3) + ph (X 3 2) (Y 3 4) + ph (X 3 1) (Y 3 5)]
  have hp4_q7_hi : v44 = p4_q7_hi := by quad_vecbin_ring hv44 with quadDualValMem, p4_q7_hi, p4_q7_hiRaw
  subst hp4_q7_hi
  denote_clear v 44 44
  denote_step_all v 45
  let p4_q7 := toBitVecValue 64 #v[(ph (X 0 3) (Y 0 0) + ph (X 0 2) (Y 0 1) + ph (X 0 1) (Y 0 2)) + (pl (X 0 4) (Y 0 0) + pl (X 0 3) (Y 0 1) + pl (X 0 2) (Y 0 2)), (ph (X 1 3) (Y 1 0) + ph (X 1 2) (Y 1 1) + ph (X 1 1) (Y 1 2)) + (pl (X 1 4) (Y 1 0) + pl (X 1 3) (Y 1 1) + pl (X 1 2) (Y 1 2)), (ph (X 2 3) (Y 2 0) + ph (X 2 2) (Y 2 1) + ph (X 2 1) (Y 2 2)) + (pl (X 2 4) (Y 2 0) + pl (X 2 3) (Y 2 1) + pl (X 2 2) (Y 2 2)), (ph (X 3 3) (Y 3 0) + ph (X 3 2) (Y 3 1) + ph (X 3 1) (Y 3 2)) + (pl (X 3 4) (Y 3 0) + pl (X 3 3) (Y 3 1) + pl (X 3 2) (Y 3 2)), (ph (X 0 3) (Y 0 3) + ph (X 0 2) (Y 0 4) + ph (X 0 1) (Y 0 5)) + (pl (X 0 4) (Y 0 3) + pl (X 0 3) (Y 0 4) + pl (X 0 2) (Y 0 5)), (ph (X 1 3) (Y 1 3) + ph (X 1 2) (Y 1 4) + ph (X 1 1) (Y 1 5)) + (pl (X 1 4) (Y 1 3) + pl (X 1 3) (Y 1 4) + pl (X 1 2) (Y 1 5)), (ph (X 2 3) (Y 2 3) + ph (X 2 2) (Y 2 4) + ph (X 2 1) (Y 2 5)) + (pl (X 2 4) (Y 2 3) + pl (X 2 3) (Y 2 4) + pl (X 2 2) (Y 2 5)), (ph (X 3 3) (Y 3 3) + ph (X 3 2) (Y 3 4) + ph (X 3 1) (Y 3 5)) + (pl (X 3 4) (Y 3 3) + pl (X 3 3) (Y 3 4) + pl (X 3 2) (Y 3 5))]
  have hp4_q7 : v45 = p4_q7 := by quad_vecbin hv45 with quadDualValMem, p4_q7, p4_q7_hi, p4_q7_lo
  subst hp4_q7
  denote_clear v 45 45
  denote_step_all v 46
  let p5_q8_hiRaw1 := toBitVecValue 64 #v[phRaw (X 0 4) (Y 0 0), phRaw (X 1 4) (Y 1 0), phRaw (X 2 4) (Y 2 0), phRaw (X 3 4) (Y 3 0), phRaw (X 0 4) (Y 0 3), phRaw (X 1 4) (Y 1 3), phRaw (X 2 4) (Y 2 3), phRaw (X 3 4) (Y 3 3)]
  have hp5_q8_hiRaw1 : v46 = p5_q8_hiRaw1 := by quad_madd52 hv46 with p5_q8_hiRaw1, x44
  subst hp5_q8_hiRaw1
  denote_clear v 46 46
  denote_step_all v 47
  let p5_q8_hiRaw2 := toBitVecValue 64 #v[phRaw (X 0 4) (Y 0 0) + phRaw (X 0 3) (Y 0 1), phRaw (X 1 4) (Y 1 0) + phRaw (X 1 3) (Y 1 1), phRaw (X 2 4) (Y 2 0) + phRaw (X 2 3) (Y 2 1), phRaw (X 3 4) (Y 3 0) + phRaw (X 3 3) (Y 3 1), phRaw (X 0 4) (Y 0 3) + phRaw (X 0 3) (Y 0 4), phRaw (X 1 4) (Y 1 3) + phRaw (X 1 3) (Y 1 4), phRaw (X 2 4) (Y 2 3) + phRaw (X 2 3) (Y 2 4), phRaw (X 3 4) (Y 3 3) + phRaw (X 3 3) (Y 3 4)]
  have hp5_q8_hiRaw2 : v47 = p5_q8_hiRaw2 := by quad_madd52 hv47 with p5_q8_hiRaw1, p5_q8_hiRaw2, x33
  subst hp5_q8_hiRaw2
  denote_clear v 47 47
  denote_step_all v 48
  let p5_q8_hiRaw := toBitVecValue 64 #v[phRaw (X 0 4) (Y 0 0) + phRaw (X 0 3) (Y 0 1) + phRaw (X 0 2) (Y 0 2), phRaw (X 1 4) (Y 1 0) + phRaw (X 1 3) (Y 1 1) + phRaw (X 1 2) (Y 1 2), phRaw (X 2 4) (Y 2 0) + phRaw (X 2 3) (Y 2 1) + phRaw (X 2 2) (Y 2 2), phRaw (X 3 4) (Y 3 0) + phRaw (X 3 3) (Y 3 1) + phRaw (X 3 2) (Y 3 2), phRaw (X 0 4) (Y 0 3) + phRaw (X 0 3) (Y 0 4) + phRaw (X 0 2) (Y 0 5), phRaw (X 1 4) (Y 1 3) + phRaw (X 1 3) (Y 1 4) + phRaw (X 1 2) (Y 1 5), phRaw (X 2 4) (Y 2 3) + phRaw (X 2 3) (Y 2 4) + phRaw (X 2 2) (Y 2 5), phRaw (X 3 4) (Y 3 3) + phRaw (X 3 3) (Y 3 4) + phRaw (X 3 2) (Y 3 5)]
  have hp5_q8_hiRaw : v48 = p5_q8_hiRaw := by quad_madd52 hv48 with p5_q8_hiRaw, p5_q8_hiRaw2, x22
  subst hp5_q8_hiRaw
  denote_clear v 48 48
  denote_step_all v 49
  let p5_q8_hi := toBitVecValue 64 #v[ph (X 0 4) (Y 0 0) + ph (X 0 3) (Y 0 1) + ph (X 0 2) (Y 0 2), ph (X 1 4) (Y 1 0) + ph (X 1 3) (Y 1 1) + ph (X 1 2) (Y 1 2), ph (X 2 4) (Y 2 0) + ph (X 2 3) (Y 2 1) + ph (X 2 2) (Y 2 2), ph (X 3 4) (Y 3 0) + ph (X 3 3) (Y 3 1) + ph (X 3 2) (Y 3 2), ph (X 0 4) (Y 0 3) + ph (X 0 3) (Y 0 4) + ph (X 0 2) (Y 0 5), ph (X 1 4) (Y 1 3) + ph (X 1 3) (Y 1 4) + ph (X 1 2) (Y 1 5), ph (X 2 4) (Y 2 3) + ph (X 2 3) (Y 2 4) + ph (X 2 2) (Y 2 5), ph (X 3 4) (Y 3 3) + ph (X 3 3) (Y 3 4) + ph (X 3 2) (Y 3 5)]
  have hp5_q8_hi : v49 = p5_q8_hi := by quad_vecbin_ring hv49 with quadDualValMem, p5_q8_hi, p5_q8_hiRaw
  subst hp5_q8_hi
  denote_clear v 49 49
  denote_step_all v 50
  let p5_q8 := toBitVecValue 64 #v[(ph (X 0 4) (Y 0 0) + ph (X 0 3) (Y 0 1) + ph (X 0 2) (Y 0 2)) + (pl (X 0 5) (Y 0 0) + pl (X 0 4) (Y 0 1) + pl (X 0 3) (Y 0 2)), (ph (X 1 4) (Y 1 0) + ph (X 1 3) (Y 1 1) + ph (X 1 2) (Y 1 2)) + (pl (X 1 5) (Y 1 0) + pl (X 1 4) (Y 1 1) + pl (X 1 3) (Y 1 2)), (ph (X 2 4) (Y 2 0) + ph (X 2 3) (Y 2 1) + ph (X 2 2) (Y 2 2)) + (pl (X 2 5) (Y 2 0) + pl (X 2 4) (Y 2 1) + pl (X 2 3) (Y 2 2)), (ph (X 3 4) (Y 3 0) + ph (X 3 3) (Y 3 1) + ph (X 3 2) (Y 3 2)) + (pl (X 3 5) (Y 3 0) + pl (X 3 4) (Y 3 1) + pl (X 3 3) (Y 3 2)), (ph (X 0 4) (Y 0 3) + ph (X 0 3) (Y 0 4) + ph (X 0 2) (Y 0 5)) + (pl (X 0 5) (Y 0 3) + pl (X 0 4) (Y 0 4) + pl (X 0 3) (Y 0 5)), (ph (X 1 4) (Y 1 3) + ph (X 1 3) (Y 1 4) + ph (X 1 2) (Y 1 5)) + (pl (X 1 5) (Y 1 3) + pl (X 1 4) (Y 1 4) + pl (X 1 3) (Y 1 5)), (ph (X 2 4) (Y 2 3) + ph (X 2 3) (Y 2 4) + ph (X 2 2) (Y 2 5)) + (pl (X 2 5) (Y 2 3) + pl (X 2 4) (Y 2 4) + pl (X 2 3) (Y 2 5)), (ph (X 3 4) (Y 3 3) + ph (X 3 3) (Y 3 4) + ph (X 3 2) (Y 3 5)) + (pl (X 3 5) (Y 3 3) + pl (X 3 4) (Y 3 4) + pl (X 3 3) (Y 3 5))]
  have hp5_q8 : v50 = p5_q8 := by quad_vecbin hv50 with quadDualValMem, p5_q8, p5_q8_hi, p5_q8_lo
  subst hp5_q8
  denote_clear v 50 50
  denote_step_all v 51
  let p6_q9_hiRaw1 := toBitVecValue 64 #v[phRaw (X 0 5) (Y 0 0), phRaw (X 1 5) (Y 1 0), phRaw (X 2 5) (Y 2 0), phRaw (X 3 5) (Y 3 0), phRaw (X 0 5) (Y 0 3), phRaw (X 1 5) (Y 1 3), phRaw (X 2 5) (Y 2 3), phRaw (X 3 5) (Y 3 3)]
  have hp6_q9_hiRaw1 : v51 = p6_q9_hiRaw1 := by quad_madd52 hv51 with p6_q9_hiRaw1, x55
  subst hp6_q9_hiRaw1
  denote_clear v 51 51
  denote_step_all v 52
  let p6_q9_hiRaw2 := toBitVecValue 64 #v[phRaw (X 0 5) (Y 0 0) + phRaw (X 0 4) (Y 0 1), phRaw (X 1 5) (Y 1 0) + phRaw (X 1 4) (Y 1 1), phRaw (X 2 5) (Y 2 0) + phRaw (X 2 4) (Y 2 1), phRaw (X 3 5) (Y 3 0) + phRaw (X 3 4) (Y 3 1), phRaw (X 0 5) (Y 0 3) + phRaw (X 0 4) (Y 0 4), phRaw (X 1 5) (Y 1 3) + phRaw (X 1 4) (Y 1 4), phRaw (X 2 5) (Y 2 3) + phRaw (X 2 4) (Y 2 4), phRaw (X 3 5) (Y 3 3) + phRaw (X 3 4) (Y 3 4)]
  have hp6_q9_hiRaw2 : v52 = p6_q9_hiRaw2 := by quad_madd52 hv52 with p6_q9_hiRaw1, p6_q9_hiRaw2, x44
  subst hp6_q9_hiRaw2
  denote_clear v 52 52
  denote_step_all v 53
  let p6_q9_hiRaw := toBitVecValue 64 #v[phRaw (X 0 5) (Y 0 0) + phRaw (X 0 4) (Y 0 1) + phRaw (X 0 3) (Y 0 2), phRaw (X 1 5) (Y 1 0) + phRaw (X 1 4) (Y 1 1) + phRaw (X 1 3) (Y 1 2), phRaw (X 2 5) (Y 2 0) + phRaw (X 2 4) (Y 2 1) + phRaw (X 2 3) (Y 2 2), phRaw (X 3 5) (Y 3 0) + phRaw (X 3 4) (Y 3 1) + phRaw (X 3 3) (Y 3 2), phRaw (X 0 5) (Y 0 3) + phRaw (X 0 4) (Y 0 4) + phRaw (X 0 3) (Y 0 5), phRaw (X 1 5) (Y 1 3) + phRaw (X 1 4) (Y 1 4) + phRaw (X 1 3) (Y 1 5), phRaw (X 2 5) (Y 2 3) + phRaw (X 2 4) (Y 2 4) + phRaw (X 2 3) (Y 2 5), phRaw (X 3 5) (Y 3 3) + phRaw (X 3 4) (Y 3 4) + phRaw (X 3 3) (Y 3 5)]
  have hp6_q9_hiRaw : v53 = p6_q9_hiRaw := by quad_madd52 hv53 with p6_q9_hiRaw, p6_q9_hiRaw2, x33
  subst hp6_q9_hiRaw
  denote_clear v 53 53
  denote_step_all v 54
  let p6_q9_hi := toBitVecValue 64 #v[ph (X 0 5) (Y 0 0) + ph (X 0 4) (Y 0 1) + ph (X 0 3) (Y 0 2), ph (X 1 5) (Y 1 0) + ph (X 1 4) (Y 1 1) + ph (X 1 3) (Y 1 2), ph (X 2 5) (Y 2 0) + ph (X 2 4) (Y 2 1) + ph (X 2 3) (Y 2 2), ph (X 3 5) (Y 3 0) + ph (X 3 4) (Y 3 1) + ph (X 3 3) (Y 3 2), ph (X 0 5) (Y 0 3) + ph (X 0 4) (Y 0 4) + ph (X 0 3) (Y 0 5), ph (X 1 5) (Y 1 3) + ph (X 1 4) (Y 1 4) + ph (X 1 3) (Y 1 5), ph (X 2 5) (Y 2 3) + ph (X 2 4) (Y 2 4) + ph (X 2 3) (Y 2 5), ph (X 3 5) (Y 3 3) + ph (X 3 4) (Y 3 4) + ph (X 3 3) (Y 3 5)]
  have hp6_q9_hi : v54 = p6_q9_hi := by quad_vecbin_ring hv54 with quadDualValMem, p6_q9_hi, p6_q9_hiRaw
  subst hp6_q9_hi
  denote_clear v 54 54
  denote_step_all v 55
  let p6_q9 := toBitVecValue 64 #v[(ph (X 0 5) (Y 0 0) + ph (X 0 4) (Y 0 1) + ph (X 0 3) (Y 0 2)) + (pl (X 0 5) (Y 0 1) + pl (X 0 4) (Y 0 2)), (ph (X 1 5) (Y 1 0) + ph (X 1 4) (Y 1 1) + ph (X 1 3) (Y 1 2)) + (pl (X 1 5) (Y 1 1) + pl (X 1 4) (Y 1 2)), (ph (X 2 5) (Y 2 0) + ph (X 2 4) (Y 2 1) + ph (X 2 3) (Y 2 2)) + (pl (X 2 5) (Y 2 1) + pl (X 2 4) (Y 2 2)), (ph (X 3 5) (Y 3 0) + ph (X 3 4) (Y 3 1) + ph (X 3 3) (Y 3 2)) + (pl (X 3 5) (Y 3 1) + pl (X 3 4) (Y 3 2)), (ph (X 0 5) (Y 0 3) + ph (X 0 4) (Y 0 4) + ph (X 0 3) (Y 0 5)) + (pl (X 0 5) (Y 0 4) + pl (X 0 4) (Y 0 5)), (ph (X 1 5) (Y 1 3) + ph (X 1 4) (Y 1 4) + ph (X 1 3) (Y 1 5)) + (pl (X 1 5) (Y 1 4) + pl (X 1 4) (Y 1 5)), (ph (X 2 5) (Y 2 3) + ph (X 2 4) (Y 2 4) + ph (X 2 3) (Y 2 5)) + (pl (X 2 5) (Y 2 4) + pl (X 2 4) (Y 2 5)), (ph (X 3 5) (Y 3 3) + ph (X 3 4) (Y 3 4) + ph (X 3 3) (Y 3 5)) + (pl (X 3 5) (Y 3 4) + pl (X 3 4) (Y 3 5))]
  have hp6_q9 : v55 = p6_q9 := by quad_vecbin hv55 with quadDualValMem, p6_q9, p6_q9_hi, p6_q9_lo
  subst hp6_q9
  denote_clear v 55 55
  denote_step_all v 56
  let p7_qa_hiRaw1 := toBitVecValue 64 #v[phRaw (X 0 5) (Y 0 1), phRaw (X 1 5) (Y 1 1), phRaw (X 2 5) (Y 2 1), phRaw (X 3 5) (Y 3 1), phRaw (X 0 5) (Y 0 4), phRaw (X 1 5) (Y 1 4), phRaw (X 2 5) (Y 2 4), phRaw (X 3 5) (Y 3 4)]
  have hp7_qa_hiRaw1 : v56 = p7_qa_hiRaw1 := by quad_madd52 hv56 with p7_qa_hiRaw1, x55
  subst hp7_qa_hiRaw1
  denote_clear v 56 56
  denote_step_all v 57
  let p7_qa_hiRaw := toBitVecValue 64 #v[phRaw (X 0 5) (Y 0 1) + phRaw (X 0 4) (Y 0 2), phRaw (X 1 5) (Y 1 1) + phRaw (X 1 4) (Y 1 2), phRaw (X 2 5) (Y 2 1) + phRaw (X 2 4) (Y 2 2), phRaw (X 3 5) (Y 3 1) + phRaw (X 3 4) (Y 3 2), phRaw (X 0 5) (Y 0 4) + phRaw (X 0 4) (Y 0 5), phRaw (X 1 5) (Y 1 4) + phRaw (X 1 4) (Y 1 5), phRaw (X 2 5) (Y 2 4) + phRaw (X 2 4) (Y 2 5), phRaw (X 3 5) (Y 3 4) + phRaw (X 3 4) (Y 3 5)]
  have hp7_qa_hiRaw : v57 = p7_qa_hiRaw := by quad_madd52 hv57 with p7_qa_hiRaw, p7_qa_hiRaw1, x44
  subst hp7_qa_hiRaw
  denote_clear v 57 57
  denote_step_all v 58
  let p7_qa_hi := toBitVecValue 64 #v[ph (X 0 5) (Y 0 1) + ph (X 0 4) (Y 0 2), ph (X 1 5) (Y 1 1) + ph (X 1 4) (Y 1 2), ph (X 2 5) (Y 2 1) + ph (X 2 4) (Y 2 2), ph (X 3 5) (Y 3 1) + ph (X 3 4) (Y 3 2), ph (X 0 5) (Y 0 4) + ph (X 0 4) (Y 0 5), ph (X 1 5) (Y 1 4) + ph (X 1 4) (Y 1 5), ph (X 2 5) (Y 2 4) + ph (X 2 4) (Y 2 5), ph (X 3 5) (Y 3 4) + ph (X 3 4) (Y 3 5)]
  have hp7_qa_hi : v58 = p7_qa_hi := by quad_vecbin_ring hv58 with quadDualValMem, p7_qa_hi, p7_qa_hiRaw
  subst hp7_qa_hi
  denote_clear v 58 58
  denote_step_all v 59
  let p7_qa := toBitVecValue 64 #v[(ph (X 0 5) (Y 0 1) + ph (X 0 4) (Y 0 2)) + (pl (X 0 5) (Y 0 2)), (ph (X 1 5) (Y 1 1) + ph (X 1 4) (Y 1 2)) + (pl (X 1 5) (Y 1 2)), (ph (X 2 5) (Y 2 1) + ph (X 2 4) (Y 2 2)) + (pl (X 2 5) (Y 2 2)), (ph (X 3 5) (Y 3 1) + ph (X 3 4) (Y 3 2)) + (pl (X 3 5) (Y 3 2)), (ph (X 0 5) (Y 0 4) + ph (X 0 4) (Y 0 5)) + (pl (X 0 5) (Y 0 5)), (ph (X 1 5) (Y 1 4) + ph (X 1 4) (Y 1 5)) + (pl (X 1 5) (Y 1 5)), (ph (X 2 5) (Y 2 4) + ph (X 2 4) (Y 2 5)) + (pl (X 2 5) (Y 2 5)), (ph (X 3 5) (Y 3 4) + ph (X 3 4) (Y 3 5)) + (pl (X 3 5) (Y 3 5))]
  have hp7_qa : v59 = p7_qa := by quad_vecbin hv59 with quadDualValMem, p7_qa, p7_qa_hi, p7_qa_lo
  subst hp7_qa
  denote_clear v 59 59
  denote_step_all v 60
  let p8_qb_hiRaw := toBitVecValue 64 #v[phRaw (X 0 5) (Y 0 2), phRaw (X 1 5) (Y 1 2), phRaw (X 2 5) (Y 2 2), phRaw (X 3 5) (Y 3 2), phRaw (X 0 5) (Y 0 5), phRaw (X 1 5) (Y 1 5), phRaw (X 2 5) (Y 2 5), phRaw (X 3 5) (Y 3 5)]
  have hp8_qb_hiRaw : v60 = p8_qb_hiRaw := by quad_madd52 hv60 with p8_qb_hiRaw, x55
  subst hp8_qb_hiRaw
  denote_clear v 60 60
  denote_step_all v 61
  let p8_qb := toBitVecValue 64 #v[ph (X 0 5) (Y 0 2), ph (X 1 5) (Y 1 2), ph (X 2 5) (Y 2 2), ph (X 3 5) (Y 3 2), ph (X 0 5) (Y 0 5), ph (X 1 5) (Y 1 5), ph (X 2 5) (Y 2 5), ph (X 3 5) (Y 3 5)]
  have hp8_qb : v61 = p8_qb := by quad_vecbin_ring hv61 with quadDualValMem, p8_qb, p8_qb_hiRaw
  subst hp8_qb
  denote_clear v 61 61

  -- q6_p3 .. q8_p5, then za/zb and the `za + 152*zb` fold
  denote_step_all v 62
  -- q6_p3: `p3_q6` with its halves swapped, so each column meets its other part
  let q6_p3 := toBitVecValue 64 #v[(ph (X 0 2) (Y 0 3) + ph (X 0 1) (Y 0 4) + ph (X 0 0) (Y 0 5)) + (pl (X 0 3) (Y 0 3) + pl (X 0 2) (Y 0 4) + pl (X 0 1) (Y 0 5)), (ph (X 1 2) (Y 1 3) + ph (X 1 1) (Y 1 4) + ph (X 1 0) (Y 1 5)) + (pl (X 1 3) (Y 1 3) + pl (X 1 2) (Y 1 4) + pl (X 1 1) (Y 1 5)), (ph (X 2 2) (Y 2 3) + ph (X 2 1) (Y 2 4) + ph (X 2 0) (Y 2 5)) + (pl (X 2 3) (Y 2 3) + pl (X 2 2) (Y 2 4) + pl (X 2 1) (Y 2 5)), (ph (X 3 2) (Y 3 3) + ph (X 3 1) (Y 3 4) + ph (X 3 0) (Y 3 5)) + (pl (X 3 3) (Y 3 3) + pl (X 3 2) (Y 3 4) + pl (X 3 1) (Y 3 5)), (ph (X 0 2) (Y 0 0) + ph (X 0 1) (Y 0 1) + ph (X 0 0) (Y 0 2)) + (pl (X 0 3) (Y 0 0) + pl (X 0 2) (Y 0 1) + pl (X 0 1) (Y 0 2)), (ph (X 1 2) (Y 1 0) + ph (X 1 1) (Y 1 1) + ph (X 1 0) (Y 1 2)) + (pl (X 1 3) (Y 1 0) + pl (X 1 2) (Y 1 1) + pl (X 1 1) (Y 1 2)), (ph (X 2 2) (Y 2 0) + ph (X 2 1) (Y 2 1) + ph (X 2 0) (Y 2 2)) + (pl (X 2 3) (Y 2 0) + pl (X 2 2) (Y 2 1) + pl (X 2 1) (Y 2 2)), (ph (X 3 2) (Y 3 0) + ph (X 3 1) (Y 3 1) + ph (X 3 0) (Y 3 2)) + (pl (X 3 3) (Y 3 0) + pl (X 3 2) (Y 3 1) + pl (X 3 1) (Y 3 2))]
  have hq6_p3 : v62 = q6_p3 := by quad_shuffle hv62 with p3_q6, q6_p3
  subst hq6_p3
  denote_clear v 62 62
  denote_step_all v 63
  -- q7_p4: `p4_q7` with its halves swapped
  let q7_p4 := toBitVecValue 64 #v[(ph (X 0 3) (Y 0 3) + ph (X 0 2) (Y 0 4) + ph (X 0 1) (Y 0 5)) + (pl (X 0 4) (Y 0 3) + pl (X 0 3) (Y 0 4) + pl (X 0 2) (Y 0 5)), (ph (X 1 3) (Y 1 3) + ph (X 1 2) (Y 1 4) + ph (X 1 1) (Y 1 5)) + (pl (X 1 4) (Y 1 3) + pl (X 1 3) (Y 1 4) + pl (X 1 2) (Y 1 5)), (ph (X 2 3) (Y 2 3) + ph (X 2 2) (Y 2 4) + ph (X 2 1) (Y 2 5)) + (pl (X 2 4) (Y 2 3) + pl (X 2 3) (Y 2 4) + pl (X 2 2) (Y 2 5)), (ph (X 3 3) (Y 3 3) + ph (X 3 2) (Y 3 4) + ph (X 3 1) (Y 3 5)) + (pl (X 3 4) (Y 3 3) + pl (X 3 3) (Y 3 4) + pl (X 3 2) (Y 3 5)), (ph (X 0 3) (Y 0 0) + ph (X 0 2) (Y 0 1) + ph (X 0 1) (Y 0 2)) + (pl (X 0 4) (Y 0 0) + pl (X 0 3) (Y 0 1) + pl (X 0 2) (Y 0 2)), (ph (X 1 3) (Y 1 0) + ph (X 1 2) (Y 1 1) + ph (X 1 1) (Y 1 2)) + (pl (X 1 4) (Y 1 0) + pl (X 1 3) (Y 1 1) + pl (X 1 2) (Y 1 2)), (ph (X 2 3) (Y 2 0) + ph (X 2 2) (Y 2 1) + ph (X 2 1) (Y 2 2)) + (pl (X 2 4) (Y 2 0) + pl (X 2 3) (Y 2 1) + pl (X 2 2) (Y 2 2)), (ph (X 3 3) (Y 3 0) + ph (X 3 2) (Y 3 1) + ph (X 3 1) (Y 3 2)) + (pl (X 3 4) (Y 3 0) + pl (X 3 3) (Y 3 1) + pl (X 3 2) (Y 3 2))]
  have hq7_p4 : v63 = q7_p4 := by quad_shuffle hv63 with p4_q7, q7_p4
  subst hq7_p4
  denote_clear v 63 63
  denote_step_all v 64
  -- q8_p5: `p5_q8` with its halves swapped
  let q8_p5 := toBitVecValue 64 #v[(ph (X 0 4) (Y 0 3) + ph (X 0 3) (Y 0 4) + ph (X 0 2) (Y 0 5)) + (pl (X 0 5) (Y 0 3) + pl (X 0 4) (Y 0 4) + pl (X 0 3) (Y 0 5)), (ph (X 1 4) (Y 1 3) + ph (X 1 3) (Y 1 4) + ph (X 1 2) (Y 1 5)) + (pl (X 1 5) (Y 1 3) + pl (X 1 4) (Y 1 4) + pl (X 1 3) (Y 1 5)), (ph (X 2 4) (Y 2 3) + ph (X 2 3) (Y 2 4) + ph (X 2 2) (Y 2 5)) + (pl (X 2 5) (Y 2 3) + pl (X 2 4) (Y 2 4) + pl (X 2 3) (Y 2 5)), (ph (X 3 4) (Y 3 3) + ph (X 3 3) (Y 3 4) + ph (X 3 2) (Y 3 5)) + (pl (X 3 5) (Y 3 3) + pl (X 3 4) (Y 3 4) + pl (X 3 3) (Y 3 5)), (ph (X 0 4) (Y 0 0) + ph (X 0 3) (Y 0 1) + ph (X 0 2) (Y 0 2)) + (pl (X 0 5) (Y 0 0) + pl (X 0 4) (Y 0 1) + pl (X 0 3) (Y 0 2)), (ph (X 1 4) (Y 1 0) + ph (X 1 3) (Y 1 1) + ph (X 1 2) (Y 1 2)) + (pl (X 1 5) (Y 1 0) + pl (X 1 4) (Y 1 1) + pl (X 1 3) (Y 1 2)), (ph (X 2 4) (Y 2 0) + ph (X 2 3) (Y 2 1) + ph (X 2 2) (Y 2 2)) + (pl (X 2 5) (Y 2 0) + pl (X 2 4) (Y 2 1) + pl (X 2 3) (Y 2 2)), (ph (X 3 4) (Y 3 0) + ph (X 3 3) (Y 3 1) + ph (X 3 2) (Y 3 2)) + (pl (X 3 5) (Y 3 0) + pl (X 3 4) (Y 3 1) + pl (X 3 3) (Y 3 2))]
  have hq8_p5 : v64 = q8_p5 := by quad_shuffle hv64 with p5_q8, q8_p5
  subst hq8_p5
  denote_clear v 64 64
  denote_step_all v 65
  let za03_add := toBitVecValue 64 #v[((ph (X 0 2) (Y 0 3) + ph (X 0 1) (Y 0 4) + ph (X 0 0) (Y 0 5)) + (pl (X 0 3) (Y 0 3) + pl (X 0 2) (Y 0 4) + pl (X 0 1) (Y 0 5))) + (pl (X 0 0) (Y 0 0)), ((ph (X 1 2) (Y 1 3) + ph (X 1 1) (Y 1 4) + ph (X 1 0) (Y 1 5)) + (pl (X 1 3) (Y 1 3) + pl (X 1 2) (Y 1 4) + pl (X 1 1) (Y 1 5))) + (pl (X 1 0) (Y 1 0)), ((ph (X 2 2) (Y 2 3) + ph (X 2 1) (Y 2 4) + ph (X 2 0) (Y 2 5)) + (pl (X 2 3) (Y 2 3) + pl (X 2 2) (Y 2 4) + pl (X 2 1) (Y 2 5))) + (pl (X 2 0) (Y 2 0)), ((ph (X 3 2) (Y 3 3) + ph (X 3 1) (Y 3 4) + ph (X 3 0) (Y 3 5)) + (pl (X 3 3) (Y 3 3) + pl (X 3 2) (Y 3 4) + pl (X 3 1) (Y 3 5))) + (pl (X 3 0) (Y 3 0)), ((ph (X 0 2) (Y 0 0) + ph (X 0 1) (Y 0 1) + ph (X 0 0) (Y 0 2)) + (pl (X 0 3) (Y 0 0) + pl (X 0 2) (Y 0 1) + pl (X 0 1) (Y 0 2))) + (pl (X 0 0) (Y 0 3)), ((ph (X 1 2) (Y 1 0) + ph (X 1 1) (Y 1 1) + ph (X 1 0) (Y 1 2)) + (pl (X 1 3) (Y 1 0) + pl (X 1 2) (Y 1 1) + pl (X 1 1) (Y 1 2))) + (pl (X 1 0) (Y 1 3)), ((ph (X 2 2) (Y 2 0) + ph (X 2 1) (Y 2 1) + ph (X 2 0) (Y 2 2)) + (pl (X 2 3) (Y 2 0) + pl (X 2 2) (Y 2 1) + pl (X 2 1) (Y 2 2))) + (pl (X 2 0) (Y 2 3)), ((ph (X 3 2) (Y 3 0) + ph (X 3 1) (Y 3 1) + ph (X 3 0) (Y 3 2)) + (pl (X 3 3) (Y 3 0) + pl (X 3 2) (Y 3 1) + pl (X 3 1) (Y 3 2))) + (pl (X 3 0) (Y 3 3))]
  have hza03_add : v65 = za03_add := by quad_vecbin hv65 with quadDualValMem, p0_q3, q6_p3, za03_add
  subst hza03_add
  denote_clear v 65 65
  denote_step_all v 66
  -- za03: columns 0 and 3, the `wwv_add_if( 0xF0, ... )` blend
  let za03 := toBitVecValue 64 #v[pl (X 0 0) (Y 0 0), pl (X 1 0) (Y 1 0), pl (X 2 0) (Y 2 0), pl (X 3 0) (Y 3 0), ((ph (X 0 2) (Y 0 0) + ph (X 0 1) (Y 0 1) + ph (X 0 0) (Y 0 2)) + (pl (X 0 3) (Y 0 0) + pl (X 0 2) (Y 0 1) + pl (X 0 1) (Y 0 2))) + (pl (X 0 0) (Y 0 3)), ((ph (X 1 2) (Y 1 0) + ph (X 1 1) (Y 1 1) + ph (X 1 0) (Y 1 2)) + (pl (X 1 3) (Y 1 0) + pl (X 1 2) (Y 1 1) + pl (X 1 1) (Y 1 2))) + (pl (X 1 0) (Y 1 3)), ((ph (X 2 2) (Y 2 0) + ph (X 2 1) (Y 2 1) + ph (X 2 0) (Y 2 2)) + (pl (X 2 3) (Y 2 0) + pl (X 2 2) (Y 2 1) + pl (X 2 1) (Y 2 2))) + (pl (X 2 0) (Y 2 3)), ((ph (X 3 2) (Y 3 0) + ph (X 3 1) (Y 3 1) + ph (X 3 0) (Y 3 2)) + (pl (X 3 3) (Y 3 0) + pl (X 3 2) (Y 3 1) + pl (X 3 1) (Y 3 2))) + (pl (X 3 0) (Y 3 3))]
  have hza03 : v66 = za03 := by quad_shuffle hv66 with p0_q3, za03, za03_add
  subst hza03
  denote_clear v 66 66
  denote_step_all v 67
  let za14_add := toBitVecValue 64 #v[((ph (X 0 3) (Y 0 3) + ph (X 0 2) (Y 0 4) + ph (X 0 1) (Y 0 5)) + (pl (X 0 4) (Y 0 3) + pl (X 0 3) (Y 0 4) + pl (X 0 2) (Y 0 5))) + ((ph (X 0 0) (Y 0 0)) + (pl (X 0 1) (Y 0 0) + pl (X 0 0) (Y 0 1))), ((ph (X 1 3) (Y 1 3) + ph (X 1 2) (Y 1 4) + ph (X 1 1) (Y 1 5)) + (pl (X 1 4) (Y 1 3) + pl (X 1 3) (Y 1 4) + pl (X 1 2) (Y 1 5))) + ((ph (X 1 0) (Y 1 0)) + (pl (X 1 1) (Y 1 0) + pl (X 1 0) (Y 1 1))), ((ph (X 2 3) (Y 2 3) + ph (X 2 2) (Y 2 4) + ph (X 2 1) (Y 2 5)) + (pl (X 2 4) (Y 2 3) + pl (X 2 3) (Y 2 4) + pl (X 2 2) (Y 2 5))) + ((ph (X 2 0) (Y 2 0)) + (pl (X 2 1) (Y 2 0) + pl (X 2 0) (Y 2 1))), ((ph (X 3 3) (Y 3 3) + ph (X 3 2) (Y 3 4) + ph (X 3 1) (Y 3 5)) + (pl (X 3 4) (Y 3 3) + pl (X 3 3) (Y 3 4) + pl (X 3 2) (Y 3 5))) + ((ph (X 3 0) (Y 3 0)) + (pl (X 3 1) (Y 3 0) + pl (X 3 0) (Y 3 1))), ((ph (X 0 3) (Y 0 0) + ph (X 0 2) (Y 0 1) + ph (X 0 1) (Y 0 2)) + (pl (X 0 4) (Y 0 0) + pl (X 0 3) (Y 0 1) + pl (X 0 2) (Y 0 2))) + ((ph (X 0 0) (Y 0 3)) + (pl (X 0 1) (Y 0 3) + pl (X 0 0) (Y 0 4))), ((ph (X 1 3) (Y 1 0) + ph (X 1 2) (Y 1 1) + ph (X 1 1) (Y 1 2)) + (pl (X 1 4) (Y 1 0) + pl (X 1 3) (Y 1 1) + pl (X 1 2) (Y 1 2))) + ((ph (X 1 0) (Y 1 3)) + (pl (X 1 1) (Y 1 3) + pl (X 1 0) (Y 1 4))), ((ph (X 2 3) (Y 2 0) + ph (X 2 2) (Y 2 1) + ph (X 2 1) (Y 2 2)) + (pl (X 2 4) (Y 2 0) + pl (X 2 3) (Y 2 1) + pl (X 2 2) (Y 2 2))) + ((ph (X 2 0) (Y 2 3)) + (pl (X 2 1) (Y 2 3) + pl (X 2 0) (Y 2 4))), ((ph (X 3 3) (Y 3 0) + ph (X 3 2) (Y 3 1) + ph (X 3 1) (Y 3 2)) + (pl (X 3 4) (Y 3 0) + pl (X 3 3) (Y 3 1) + pl (X 3 2) (Y 3 2))) + ((ph (X 3 0) (Y 3 3)) + (pl (X 3 1) (Y 3 3) + pl (X 3 0) (Y 3 4)))]
  have hza14_add : v67 = za14_add := by quad_vecbin hv67 with quadDualValMem, p1_q4, q7_p4, za14_add
  subst hza14_add
  denote_clear v 67 67
  denote_step_all v 68
  -- za14: columns 1 and 4
  let za14 := toBitVecValue 64 #v[(ph (X 0 0) (Y 0 0)) + (pl (X 0 1) (Y 0 0) + pl (X 0 0) (Y 0 1)), (ph (X 1 0) (Y 1 0)) + (pl (X 1 1) (Y 1 0) + pl (X 1 0) (Y 1 1)), (ph (X 2 0) (Y 2 0)) + (pl (X 2 1) (Y 2 0) + pl (X 2 0) (Y 2 1)), (ph (X 3 0) (Y 3 0)) + (pl (X 3 1) (Y 3 0) + pl (X 3 0) (Y 3 1)), ((ph (X 0 3) (Y 0 0) + ph (X 0 2) (Y 0 1) + ph (X 0 1) (Y 0 2)) + (pl (X 0 4) (Y 0 0) + pl (X 0 3) (Y 0 1) + pl (X 0 2) (Y 0 2))) + ((ph (X 0 0) (Y 0 3)) + (pl (X 0 1) (Y 0 3) + pl (X 0 0) (Y 0 4))), ((ph (X 1 3) (Y 1 0) + ph (X 1 2) (Y 1 1) + ph (X 1 1) (Y 1 2)) + (pl (X 1 4) (Y 1 0) + pl (X 1 3) (Y 1 1) + pl (X 1 2) (Y 1 2))) + ((ph (X 1 0) (Y 1 3)) + (pl (X 1 1) (Y 1 3) + pl (X 1 0) (Y 1 4))), ((ph (X 2 3) (Y 2 0) + ph (X 2 2) (Y 2 1) + ph (X 2 1) (Y 2 2)) + (pl (X 2 4) (Y 2 0) + pl (X 2 3) (Y 2 1) + pl (X 2 2) (Y 2 2))) + ((ph (X 2 0) (Y 2 3)) + (pl (X 2 1) (Y 2 3) + pl (X 2 0) (Y 2 4))), ((ph (X 3 3) (Y 3 0) + ph (X 3 2) (Y 3 1) + ph (X 3 1) (Y 3 2)) + (pl (X 3 4) (Y 3 0) + pl (X 3 3) (Y 3 1) + pl (X 3 2) (Y 3 2))) + ((ph (X 3 0) (Y 3 3)) + (pl (X 3 1) (Y 3 3) + pl (X 3 0) (Y 3 4)))]
  have hza14 : v68 = za14 := by quad_shuffle hv68 with p1_q4, za14, za14_add
  subst hza14
  denote_clear v 68 68
  denote_step_all v 69
  let za25_add := toBitVecValue 64 #v[((ph (X 0 4) (Y 0 3) + ph (X 0 3) (Y 0 4) + ph (X 0 2) (Y 0 5)) + (pl (X 0 5) (Y 0 3) + pl (X 0 4) (Y 0 4) + pl (X 0 3) (Y 0 5))) + ((ph (X 0 1) (Y 0 0) + ph (X 0 0) (Y 0 1)) + (pl (X 0 2) (Y 0 0) + pl (X 0 1) (Y 0 1) + pl (X 0 0) (Y 0 2))), ((ph (X 1 4) (Y 1 3) + ph (X 1 3) (Y 1 4) + ph (X 1 2) (Y 1 5)) + (pl (X 1 5) (Y 1 3) + pl (X 1 4) (Y 1 4) + pl (X 1 3) (Y 1 5))) + ((ph (X 1 1) (Y 1 0) + ph (X 1 0) (Y 1 1)) + (pl (X 1 2) (Y 1 0) + pl (X 1 1) (Y 1 1) + pl (X 1 0) (Y 1 2))), ((ph (X 2 4) (Y 2 3) + ph (X 2 3) (Y 2 4) + ph (X 2 2) (Y 2 5)) + (pl (X 2 5) (Y 2 3) + pl (X 2 4) (Y 2 4) + pl (X 2 3) (Y 2 5))) + ((ph (X 2 1) (Y 2 0) + ph (X 2 0) (Y 2 1)) + (pl (X 2 2) (Y 2 0) + pl (X 2 1) (Y 2 1) + pl (X 2 0) (Y 2 2))), ((ph (X 3 4) (Y 3 3) + ph (X 3 3) (Y 3 4) + ph (X 3 2) (Y 3 5)) + (pl (X 3 5) (Y 3 3) + pl (X 3 4) (Y 3 4) + pl (X 3 3) (Y 3 5))) + ((ph (X 3 1) (Y 3 0) + ph (X 3 0) (Y 3 1)) + (pl (X 3 2) (Y 3 0) + pl (X 3 1) (Y 3 1) + pl (X 3 0) (Y 3 2))), ((ph (X 0 4) (Y 0 0) + ph (X 0 3) (Y 0 1) + ph (X 0 2) (Y 0 2)) + (pl (X 0 5) (Y 0 0) + pl (X 0 4) (Y 0 1) + pl (X 0 3) (Y 0 2))) + ((ph (X 0 1) (Y 0 3) + ph (X 0 0) (Y 0 4)) + (pl (X 0 2) (Y 0 3) + pl (X 0 1) (Y 0 4) + pl (X 0 0) (Y 0 5))), ((ph (X 1 4) (Y 1 0) + ph (X 1 3) (Y 1 1) + ph (X 1 2) (Y 1 2)) + (pl (X 1 5) (Y 1 0) + pl (X 1 4) (Y 1 1) + pl (X 1 3) (Y 1 2))) + ((ph (X 1 1) (Y 1 3) + ph (X 1 0) (Y 1 4)) + (pl (X 1 2) (Y 1 3) + pl (X 1 1) (Y 1 4) + pl (X 1 0) (Y 1 5))), ((ph (X 2 4) (Y 2 0) + ph (X 2 3) (Y 2 1) + ph (X 2 2) (Y 2 2)) + (pl (X 2 5) (Y 2 0) + pl (X 2 4) (Y 2 1) + pl (X 2 3) (Y 2 2))) + ((ph (X 2 1) (Y 2 3) + ph (X 2 0) (Y 2 4)) + (pl (X 2 2) (Y 2 3) + pl (X 2 1) (Y 2 4) + pl (X 2 0) (Y 2 5))), ((ph (X 3 4) (Y 3 0) + ph (X 3 3) (Y 3 1) + ph (X 3 2) (Y 3 2)) + (pl (X 3 5) (Y 3 0) + pl (X 3 4) (Y 3 1) + pl (X 3 3) (Y 3 2))) + ((ph (X 3 1) (Y 3 3) + ph (X 3 0) (Y 3 4)) + (pl (X 3 2) (Y 3 3) + pl (X 3 1) (Y 3 4) + pl (X 3 0) (Y 3 5)))]
  have hza25_add : v69 = za25_add := by quad_vecbin hv69 with quadDualValMem, p2_q5, q8_p5, za25_add
  subst hza25_add
  denote_clear v 69 69
  denote_step_all v 70
  -- za25: columns 2 and 5
  let za25 := toBitVecValue 64 #v[(ph (X 0 1) (Y 0 0) + ph (X 0 0) (Y 0 1)) + (pl (X 0 2) (Y 0 0) + pl (X 0 1) (Y 0 1) + pl (X 0 0) (Y 0 2)), (ph (X 1 1) (Y 1 0) + ph (X 1 0) (Y 1 1)) + (pl (X 1 2) (Y 1 0) + pl (X 1 1) (Y 1 1) + pl (X 1 0) (Y 1 2)), (ph (X 2 1) (Y 2 0) + ph (X 2 0) (Y 2 1)) + (pl (X 2 2) (Y 2 0) + pl (X 2 1) (Y 2 1) + pl (X 2 0) (Y 2 2)), (ph (X 3 1) (Y 3 0) + ph (X 3 0) (Y 3 1)) + (pl (X 3 2) (Y 3 0) + pl (X 3 1) (Y 3 1) + pl (X 3 0) (Y 3 2)), ((ph (X 0 4) (Y 0 0) + ph (X 0 3) (Y 0 1) + ph (X 0 2) (Y 0 2)) + (pl (X 0 5) (Y 0 0) + pl (X 0 4) (Y 0 1) + pl (X 0 3) (Y 0 2))) + ((ph (X 0 1) (Y 0 3) + ph (X 0 0) (Y 0 4)) + (pl (X 0 2) (Y 0 3) + pl (X 0 1) (Y 0 4) + pl (X 0 0) (Y 0 5))), ((ph (X 1 4) (Y 1 0) + ph (X 1 3) (Y 1 1) + ph (X 1 2) (Y 1 2)) + (pl (X 1 5) (Y 1 0) + pl (X 1 4) (Y 1 1) + pl (X 1 3) (Y 1 2))) + ((ph (X 1 1) (Y 1 3) + ph (X 1 0) (Y 1 4)) + (pl (X 1 2) (Y 1 3) + pl (X 1 1) (Y 1 4) + pl (X 1 0) (Y 1 5))), ((ph (X 2 4) (Y 2 0) + ph (X 2 3) (Y 2 1) + ph (X 2 2) (Y 2 2)) + (pl (X 2 5) (Y 2 0) + pl (X 2 4) (Y 2 1) + pl (X 2 3) (Y 2 2))) + ((ph (X 2 1) (Y 2 3) + ph (X 2 0) (Y 2 4)) + (pl (X 2 2) (Y 2 3) + pl (X 2 1) (Y 2 4) + pl (X 2 0) (Y 2 5))), ((ph (X 3 4) (Y 3 0) + ph (X 3 3) (Y 3 1) + ph (X 3 2) (Y 3 2)) + (pl (X 3 5) (Y 3 0) + pl (X 3 4) (Y 3 1) + pl (X 3 3) (Y 3 2))) + ((ph (X 3 1) (Y 3 3) + ph (X 3 0) (Y 3 4)) + (pl (X 3 2) (Y 3 3) + pl (X 3 1) (Y 3 4) + pl (X 3 0) (Y 3 5)))]
  have hza25 : v70 = za25 := by quad_shuffle hv70 with p2_q5, za25, za25_add
  subst hza25
  denote_clear v 70 70
  denote_step_all v 71
  let zb03_add := toBitVecValue 64 #v[((ph (X 0 5) (Y 0 0) + ph (X 0 4) (Y 0 1) + ph (X 0 3) (Y 0 2)) + (pl (X 0 5) (Y 0 1) + pl (X 0 4) (Y 0 2))) + ((ph (X 0 2) (Y 0 3) + ph (X 0 1) (Y 0 4) + ph (X 0 0) (Y 0 5)) + (pl (X 0 3) (Y 0 3) + pl (X 0 2) (Y 0 4) + pl (X 0 1) (Y 0 5))), ((ph (X 1 5) (Y 1 0) + ph (X 1 4) (Y 1 1) + ph (X 1 3) (Y 1 2)) + (pl (X 1 5) (Y 1 1) + pl (X 1 4) (Y 1 2))) + ((ph (X 1 2) (Y 1 3) + ph (X 1 1) (Y 1 4) + ph (X 1 0) (Y 1 5)) + (pl (X 1 3) (Y 1 3) + pl (X 1 2) (Y 1 4) + pl (X 1 1) (Y 1 5))), ((ph (X 2 5) (Y 2 0) + ph (X 2 4) (Y 2 1) + ph (X 2 3) (Y 2 2)) + (pl (X 2 5) (Y 2 1) + pl (X 2 4) (Y 2 2))) + ((ph (X 2 2) (Y 2 3) + ph (X 2 1) (Y 2 4) + ph (X 2 0) (Y 2 5)) + (pl (X 2 3) (Y 2 3) + pl (X 2 2) (Y 2 4) + pl (X 2 1) (Y 2 5))), ((ph (X 3 5) (Y 3 0) + ph (X 3 4) (Y 3 1) + ph (X 3 3) (Y 3 2)) + (pl (X 3 5) (Y 3 1) + pl (X 3 4) (Y 3 2))) + ((ph (X 3 2) (Y 3 3) + ph (X 3 1) (Y 3 4) + ph (X 3 0) (Y 3 5)) + (pl (X 3 3) (Y 3 3) + pl (X 3 2) (Y 3 4) + pl (X 3 1) (Y 3 5))), ((ph (X 0 5) (Y 0 3) + ph (X 0 4) (Y 0 4) + ph (X 0 3) (Y 0 5)) + (pl (X 0 5) (Y 0 4) + pl (X 0 4) (Y 0 5))) + ((ph (X 0 2) (Y 0 0) + ph (X 0 1) (Y 0 1) + ph (X 0 0) (Y 0 2)) + (pl (X 0 3) (Y 0 0) + pl (X 0 2) (Y 0 1) + pl (X 0 1) (Y 0 2))), ((ph (X 1 5) (Y 1 3) + ph (X 1 4) (Y 1 4) + ph (X 1 3) (Y 1 5)) + (pl (X 1 5) (Y 1 4) + pl (X 1 4) (Y 1 5))) + ((ph (X 1 2) (Y 1 0) + ph (X 1 1) (Y 1 1) + ph (X 1 0) (Y 1 2)) + (pl (X 1 3) (Y 1 0) + pl (X 1 2) (Y 1 1) + pl (X 1 1) (Y 1 2))), ((ph (X 2 5) (Y 2 3) + ph (X 2 4) (Y 2 4) + ph (X 2 3) (Y 2 5)) + (pl (X 2 5) (Y 2 4) + pl (X 2 4) (Y 2 5))) + ((ph (X 2 2) (Y 2 0) + ph (X 2 1) (Y 2 1) + ph (X 2 0) (Y 2 2)) + (pl (X 2 3) (Y 2 0) + pl (X 2 2) (Y 2 1) + pl (X 2 1) (Y 2 2))), ((ph (X 3 5) (Y 3 3) + ph (X 3 4) (Y 3 4) + ph (X 3 3) (Y 3 5)) + (pl (X 3 5) (Y 3 4) + pl (X 3 4) (Y 3 5))) + ((ph (X 3 2) (Y 3 0) + ph (X 3 1) (Y 3 1) + ph (X 3 0) (Y 3 2)) + (pl (X 3 3) (Y 3 0) + pl (X 3 2) (Y 3 1) + pl (X 3 1) (Y 3 2)))]
  have hzb03_add : v71 = zb03_add := by quad_vecbin hv71 with quadDualValMem, p6_q9, q6_p3, zb03_add
  subst hzb03_add
  denote_clear v 71 71
  denote_step_all v 72
  -- zb03: columns 6 and 9, the `wwv_add_if( 0x0F, ... )` blend
  let zb03 := toBitVecValue 64 #v[((ph (X 0 5) (Y 0 0) + ph (X 0 4) (Y 0 1) + ph (X 0 3) (Y 0 2)) + (pl (X 0 5) (Y 0 1) + pl (X 0 4) (Y 0 2))) + ((ph (X 0 2) (Y 0 3) + ph (X 0 1) (Y 0 4) + ph (X 0 0) (Y 0 5)) + (pl (X 0 3) (Y 0 3) + pl (X 0 2) (Y 0 4) + pl (X 0 1) (Y 0 5))), ((ph (X 1 5) (Y 1 0) + ph (X 1 4) (Y 1 1) + ph (X 1 3) (Y 1 2)) + (pl (X 1 5) (Y 1 1) + pl (X 1 4) (Y 1 2))) + ((ph (X 1 2) (Y 1 3) + ph (X 1 1) (Y 1 4) + ph (X 1 0) (Y 1 5)) + (pl (X 1 3) (Y 1 3) + pl (X 1 2) (Y 1 4) + pl (X 1 1) (Y 1 5))), ((ph (X 2 5) (Y 2 0) + ph (X 2 4) (Y 2 1) + ph (X 2 3) (Y 2 2)) + (pl (X 2 5) (Y 2 1) + pl (X 2 4) (Y 2 2))) + ((ph (X 2 2) (Y 2 3) + ph (X 2 1) (Y 2 4) + ph (X 2 0) (Y 2 5)) + (pl (X 2 3) (Y 2 3) + pl (X 2 2) (Y 2 4) + pl (X 2 1) (Y 2 5))), ((ph (X 3 5) (Y 3 0) + ph (X 3 4) (Y 3 1) + ph (X 3 3) (Y 3 2)) + (pl (X 3 5) (Y 3 1) + pl (X 3 4) (Y 3 2))) + ((ph (X 3 2) (Y 3 3) + ph (X 3 1) (Y 3 4) + ph (X 3 0) (Y 3 5)) + (pl (X 3 3) (Y 3 3) + pl (X 3 2) (Y 3 4) + pl (X 3 1) (Y 3 5))), (ph (X 0 5) (Y 0 3) + ph (X 0 4) (Y 0 4) + ph (X 0 3) (Y 0 5)) + (pl (X 0 5) (Y 0 4) + pl (X 0 4) (Y 0 5)), (ph (X 1 5) (Y 1 3) + ph (X 1 4) (Y 1 4) + ph (X 1 3) (Y 1 5)) + (pl (X 1 5) (Y 1 4) + pl (X 1 4) (Y 1 5)), (ph (X 2 5) (Y 2 3) + ph (X 2 4) (Y 2 4) + ph (X 2 3) (Y 2 5)) + (pl (X 2 5) (Y 2 4) + pl (X 2 4) (Y 2 5)), (ph (X 3 5) (Y 3 3) + ph (X 3 4) (Y 3 4) + ph (X 3 3) (Y 3 5)) + (pl (X 3 5) (Y 3 4) + pl (X 3 4) (Y 3 5))]
  have hzb03 : v72 = zb03 := by quad_shuffle hv72 with p6_q9, zb03, zb03_add
  subst hzb03
  denote_clear v 72 72
  denote_step_all v 73
  let zb14_add := toBitVecValue 64 #v[((ph (X 0 5) (Y 0 1) + ph (X 0 4) (Y 0 2)) + (pl (X 0 5) (Y 0 2))) + ((ph (X 0 3) (Y 0 3) + ph (X 0 2) (Y 0 4) + ph (X 0 1) (Y 0 5)) + (pl (X 0 4) (Y 0 3) + pl (X 0 3) (Y 0 4) + pl (X 0 2) (Y 0 5))), ((ph (X 1 5) (Y 1 1) + ph (X 1 4) (Y 1 2)) + (pl (X 1 5) (Y 1 2))) + ((ph (X 1 3) (Y 1 3) + ph (X 1 2) (Y 1 4) + ph (X 1 1) (Y 1 5)) + (pl (X 1 4) (Y 1 3) + pl (X 1 3) (Y 1 4) + pl (X 1 2) (Y 1 5))), ((ph (X 2 5) (Y 2 1) + ph (X 2 4) (Y 2 2)) + (pl (X 2 5) (Y 2 2))) + ((ph (X 2 3) (Y 2 3) + ph (X 2 2) (Y 2 4) + ph (X 2 1) (Y 2 5)) + (pl (X 2 4) (Y 2 3) + pl (X 2 3) (Y 2 4) + pl (X 2 2) (Y 2 5))), ((ph (X 3 5) (Y 3 1) + ph (X 3 4) (Y 3 2)) + (pl (X 3 5) (Y 3 2))) + ((ph (X 3 3) (Y 3 3) + ph (X 3 2) (Y 3 4) + ph (X 3 1) (Y 3 5)) + (pl (X 3 4) (Y 3 3) + pl (X 3 3) (Y 3 4) + pl (X 3 2) (Y 3 5))), ((ph (X 0 5) (Y 0 4) + ph (X 0 4) (Y 0 5)) + (pl (X 0 5) (Y 0 5))) + ((ph (X 0 3) (Y 0 0) + ph (X 0 2) (Y 0 1) + ph (X 0 1) (Y 0 2)) + (pl (X 0 4) (Y 0 0) + pl (X 0 3) (Y 0 1) + pl (X 0 2) (Y 0 2))), ((ph (X 1 5) (Y 1 4) + ph (X 1 4) (Y 1 5)) + (pl (X 1 5) (Y 1 5))) + ((ph (X 1 3) (Y 1 0) + ph (X 1 2) (Y 1 1) + ph (X 1 1) (Y 1 2)) + (pl (X 1 4) (Y 1 0) + pl (X 1 3) (Y 1 1) + pl (X 1 2) (Y 1 2))), ((ph (X 2 5) (Y 2 4) + ph (X 2 4) (Y 2 5)) + (pl (X 2 5) (Y 2 5))) + ((ph (X 2 3) (Y 2 0) + ph (X 2 2) (Y 2 1) + ph (X 2 1) (Y 2 2)) + (pl (X 2 4) (Y 2 0) + pl (X 2 3) (Y 2 1) + pl (X 2 2) (Y 2 2))), ((ph (X 3 5) (Y 3 4) + ph (X 3 4) (Y 3 5)) + (pl (X 3 5) (Y 3 5))) + ((ph (X 3 3) (Y 3 0) + ph (X 3 2) (Y 3 1) + ph (X 3 1) (Y 3 2)) + (pl (X 3 4) (Y 3 0) + pl (X 3 3) (Y 3 1) + pl (X 3 2) (Y 3 2)))]
  have hzb14_add : v73 = zb14_add := by quad_vecbin hv73 with quadDualValMem, p7_qa, q7_p4, zb14_add
  subst hzb14_add
  denote_clear v 73 73
  denote_step_all v 74
  -- zb14: columns 7 and 10
  let zb14 := toBitVecValue 64 #v[((ph (X 0 5) (Y 0 1) + ph (X 0 4) (Y 0 2)) + (pl (X 0 5) (Y 0 2))) + ((ph (X 0 3) (Y 0 3) + ph (X 0 2) (Y 0 4) + ph (X 0 1) (Y 0 5)) + (pl (X 0 4) (Y 0 3) + pl (X 0 3) (Y 0 4) + pl (X 0 2) (Y 0 5))), ((ph (X 1 5) (Y 1 1) + ph (X 1 4) (Y 1 2)) + (pl (X 1 5) (Y 1 2))) + ((ph (X 1 3) (Y 1 3) + ph (X 1 2) (Y 1 4) + ph (X 1 1) (Y 1 5)) + (pl (X 1 4) (Y 1 3) + pl (X 1 3) (Y 1 4) + pl (X 1 2) (Y 1 5))), ((ph (X 2 5) (Y 2 1) + ph (X 2 4) (Y 2 2)) + (pl (X 2 5) (Y 2 2))) + ((ph (X 2 3) (Y 2 3) + ph (X 2 2) (Y 2 4) + ph (X 2 1) (Y 2 5)) + (pl (X 2 4) (Y 2 3) + pl (X 2 3) (Y 2 4) + pl (X 2 2) (Y 2 5))), ((ph (X 3 5) (Y 3 1) + ph (X 3 4) (Y 3 2)) + (pl (X 3 5) (Y 3 2))) + ((ph (X 3 3) (Y 3 3) + ph (X 3 2) (Y 3 4) + ph (X 3 1) (Y 3 5)) + (pl (X 3 4) (Y 3 3) + pl (X 3 3) (Y 3 4) + pl (X 3 2) (Y 3 5))), (ph (X 0 5) (Y 0 4) + ph (X 0 4) (Y 0 5)) + (pl (X 0 5) (Y 0 5)), (ph (X 1 5) (Y 1 4) + ph (X 1 4) (Y 1 5)) + (pl (X 1 5) (Y 1 5)), (ph (X 2 5) (Y 2 4) + ph (X 2 4) (Y 2 5)) + (pl (X 2 5) (Y 2 5)), (ph (X 3 5) (Y 3 4) + ph (X 3 4) (Y 3 5)) + (pl (X 3 5) (Y 3 5))]
  have hzb14 : v74 = zb14 := by quad_shuffle hv74 with p7_qa, zb14, zb14_add
  subst hzb14
  denote_clear v 74 74
  denote_step_all v 75
  let zb25_add := toBitVecValue 64 #v[(ph (X 0 5) (Y 0 2)) + ((ph (X 0 4) (Y 0 3) + ph (X 0 3) (Y 0 4) + ph (X 0 2) (Y 0 5)) + (pl (X 0 5) (Y 0 3) + pl (X 0 4) (Y 0 4) + pl (X 0 3) (Y 0 5))), (ph (X 1 5) (Y 1 2)) + ((ph (X 1 4) (Y 1 3) + ph (X 1 3) (Y 1 4) + ph (X 1 2) (Y 1 5)) + (pl (X 1 5) (Y 1 3) + pl (X 1 4) (Y 1 4) + pl (X 1 3) (Y 1 5))), (ph (X 2 5) (Y 2 2)) + ((ph (X 2 4) (Y 2 3) + ph (X 2 3) (Y 2 4) + ph (X 2 2) (Y 2 5)) + (pl (X 2 5) (Y 2 3) + pl (X 2 4) (Y 2 4) + pl (X 2 3) (Y 2 5))), (ph (X 3 5) (Y 3 2)) + ((ph (X 3 4) (Y 3 3) + ph (X 3 3) (Y 3 4) + ph (X 3 2) (Y 3 5)) + (pl (X 3 5) (Y 3 3) + pl (X 3 4) (Y 3 4) + pl (X 3 3) (Y 3 5))), (ph (X 0 5) (Y 0 5)) + ((ph (X 0 4) (Y 0 0) + ph (X 0 3) (Y 0 1) + ph (X 0 2) (Y 0 2)) + (pl (X 0 5) (Y 0 0) + pl (X 0 4) (Y 0 1) + pl (X 0 3) (Y 0 2))), (ph (X 1 5) (Y 1 5)) + ((ph (X 1 4) (Y 1 0) + ph (X 1 3) (Y 1 1) + ph (X 1 2) (Y 1 2)) + (pl (X 1 5) (Y 1 0) + pl (X 1 4) (Y 1 1) + pl (X 1 3) (Y 1 2))), (ph (X 2 5) (Y 2 5)) + ((ph (X 2 4) (Y 2 0) + ph (X 2 3) (Y 2 1) + ph (X 2 2) (Y 2 2)) + (pl (X 2 5) (Y 2 0) + pl (X 2 4) (Y 2 1) + pl (X 2 3) (Y 2 2))), (ph (X 3 5) (Y 3 5)) + ((ph (X 3 4) (Y 3 0) + ph (X 3 3) (Y 3 1) + ph (X 3 2) (Y 3 2)) + (pl (X 3 5) (Y 3 0) + pl (X 3 4) (Y 3 1) + pl (X 3 3) (Y 3 2)))]
  have hzb25_add : v75 = zb25_add := by quad_vecbin hv75 with quadDualValMem, p8_qb, q8_p5, zb25_add
  subst hzb25_add
  denote_clear v 75 75
  denote_step_all v 76
  -- zb25: columns 8 and 11
  let zb25 := toBitVecValue 64 #v[(ph (X 0 5) (Y 0 2)) + ((ph (X 0 4) (Y 0 3) + ph (X 0 3) (Y 0 4) + ph (X 0 2) (Y 0 5)) + (pl (X 0 5) (Y 0 3) + pl (X 0 4) (Y 0 4) + pl (X 0 3) (Y 0 5))), (ph (X 1 5) (Y 1 2)) + ((ph (X 1 4) (Y 1 3) + ph (X 1 3) (Y 1 4) + ph (X 1 2) (Y 1 5)) + (pl (X 1 5) (Y 1 3) + pl (X 1 4) (Y 1 4) + pl (X 1 3) (Y 1 5))), (ph (X 2 5) (Y 2 2)) + ((ph (X 2 4) (Y 2 3) + ph (X 2 3) (Y 2 4) + ph (X 2 2) (Y 2 5)) + (pl (X 2 5) (Y 2 3) + pl (X 2 4) (Y 2 4) + pl (X 2 3) (Y 2 5))), (ph (X 3 5) (Y 3 2)) + ((ph (X 3 4) (Y 3 3) + ph (X 3 3) (Y 3 4) + ph (X 3 2) (Y 3 5)) + (pl (X 3 5) (Y 3 3) + pl (X 3 4) (Y 3 4) + pl (X 3 3) (Y 3 5))), ph (X 0 5) (Y 0 5), ph (X 1 5) (Y 1 5), ph (X 2 5) (Y 2 5), ph (X 3 5) (Y 3 5)]
  have hzb25 : v76 = zb25 := by quad_shuffle hv76 with p8_qb, zb25, zb25_add
  subst hzb25
  denote_clear v 76 76
  denote_step_all v 77
  let zb03_shl7 := toBitVecValue 64 #v[(((ph (X 0 5) (Y 0 0) + ph (X 0 4) (Y 0 1) + ph (X 0 3) (Y 0 2)) + (pl (X 0 5) (Y 0 1) + pl (X 0 4) (Y 0 2))) + ((ph (X 0 2) (Y 0 3) + ph (X 0 1) (Y 0 4) + ph (X 0 0) (Y 0 5)) + (pl (X 0 3) (Y 0 3) + pl (X 0 2) (Y 0 4) + pl (X 0 1) (Y 0 5)))) * 128, (((ph (X 1 5) (Y 1 0) + ph (X 1 4) (Y 1 1) + ph (X 1 3) (Y 1 2)) + (pl (X 1 5) (Y 1 1) + pl (X 1 4) (Y 1 2))) + ((ph (X 1 2) (Y 1 3) + ph (X 1 1) (Y 1 4) + ph (X 1 0) (Y 1 5)) + (pl (X 1 3) (Y 1 3) + pl (X 1 2) (Y 1 4) + pl (X 1 1) (Y 1 5)))) * 128, (((ph (X 2 5) (Y 2 0) + ph (X 2 4) (Y 2 1) + ph (X 2 3) (Y 2 2)) + (pl (X 2 5) (Y 2 1) + pl (X 2 4) (Y 2 2))) + ((ph (X 2 2) (Y 2 3) + ph (X 2 1) (Y 2 4) + ph (X 2 0) (Y 2 5)) + (pl (X 2 3) (Y 2 3) + pl (X 2 2) (Y 2 4) + pl (X 2 1) (Y 2 5)))) * 128, (((ph (X 3 5) (Y 3 0) + ph (X 3 4) (Y 3 1) + ph (X 3 3) (Y 3 2)) + (pl (X 3 5) (Y 3 1) + pl (X 3 4) (Y 3 2))) + ((ph (X 3 2) (Y 3 3) + ph (X 3 1) (Y 3 4) + ph (X 3 0) (Y 3 5)) + (pl (X 3 3) (Y 3 3) + pl (X 3 2) (Y 3 4) + pl (X 3 1) (Y 3 5)))) * 128, ((ph (X 0 5) (Y 0 3) + ph (X 0 4) (Y 0 4) + ph (X 0 3) (Y 0 5)) + (pl (X 0 5) (Y 0 4) + pl (X 0 4) (Y 0 5))) * 128, ((ph (X 1 5) (Y 1 3) + ph (X 1 4) (Y 1 4) + ph (X 1 3) (Y 1 5)) + (pl (X 1 5) (Y 1 4) + pl (X 1 4) (Y 1 5))) * 128, ((ph (X 2 5) (Y 2 3) + ph (X 2 4) (Y 2 4) + ph (X 2 3) (Y 2 5)) + (pl (X 2 5) (Y 2 4) + pl (X 2 4) (Y 2 5))) * 128, ((ph (X 3 5) (Y 3 3) + ph (X 3 4) (Y 3 4) + ph (X 3 3) (Y 3 5)) + (pl (X 3 5) (Y 3 4) + pl (X 3 4) (Y 3 5))) * 128]
  have hzb03_shl7 : v77 = zb03_shl7 := by quad_vecbin hv77 with quadDualValMem, zb03, zb03_shl7
  subst hzb03_shl7
  denote_clear v 77 77
  denote_step_all v 78
  let z03_part := toBitVecValue 64 #v[((((ph (X 0 5) (Y 0 0) + ph (X 0 4) (Y 0 1) + ph (X 0 3) (Y 0 2)) + (pl (X 0 5) (Y 0 1) + pl (X 0 4) (Y 0 2))) + ((ph (X 0 2) (Y 0 3) + ph (X 0 1) (Y 0 4) + ph (X 0 0) (Y 0 5)) + (pl (X 0 3) (Y 0 3) + pl (X 0 2) (Y 0 4) + pl (X 0 1) (Y 0 5)))) * 128) + (pl (X 0 0) (Y 0 0)), ((((ph (X 1 5) (Y 1 0) + ph (X 1 4) (Y 1 1) + ph (X 1 3) (Y 1 2)) + (pl (X 1 5) (Y 1 1) + pl (X 1 4) (Y 1 2))) + ((ph (X 1 2) (Y 1 3) + ph (X 1 1) (Y 1 4) + ph (X 1 0) (Y 1 5)) + (pl (X 1 3) (Y 1 3) + pl (X 1 2) (Y 1 4) + pl (X 1 1) (Y 1 5)))) * 128) + (pl (X 1 0) (Y 1 0)), ((((ph (X 2 5) (Y 2 0) + ph (X 2 4) (Y 2 1) + ph (X 2 3) (Y 2 2)) + (pl (X 2 5) (Y 2 1) + pl (X 2 4) (Y 2 2))) + ((ph (X 2 2) (Y 2 3) + ph (X 2 1) (Y 2 4) + ph (X 2 0) (Y 2 5)) + (pl (X 2 3) (Y 2 3) + pl (X 2 2) (Y 2 4) + pl (X 2 1) (Y 2 5)))) * 128) + (pl (X 2 0) (Y 2 0)), ((((ph (X 3 5) (Y 3 0) + ph (X 3 4) (Y 3 1) + ph (X 3 3) (Y 3 2)) + (pl (X 3 5) (Y 3 1) + pl (X 3 4) (Y 3 2))) + ((ph (X 3 2) (Y 3 3) + ph (X 3 1) (Y 3 4) + ph (X 3 0) (Y 3 5)) + (pl (X 3 3) (Y 3 3) + pl (X 3 2) (Y 3 4) + pl (X 3 1) (Y 3 5)))) * 128) + (pl (X 3 0) (Y 3 0)), (((ph (X 0 5) (Y 0 3) + ph (X 0 4) (Y 0 4) + ph (X 0 3) (Y 0 5)) + (pl (X 0 5) (Y 0 4) + pl (X 0 4) (Y 0 5))) * 128) + (((ph (X 0 2) (Y 0 0) + ph (X 0 1) (Y 0 1) + ph (X 0 0) (Y 0 2)) + (pl (X 0 3) (Y 0 0) + pl (X 0 2) (Y 0 1) + pl (X 0 1) (Y 0 2))) + (pl (X 0 0) (Y 0 3))), (((ph (X 1 5) (Y 1 3) + ph (X 1 4) (Y 1 4) + ph (X 1 3) (Y 1 5)) + (pl (X 1 5) (Y 1 4) + pl (X 1 4) (Y 1 5))) * 128) + (((ph (X 1 2) (Y 1 0) + ph (X 1 1) (Y 1 1) + ph (X 1 0) (Y 1 2)) + (pl (X 1 3) (Y 1 0) + pl (X 1 2) (Y 1 1) + pl (X 1 1) (Y 1 2))) + (pl (X 1 0) (Y 1 3))), (((ph (X 2 5) (Y 2 3) + ph (X 2 4) (Y 2 4) + ph (X 2 3) (Y 2 5)) + (pl (X 2 5) (Y 2 4) + pl (X 2 4) (Y 2 5))) * 128) + (((ph (X 2 2) (Y 2 0) + ph (X 2 1) (Y 2 1) + ph (X 2 0) (Y 2 2)) + (pl (X 2 3) (Y 2 0) + pl (X 2 2) (Y 2 1) + pl (X 2 1) (Y 2 2))) + (pl (X 2 0) (Y 2 3))), (((ph (X 3 5) (Y 3 3) + ph (X 3 4) (Y 3 4) + ph (X 3 3) (Y 3 5)) + (pl (X 3 5) (Y 3 4) + pl (X 3 4) (Y 3 5))) * 128) + (((ph (X 3 2) (Y 3 0) + ph (X 3 1) (Y 3 1) + ph (X 3 0) (Y 3 2)) + (pl (X 3 3) (Y 3 0) + pl (X 3 2) (Y 3 1) + pl (X 3 1) (Y 3 2))) + (pl (X 3 0) (Y 3 3)))]
  have hz03_part : v78 = z03_part := by quad_vecbin hv78 with quadDualValMem, z03_part, za03, zb03_shl7
  subst hz03_part
  denote_clear v 78 78
  denote_step_all v 79
  let zb03_mul24 := toBitVecValue 64 #v[(((ph (X 0 5) (Y 0 0) + ph (X 0 4) (Y 0 1) + ph (X 0 3) (Y 0 2)) + (pl (X 0 5) (Y 0 1) + pl (X 0 4) (Y 0 2))) + ((ph (X 0 2) (Y 0 3) + ph (X 0 1) (Y 0 4) + ph (X 0 0) (Y 0 5)) + (pl (X 0 3) (Y 0 3) + pl (X 0 2) (Y 0 4) + pl (X 0 1) (Y 0 5)))) * 24, (((ph (X 1 5) (Y 1 0) + ph (X 1 4) (Y 1 1) + ph (X 1 3) (Y 1 2)) + (pl (X 1 5) (Y 1 1) + pl (X 1 4) (Y 1 2))) + ((ph (X 1 2) (Y 1 3) + ph (X 1 1) (Y 1 4) + ph (X 1 0) (Y 1 5)) + (pl (X 1 3) (Y 1 3) + pl (X 1 2) (Y 1 4) + pl (X 1 1) (Y 1 5)))) * 24, (((ph (X 2 5) (Y 2 0) + ph (X 2 4) (Y 2 1) + ph (X 2 3) (Y 2 2)) + (pl (X 2 5) (Y 2 1) + pl (X 2 4) (Y 2 2))) + ((ph (X 2 2) (Y 2 3) + ph (X 2 1) (Y 2 4) + ph (X 2 0) (Y 2 5)) + (pl (X 2 3) (Y 2 3) + pl (X 2 2) (Y 2 4) + pl (X 2 1) (Y 2 5)))) * 24, (((ph (X 3 5) (Y 3 0) + ph (X 3 4) (Y 3 1) + ph (X 3 3) (Y 3 2)) + (pl (X 3 5) (Y 3 1) + pl (X 3 4) (Y 3 2))) + ((ph (X 3 2) (Y 3 3) + ph (X 3 1) (Y 3 4) + ph (X 3 0) (Y 3 5)) + (pl (X 3 3) (Y 3 3) + pl (X 3 2) (Y 3 4) + pl (X 3 1) (Y 3 5)))) * 24, ((ph (X 0 5) (Y 0 3) + ph (X 0 4) (Y 0 4) + ph (X 0 3) (Y 0 5)) + (pl (X 0 5) (Y 0 4) + pl (X 0 4) (Y 0 5))) * 24, ((ph (X 1 5) (Y 1 3) + ph (X 1 4) (Y 1 4) + ph (X 1 3) (Y 1 5)) + (pl (X 1 5) (Y 1 4) + pl (X 1 4) (Y 1 5))) * 24, ((ph (X 2 5) (Y 2 3) + ph (X 2 4) (Y 2 4) + ph (X 2 3) (Y 2 5)) + (pl (X 2 5) (Y 2 4) + pl (X 2 4) (Y 2 5))) * 24, ((ph (X 3 5) (Y 3 3) + ph (X 3 4) (Y 3 4) + ph (X 3 3) (Y 3 5)) + (pl (X 3 5) (Y 3 4) + pl (X 3 4) (Y 3 5))) * 24]
  have hzb03_mul24 : v79 = zb03_mul24 := by quad_vecbin hv79 with quadDualValMem, zb03, zb03_mul24
  subst hzb03_mul24
  denote_clear v 79 79
  denote_step_all v 80
  -- z03: `za03 + 152*zb03`, limbs 0 and 3 of all four elements
  let z03 := toBitVecValue 64 #v[(((((ph (X 0 5) (Y 0 0) + ph (X 0 4) (Y 0 1) + ph (X 0 3) (Y 0 2)) + (pl (X 0 5) (Y 0 1) + pl (X 0 4) (Y 0 2))) + ((ph (X 0 2) (Y 0 3) + ph (X 0 1) (Y 0 4) + ph (X 0 0) (Y 0 5)) + (pl (X 0 3) (Y 0 3) + pl (X 0 2) (Y 0 4) + pl (X 0 1) (Y 0 5)))) * 128) + (pl (X 0 0) (Y 0 0))) + ((((ph (X 0 5) (Y 0 0) + ph (X 0 4) (Y 0 1) + ph (X 0 3) (Y 0 2)) + (pl (X 0 5) (Y 0 1) + pl (X 0 4) (Y 0 2))) + ((ph (X 0 2) (Y 0 3) + ph (X 0 1) (Y 0 4) + ph (X 0 0) (Y 0 5)) + (pl (X 0 3) (Y 0 3) + pl (X 0 2) (Y 0 4) + pl (X 0 1) (Y 0 5)))) * 24), (((((ph (X 1 5) (Y 1 0) + ph (X 1 4) (Y 1 1) + ph (X 1 3) (Y 1 2)) + (pl (X 1 5) (Y 1 1) + pl (X 1 4) (Y 1 2))) + ((ph (X 1 2) (Y 1 3) + ph (X 1 1) (Y 1 4) + ph (X 1 0) (Y 1 5)) + (pl (X 1 3) (Y 1 3) + pl (X 1 2) (Y 1 4) + pl (X 1 1) (Y 1 5)))) * 128) + (pl (X 1 0) (Y 1 0))) + ((((ph (X 1 5) (Y 1 0) + ph (X 1 4) (Y 1 1) + ph (X 1 3) (Y 1 2)) + (pl (X 1 5) (Y 1 1) + pl (X 1 4) (Y 1 2))) + ((ph (X 1 2) (Y 1 3) + ph (X 1 1) (Y 1 4) + ph (X 1 0) (Y 1 5)) + (pl (X 1 3) (Y 1 3) + pl (X 1 2) (Y 1 4) + pl (X 1 1) (Y 1 5)))) * 24), (((((ph (X 2 5) (Y 2 0) + ph (X 2 4) (Y 2 1) + ph (X 2 3) (Y 2 2)) + (pl (X 2 5) (Y 2 1) + pl (X 2 4) (Y 2 2))) + ((ph (X 2 2) (Y 2 3) + ph (X 2 1) (Y 2 4) + ph (X 2 0) (Y 2 5)) + (pl (X 2 3) (Y 2 3) + pl (X 2 2) (Y 2 4) + pl (X 2 1) (Y 2 5)))) * 128) + (pl (X 2 0) (Y 2 0))) + ((((ph (X 2 5) (Y 2 0) + ph (X 2 4) (Y 2 1) + ph (X 2 3) (Y 2 2)) + (pl (X 2 5) (Y 2 1) + pl (X 2 4) (Y 2 2))) + ((ph (X 2 2) (Y 2 3) + ph (X 2 1) (Y 2 4) + ph (X 2 0) (Y 2 5)) + (pl (X 2 3) (Y 2 3) + pl (X 2 2) (Y 2 4) + pl (X 2 1) (Y 2 5)))) * 24), (((((ph (X 3 5) (Y 3 0) + ph (X 3 4) (Y 3 1) + ph (X 3 3) (Y 3 2)) + (pl (X 3 5) (Y 3 1) + pl (X 3 4) (Y 3 2))) + ((ph (X 3 2) (Y 3 3) + ph (X 3 1) (Y 3 4) + ph (X 3 0) (Y 3 5)) + (pl (X 3 3) (Y 3 3) + pl (X 3 2) (Y 3 4) + pl (X 3 1) (Y 3 5)))) * 128) + (pl (X 3 0) (Y 3 0))) + ((((ph (X 3 5) (Y 3 0) + ph (X 3 4) (Y 3 1) + ph (X 3 3) (Y 3 2)) + (pl (X 3 5) (Y 3 1) + pl (X 3 4) (Y 3 2))) + ((ph (X 3 2) (Y 3 3) + ph (X 3 1) (Y 3 4) + ph (X 3 0) (Y 3 5)) + (pl (X 3 3) (Y 3 3) + pl (X 3 2) (Y 3 4) + pl (X 3 1) (Y 3 5)))) * 24), ((((ph (X 0 5) (Y 0 3) + ph (X 0 4) (Y 0 4) + ph (X 0 3) (Y 0 5)) + (pl (X 0 5) (Y 0 4) + pl (X 0 4) (Y 0 5))) * 128) + (((ph (X 0 2) (Y 0 0) + ph (X 0 1) (Y 0 1) + ph (X 0 0) (Y 0 2)) + (pl (X 0 3) (Y 0 0) + pl (X 0 2) (Y 0 1) + pl (X 0 1) (Y 0 2))) + (pl (X 0 0) (Y 0 3)))) + (((ph (X 0 5) (Y 0 3) + ph (X 0 4) (Y 0 4) + ph (X 0 3) (Y 0 5)) + (pl (X 0 5) (Y 0 4) + pl (X 0 4) (Y 0 5))) * 24), ((((ph (X 1 5) (Y 1 3) + ph (X 1 4) (Y 1 4) + ph (X 1 3) (Y 1 5)) + (pl (X 1 5) (Y 1 4) + pl (X 1 4) (Y 1 5))) * 128) + (((ph (X 1 2) (Y 1 0) + ph (X 1 1) (Y 1 1) + ph (X 1 0) (Y 1 2)) + (pl (X 1 3) (Y 1 0) + pl (X 1 2) (Y 1 1) + pl (X 1 1) (Y 1 2))) + (pl (X 1 0) (Y 1 3)))) + (((ph (X 1 5) (Y 1 3) + ph (X 1 4) (Y 1 4) + ph (X 1 3) (Y 1 5)) + (pl (X 1 5) (Y 1 4) + pl (X 1 4) (Y 1 5))) * 24), ((((ph (X 2 5) (Y 2 3) + ph (X 2 4) (Y 2 4) + ph (X 2 3) (Y 2 5)) + (pl (X 2 5) (Y 2 4) + pl (X 2 4) (Y 2 5))) * 128) + (((ph (X 2 2) (Y 2 0) + ph (X 2 1) (Y 2 1) + ph (X 2 0) (Y 2 2)) + (pl (X 2 3) (Y 2 0) + pl (X 2 2) (Y 2 1) + pl (X 2 1) (Y 2 2))) + (pl (X 2 0) (Y 2 3)))) + (((ph (X 2 5) (Y 2 3) + ph (X 2 4) (Y 2 4) + ph (X 2 3) (Y 2 5)) + (pl (X 2 5) (Y 2 4) + pl (X 2 4) (Y 2 5))) * 24), ((((ph (X 3 5) (Y 3 3) + ph (X 3 4) (Y 3 4) + ph (X 3 3) (Y 3 5)) + (pl (X 3 5) (Y 3 4) + pl (X 3 4) (Y 3 5))) * 128) + (((ph (X 3 2) (Y 3 0) + ph (X 3 1) (Y 3 1) + ph (X 3 0) (Y 3 2)) + (pl (X 3 3) (Y 3 0) + pl (X 3 2) (Y 3 1) + pl (X 3 1) (Y 3 2))) + (pl (X 3 0) (Y 3 3)))) + (((ph (X 3 5) (Y 3 3) + ph (X 3 4) (Y 3 4) + ph (X 3 3) (Y 3 5)) + (pl (X 3 5) (Y 3 4) + pl (X 3 4) (Y 3 5))) * 24)]
  have hz03 : v80 = z03 := by quad_vecbin hv80 with quadDualValMem, z03, z03_part, zb03_mul24
  subst hz03
  denote_clear v 80 80
  denote_step_all v 81
  let zb14_shl7 := toBitVecValue 64 #v[(((ph (X 0 5) (Y 0 1) + ph (X 0 4) (Y 0 2)) + (pl (X 0 5) (Y 0 2))) + ((ph (X 0 3) (Y 0 3) + ph (X 0 2) (Y 0 4) + ph (X 0 1) (Y 0 5)) + (pl (X 0 4) (Y 0 3) + pl (X 0 3) (Y 0 4) + pl (X 0 2) (Y 0 5)))) * 128, (((ph (X 1 5) (Y 1 1) + ph (X 1 4) (Y 1 2)) + (pl (X 1 5) (Y 1 2))) + ((ph (X 1 3) (Y 1 3) + ph (X 1 2) (Y 1 4) + ph (X 1 1) (Y 1 5)) + (pl (X 1 4) (Y 1 3) + pl (X 1 3) (Y 1 4) + pl (X 1 2) (Y 1 5)))) * 128, (((ph (X 2 5) (Y 2 1) + ph (X 2 4) (Y 2 2)) + (pl (X 2 5) (Y 2 2))) + ((ph (X 2 3) (Y 2 3) + ph (X 2 2) (Y 2 4) + ph (X 2 1) (Y 2 5)) + (pl (X 2 4) (Y 2 3) + pl (X 2 3) (Y 2 4) + pl (X 2 2) (Y 2 5)))) * 128, (((ph (X 3 5) (Y 3 1) + ph (X 3 4) (Y 3 2)) + (pl (X 3 5) (Y 3 2))) + ((ph (X 3 3) (Y 3 3) + ph (X 3 2) (Y 3 4) + ph (X 3 1) (Y 3 5)) + (pl (X 3 4) (Y 3 3) + pl (X 3 3) (Y 3 4) + pl (X 3 2) (Y 3 5)))) * 128, ((ph (X 0 5) (Y 0 4) + ph (X 0 4) (Y 0 5)) + (pl (X 0 5) (Y 0 5))) * 128, ((ph (X 1 5) (Y 1 4) + ph (X 1 4) (Y 1 5)) + (pl (X 1 5) (Y 1 5))) * 128, ((ph (X 2 5) (Y 2 4) + ph (X 2 4) (Y 2 5)) + (pl (X 2 5) (Y 2 5))) * 128, ((ph (X 3 5) (Y 3 4) + ph (X 3 4) (Y 3 5)) + (pl (X 3 5) (Y 3 5))) * 128]
  have hzb14_shl7 : v81 = zb14_shl7 := by quad_vecbin hv81 with quadDualValMem, zb14, zb14_shl7
  subst hzb14_shl7
  denote_clear v 81 81
  denote_step_all v 82
  let z14_part := toBitVecValue 64 #v[((((ph (X 0 5) (Y 0 1) + ph (X 0 4) (Y 0 2)) + (pl (X 0 5) (Y 0 2))) + ((ph (X 0 3) (Y 0 3) + ph (X 0 2) (Y 0 4) + ph (X 0 1) (Y 0 5)) + (pl (X 0 4) (Y 0 3) + pl (X 0 3) (Y 0 4) + pl (X 0 2) (Y 0 5)))) * 128) + ((ph (X 0 0) (Y 0 0)) + (pl (X 0 1) (Y 0 0) + pl (X 0 0) (Y 0 1))), ((((ph (X 1 5) (Y 1 1) + ph (X 1 4) (Y 1 2)) + (pl (X 1 5) (Y 1 2))) + ((ph (X 1 3) (Y 1 3) + ph (X 1 2) (Y 1 4) + ph (X 1 1) (Y 1 5)) + (pl (X 1 4) (Y 1 3) + pl (X 1 3) (Y 1 4) + pl (X 1 2) (Y 1 5)))) * 128) + ((ph (X 1 0) (Y 1 0)) + (pl (X 1 1) (Y 1 0) + pl (X 1 0) (Y 1 1))), ((((ph (X 2 5) (Y 2 1) + ph (X 2 4) (Y 2 2)) + (pl (X 2 5) (Y 2 2))) + ((ph (X 2 3) (Y 2 3) + ph (X 2 2) (Y 2 4) + ph (X 2 1) (Y 2 5)) + (pl (X 2 4) (Y 2 3) + pl (X 2 3) (Y 2 4) + pl (X 2 2) (Y 2 5)))) * 128) + ((ph (X 2 0) (Y 2 0)) + (pl (X 2 1) (Y 2 0) + pl (X 2 0) (Y 2 1))), ((((ph (X 3 5) (Y 3 1) + ph (X 3 4) (Y 3 2)) + (pl (X 3 5) (Y 3 2))) + ((ph (X 3 3) (Y 3 3) + ph (X 3 2) (Y 3 4) + ph (X 3 1) (Y 3 5)) + (pl (X 3 4) (Y 3 3) + pl (X 3 3) (Y 3 4) + pl (X 3 2) (Y 3 5)))) * 128) + ((ph (X 3 0) (Y 3 0)) + (pl (X 3 1) (Y 3 0) + pl (X 3 0) (Y 3 1))), (((ph (X 0 5) (Y 0 4) + ph (X 0 4) (Y 0 5)) + (pl (X 0 5) (Y 0 5))) * 128) + (((ph (X 0 3) (Y 0 0) + ph (X 0 2) (Y 0 1) + ph (X 0 1) (Y 0 2)) + (pl (X 0 4) (Y 0 0) + pl (X 0 3) (Y 0 1) + pl (X 0 2) (Y 0 2))) + ((ph (X 0 0) (Y 0 3)) + (pl (X 0 1) (Y 0 3) + pl (X 0 0) (Y 0 4)))), (((ph (X 1 5) (Y 1 4) + ph (X 1 4) (Y 1 5)) + (pl (X 1 5) (Y 1 5))) * 128) + (((ph (X 1 3) (Y 1 0) + ph (X 1 2) (Y 1 1) + ph (X 1 1) (Y 1 2)) + (pl (X 1 4) (Y 1 0) + pl (X 1 3) (Y 1 1) + pl (X 1 2) (Y 1 2))) + ((ph (X 1 0) (Y 1 3)) + (pl (X 1 1) (Y 1 3) + pl (X 1 0) (Y 1 4)))), (((ph (X 2 5) (Y 2 4) + ph (X 2 4) (Y 2 5)) + (pl (X 2 5) (Y 2 5))) * 128) + (((ph (X 2 3) (Y 2 0) + ph (X 2 2) (Y 2 1) + ph (X 2 1) (Y 2 2)) + (pl (X 2 4) (Y 2 0) + pl (X 2 3) (Y 2 1) + pl (X 2 2) (Y 2 2))) + ((ph (X 2 0) (Y 2 3)) + (pl (X 2 1) (Y 2 3) + pl (X 2 0) (Y 2 4)))), (((ph (X 3 5) (Y 3 4) + ph (X 3 4) (Y 3 5)) + (pl (X 3 5) (Y 3 5))) * 128) + (((ph (X 3 3) (Y 3 0) + ph (X 3 2) (Y 3 1) + ph (X 3 1) (Y 3 2)) + (pl (X 3 4) (Y 3 0) + pl (X 3 3) (Y 3 1) + pl (X 3 2) (Y 3 2))) + ((ph (X 3 0) (Y 3 3)) + (pl (X 3 1) (Y 3 3) + pl (X 3 0) (Y 3 4))))]
  have hz14_part : v82 = z14_part := by quad_vecbin hv82 with quadDualValMem, z14_part, za14, zb14_shl7
  subst hz14_part
  denote_clear v 82 82
  denote_step_all v 83
  let zb14_mul24 := toBitVecValue 64 #v[(((ph (X 0 5) (Y 0 1) + ph (X 0 4) (Y 0 2)) + (pl (X 0 5) (Y 0 2))) + ((ph (X 0 3) (Y 0 3) + ph (X 0 2) (Y 0 4) + ph (X 0 1) (Y 0 5)) + (pl (X 0 4) (Y 0 3) + pl (X 0 3) (Y 0 4) + pl (X 0 2) (Y 0 5)))) * 24, (((ph (X 1 5) (Y 1 1) + ph (X 1 4) (Y 1 2)) + (pl (X 1 5) (Y 1 2))) + ((ph (X 1 3) (Y 1 3) + ph (X 1 2) (Y 1 4) + ph (X 1 1) (Y 1 5)) + (pl (X 1 4) (Y 1 3) + pl (X 1 3) (Y 1 4) + pl (X 1 2) (Y 1 5)))) * 24, (((ph (X 2 5) (Y 2 1) + ph (X 2 4) (Y 2 2)) + (pl (X 2 5) (Y 2 2))) + ((ph (X 2 3) (Y 2 3) + ph (X 2 2) (Y 2 4) + ph (X 2 1) (Y 2 5)) + (pl (X 2 4) (Y 2 3) + pl (X 2 3) (Y 2 4) + pl (X 2 2) (Y 2 5)))) * 24, (((ph (X 3 5) (Y 3 1) + ph (X 3 4) (Y 3 2)) + (pl (X 3 5) (Y 3 2))) + ((ph (X 3 3) (Y 3 3) + ph (X 3 2) (Y 3 4) + ph (X 3 1) (Y 3 5)) + (pl (X 3 4) (Y 3 3) + pl (X 3 3) (Y 3 4) + pl (X 3 2) (Y 3 5)))) * 24, ((ph (X 0 5) (Y 0 4) + ph (X 0 4) (Y 0 5)) + (pl (X 0 5) (Y 0 5))) * 24, ((ph (X 1 5) (Y 1 4) + ph (X 1 4) (Y 1 5)) + (pl (X 1 5) (Y 1 5))) * 24, ((ph (X 2 5) (Y 2 4) + ph (X 2 4) (Y 2 5)) + (pl (X 2 5) (Y 2 5))) * 24, ((ph (X 3 5) (Y 3 4) + ph (X 3 4) (Y 3 5)) + (pl (X 3 5) (Y 3 5))) * 24]
  have hzb14_mul24 : v83 = zb14_mul24 := by quad_vecbin hv83 with quadDualValMem, zb14, zb14_mul24
  subst hzb14_mul24
  denote_clear v 83 83
  denote_step_all v 84
  -- z14: limbs 1 and 4
  let z14 := toBitVecValue 64 #v[(((((ph (X 0 5) (Y 0 1) + ph (X 0 4) (Y 0 2)) + (pl (X 0 5) (Y 0 2))) + ((ph (X 0 3) (Y 0 3) + ph (X 0 2) (Y 0 4) + ph (X 0 1) (Y 0 5)) + (pl (X 0 4) (Y 0 3) + pl (X 0 3) (Y 0 4) + pl (X 0 2) (Y 0 5)))) * 128) + ((ph (X 0 0) (Y 0 0)) + (pl (X 0 1) (Y 0 0) + pl (X 0 0) (Y 0 1)))) + ((((ph (X 0 5) (Y 0 1) + ph (X 0 4) (Y 0 2)) + (pl (X 0 5) (Y 0 2))) + ((ph (X 0 3) (Y 0 3) + ph (X 0 2) (Y 0 4) + ph (X 0 1) (Y 0 5)) + (pl (X 0 4) (Y 0 3) + pl (X 0 3) (Y 0 4) + pl (X 0 2) (Y 0 5)))) * 24), (((((ph (X 1 5) (Y 1 1) + ph (X 1 4) (Y 1 2)) + (pl (X 1 5) (Y 1 2))) + ((ph (X 1 3) (Y 1 3) + ph (X 1 2) (Y 1 4) + ph (X 1 1) (Y 1 5)) + (pl (X 1 4) (Y 1 3) + pl (X 1 3) (Y 1 4) + pl (X 1 2) (Y 1 5)))) * 128) + ((ph (X 1 0) (Y 1 0)) + (pl (X 1 1) (Y 1 0) + pl (X 1 0) (Y 1 1)))) + ((((ph (X 1 5) (Y 1 1) + ph (X 1 4) (Y 1 2)) + (pl (X 1 5) (Y 1 2))) + ((ph (X 1 3) (Y 1 3) + ph (X 1 2) (Y 1 4) + ph (X 1 1) (Y 1 5)) + (pl (X 1 4) (Y 1 3) + pl (X 1 3) (Y 1 4) + pl (X 1 2) (Y 1 5)))) * 24), (((((ph (X 2 5) (Y 2 1) + ph (X 2 4) (Y 2 2)) + (pl (X 2 5) (Y 2 2))) + ((ph (X 2 3) (Y 2 3) + ph (X 2 2) (Y 2 4) + ph (X 2 1) (Y 2 5)) + (pl (X 2 4) (Y 2 3) + pl (X 2 3) (Y 2 4) + pl (X 2 2) (Y 2 5)))) * 128) + ((ph (X 2 0) (Y 2 0)) + (pl (X 2 1) (Y 2 0) + pl (X 2 0) (Y 2 1)))) + ((((ph (X 2 5) (Y 2 1) + ph (X 2 4) (Y 2 2)) + (pl (X 2 5) (Y 2 2))) + ((ph (X 2 3) (Y 2 3) + ph (X 2 2) (Y 2 4) + ph (X 2 1) (Y 2 5)) + (pl (X 2 4) (Y 2 3) + pl (X 2 3) (Y 2 4) + pl (X 2 2) (Y 2 5)))) * 24), (((((ph (X 3 5) (Y 3 1) + ph (X 3 4) (Y 3 2)) + (pl (X 3 5) (Y 3 2))) + ((ph (X 3 3) (Y 3 3) + ph (X 3 2) (Y 3 4) + ph (X 3 1) (Y 3 5)) + (pl (X 3 4) (Y 3 3) + pl (X 3 3) (Y 3 4) + pl (X 3 2) (Y 3 5)))) * 128) + ((ph (X 3 0) (Y 3 0)) + (pl (X 3 1) (Y 3 0) + pl (X 3 0) (Y 3 1)))) + ((((ph (X 3 5) (Y 3 1) + ph (X 3 4) (Y 3 2)) + (pl (X 3 5) (Y 3 2))) + ((ph (X 3 3) (Y 3 3) + ph (X 3 2) (Y 3 4) + ph (X 3 1) (Y 3 5)) + (pl (X 3 4) (Y 3 3) + pl (X 3 3) (Y 3 4) + pl (X 3 2) (Y 3 5)))) * 24), ((((ph (X 0 5) (Y 0 4) + ph (X 0 4) (Y 0 5)) + (pl (X 0 5) (Y 0 5))) * 128) + (((ph (X 0 3) (Y 0 0) + ph (X 0 2) (Y 0 1) + ph (X 0 1) (Y 0 2)) + (pl (X 0 4) (Y 0 0) + pl (X 0 3) (Y 0 1) + pl (X 0 2) (Y 0 2))) + ((ph (X 0 0) (Y 0 3)) + (pl (X 0 1) (Y 0 3) + pl (X 0 0) (Y 0 4))))) + (((ph (X 0 5) (Y 0 4) + ph (X 0 4) (Y 0 5)) + (pl (X 0 5) (Y 0 5))) * 24), ((((ph (X 1 5) (Y 1 4) + ph (X 1 4) (Y 1 5)) + (pl (X 1 5) (Y 1 5))) * 128) + (((ph (X 1 3) (Y 1 0) + ph (X 1 2) (Y 1 1) + ph (X 1 1) (Y 1 2)) + (pl (X 1 4) (Y 1 0) + pl (X 1 3) (Y 1 1) + pl (X 1 2) (Y 1 2))) + ((ph (X 1 0) (Y 1 3)) + (pl (X 1 1) (Y 1 3) + pl (X 1 0) (Y 1 4))))) + (((ph (X 1 5) (Y 1 4) + ph (X 1 4) (Y 1 5)) + (pl (X 1 5) (Y 1 5))) * 24), ((((ph (X 2 5) (Y 2 4) + ph (X 2 4) (Y 2 5)) + (pl (X 2 5) (Y 2 5))) * 128) + (((ph (X 2 3) (Y 2 0) + ph (X 2 2) (Y 2 1) + ph (X 2 1) (Y 2 2)) + (pl (X 2 4) (Y 2 0) + pl (X 2 3) (Y 2 1) + pl (X 2 2) (Y 2 2))) + ((ph (X 2 0) (Y 2 3)) + (pl (X 2 1) (Y 2 3) + pl (X 2 0) (Y 2 4))))) + (((ph (X 2 5) (Y 2 4) + ph (X 2 4) (Y 2 5)) + (pl (X 2 5) (Y 2 5))) * 24), ((((ph (X 3 5) (Y 3 4) + ph (X 3 4) (Y 3 5)) + (pl (X 3 5) (Y 3 5))) * 128) + (((ph (X 3 3) (Y 3 0) + ph (X 3 2) (Y 3 1) + ph (X 3 1) (Y 3 2)) + (pl (X 3 4) (Y 3 0) + pl (X 3 3) (Y 3 1) + pl (X 3 2) (Y 3 2))) + ((ph (X 3 0) (Y 3 3)) + (pl (X 3 1) (Y 3 3) + pl (X 3 0) (Y 3 4))))) + (((ph (X 3 5) (Y 3 4) + ph (X 3 4) (Y 3 5)) + (pl (X 3 5) (Y 3 5))) * 24)]
  have hz14 : v84 = z14 := by quad_vecbin hv84 with quadDualValMem, z14, z14_part, zb14_mul24
  subst hz14
  denote_clear v 84 84
  denote_step_all v 85
  let zb25_shl7 := toBitVecValue 64 #v[((ph (X 0 5) (Y 0 2)) + ((ph (X 0 4) (Y 0 3) + ph (X 0 3) (Y 0 4) + ph (X 0 2) (Y 0 5)) + (pl (X 0 5) (Y 0 3) + pl (X 0 4) (Y 0 4) + pl (X 0 3) (Y 0 5)))) * 128, ((ph (X 1 5) (Y 1 2)) + ((ph (X 1 4) (Y 1 3) + ph (X 1 3) (Y 1 4) + ph (X 1 2) (Y 1 5)) + (pl (X 1 5) (Y 1 3) + pl (X 1 4) (Y 1 4) + pl (X 1 3) (Y 1 5)))) * 128, ((ph (X 2 5) (Y 2 2)) + ((ph (X 2 4) (Y 2 3) + ph (X 2 3) (Y 2 4) + ph (X 2 2) (Y 2 5)) + (pl (X 2 5) (Y 2 3) + pl (X 2 4) (Y 2 4) + pl (X 2 3) (Y 2 5)))) * 128, ((ph (X 3 5) (Y 3 2)) + ((ph (X 3 4) (Y 3 3) + ph (X 3 3) (Y 3 4) + ph (X 3 2) (Y 3 5)) + (pl (X 3 5) (Y 3 3) + pl (X 3 4) (Y 3 4) + pl (X 3 3) (Y 3 5)))) * 128, (ph (X 0 5) (Y 0 5)) * 128, (ph (X 1 5) (Y 1 5)) * 128, (ph (X 2 5) (Y 2 5)) * 128, (ph (X 3 5) (Y 3 5)) * 128]
  have hzb25_shl7 : v85 = zb25_shl7 := by quad_vecbin hv85 with quadDualValMem, zb25, zb25_shl7
  subst hzb25_shl7
  denote_clear v 85 85
  denote_step_all v 86
  let z25_part := toBitVecValue 64 #v[(((ph (X 0 5) (Y 0 2)) + ((ph (X 0 4) (Y 0 3) + ph (X 0 3) (Y 0 4) + ph (X 0 2) (Y 0 5)) + (pl (X 0 5) (Y 0 3) + pl (X 0 4) (Y 0 4) + pl (X 0 3) (Y 0 5)))) * 128) + ((ph (X 0 1) (Y 0 0) + ph (X 0 0) (Y 0 1)) + (pl (X 0 2) (Y 0 0) + pl (X 0 1) (Y 0 1) + pl (X 0 0) (Y 0 2))), (((ph (X 1 5) (Y 1 2)) + ((ph (X 1 4) (Y 1 3) + ph (X 1 3) (Y 1 4) + ph (X 1 2) (Y 1 5)) + (pl (X 1 5) (Y 1 3) + pl (X 1 4) (Y 1 4) + pl (X 1 3) (Y 1 5)))) * 128) + ((ph (X 1 1) (Y 1 0) + ph (X 1 0) (Y 1 1)) + (pl (X 1 2) (Y 1 0) + pl (X 1 1) (Y 1 1) + pl (X 1 0) (Y 1 2))), (((ph (X 2 5) (Y 2 2)) + ((ph (X 2 4) (Y 2 3) + ph (X 2 3) (Y 2 4) + ph (X 2 2) (Y 2 5)) + (pl (X 2 5) (Y 2 3) + pl (X 2 4) (Y 2 4) + pl (X 2 3) (Y 2 5)))) * 128) + ((ph (X 2 1) (Y 2 0) + ph (X 2 0) (Y 2 1)) + (pl (X 2 2) (Y 2 0) + pl (X 2 1) (Y 2 1) + pl (X 2 0) (Y 2 2))), (((ph (X 3 5) (Y 3 2)) + ((ph (X 3 4) (Y 3 3) + ph (X 3 3) (Y 3 4) + ph (X 3 2) (Y 3 5)) + (pl (X 3 5) (Y 3 3) + pl (X 3 4) (Y 3 4) + pl (X 3 3) (Y 3 5)))) * 128) + ((ph (X 3 1) (Y 3 0) + ph (X 3 0) (Y 3 1)) + (pl (X 3 2) (Y 3 0) + pl (X 3 1) (Y 3 1) + pl (X 3 0) (Y 3 2))), ((ph (X 0 5) (Y 0 5)) * 128) + (((ph (X 0 4) (Y 0 0) + ph (X 0 3) (Y 0 1) + ph (X 0 2) (Y 0 2)) + (pl (X 0 5) (Y 0 0) + pl (X 0 4) (Y 0 1) + pl (X 0 3) (Y 0 2))) + ((ph (X 0 1) (Y 0 3) + ph (X 0 0) (Y 0 4)) + (pl (X 0 2) (Y 0 3) + pl (X 0 1) (Y 0 4) + pl (X 0 0) (Y 0 5)))), ((ph (X 1 5) (Y 1 5)) * 128) + (((ph (X 1 4) (Y 1 0) + ph (X 1 3) (Y 1 1) + ph (X 1 2) (Y 1 2)) + (pl (X 1 5) (Y 1 0) + pl (X 1 4) (Y 1 1) + pl (X 1 3) (Y 1 2))) + ((ph (X 1 1) (Y 1 3) + ph (X 1 0) (Y 1 4)) + (pl (X 1 2) (Y 1 3) + pl (X 1 1) (Y 1 4) + pl (X 1 0) (Y 1 5)))), ((ph (X 2 5) (Y 2 5)) * 128) + (((ph (X 2 4) (Y 2 0) + ph (X 2 3) (Y 2 1) + ph (X 2 2) (Y 2 2)) + (pl (X 2 5) (Y 2 0) + pl (X 2 4) (Y 2 1) + pl (X 2 3) (Y 2 2))) + ((ph (X 2 1) (Y 2 3) + ph (X 2 0) (Y 2 4)) + (pl (X 2 2) (Y 2 3) + pl (X 2 1) (Y 2 4) + pl (X 2 0) (Y 2 5)))), ((ph (X 3 5) (Y 3 5)) * 128) + (((ph (X 3 4) (Y 3 0) + ph (X 3 3) (Y 3 1) + ph (X 3 2) (Y 3 2)) + (pl (X 3 5) (Y 3 0) + pl (X 3 4) (Y 3 1) + pl (X 3 3) (Y 3 2))) + ((ph (X 3 1) (Y 3 3) + ph (X 3 0) (Y 3 4)) + (pl (X 3 2) (Y 3 3) + pl (X 3 1) (Y 3 4) + pl (X 3 0) (Y 3 5))))]
  have hz25_part : v86 = z25_part := by quad_vecbin hv86 with quadDualValMem, z25_part, za25, zb25_shl7
  subst hz25_part
  denote_clear v 86 86
  denote_step_all v 87
  let zb25_mul24 := toBitVecValue 64 #v[((ph (X 0 5) (Y 0 2)) + ((ph (X 0 4) (Y 0 3) + ph (X 0 3) (Y 0 4) + ph (X 0 2) (Y 0 5)) + (pl (X 0 5) (Y 0 3) + pl (X 0 4) (Y 0 4) + pl (X 0 3) (Y 0 5)))) * 24, ((ph (X 1 5) (Y 1 2)) + ((ph (X 1 4) (Y 1 3) + ph (X 1 3) (Y 1 4) + ph (X 1 2) (Y 1 5)) + (pl (X 1 5) (Y 1 3) + pl (X 1 4) (Y 1 4) + pl (X 1 3) (Y 1 5)))) * 24, ((ph (X 2 5) (Y 2 2)) + ((ph (X 2 4) (Y 2 3) + ph (X 2 3) (Y 2 4) + ph (X 2 2) (Y 2 5)) + (pl (X 2 5) (Y 2 3) + pl (X 2 4) (Y 2 4) + pl (X 2 3) (Y 2 5)))) * 24, ((ph (X 3 5) (Y 3 2)) + ((ph (X 3 4) (Y 3 3) + ph (X 3 3) (Y 3 4) + ph (X 3 2) (Y 3 5)) + (pl (X 3 5) (Y 3 3) + pl (X 3 4) (Y 3 4) + pl (X 3 3) (Y 3 5)))) * 24, (ph (X 0 5) (Y 0 5)) * 24, (ph (X 1 5) (Y 1 5)) * 24, (ph (X 2 5) (Y 2 5)) * 24, (ph (X 3 5) (Y 3 5)) * 24]
  have hzb25_mul24 : v87 = zb25_mul24 := by quad_vecbin hv87 with quadDualValMem, zb25, zb25_mul24
  subst hzb25_mul24
  denote_clear v 87 87
  denote_step_all v 88
  -- z25: limbs 2 and 5
  let z25 := toBitVecValue 64 #v[((((ph (X 0 5) (Y 0 2)) + ((ph (X 0 4) (Y 0 3) + ph (X 0 3) (Y 0 4) + ph (X 0 2) (Y 0 5)) + (pl (X 0 5) (Y 0 3) + pl (X 0 4) (Y 0 4) + pl (X 0 3) (Y 0 5)))) * 128) + ((ph (X 0 1) (Y 0 0) + ph (X 0 0) (Y 0 1)) + (pl (X 0 2) (Y 0 0) + pl (X 0 1) (Y 0 1) + pl (X 0 0) (Y 0 2)))) + (((ph (X 0 5) (Y 0 2)) + ((ph (X 0 4) (Y 0 3) + ph (X 0 3) (Y 0 4) + ph (X 0 2) (Y 0 5)) + (pl (X 0 5) (Y 0 3) + pl (X 0 4) (Y 0 4) + pl (X 0 3) (Y 0 5)))) * 24), ((((ph (X 1 5) (Y 1 2)) + ((ph (X 1 4) (Y 1 3) + ph (X 1 3) (Y 1 4) + ph (X 1 2) (Y 1 5)) + (pl (X 1 5) (Y 1 3) + pl (X 1 4) (Y 1 4) + pl (X 1 3) (Y 1 5)))) * 128) + ((ph (X 1 1) (Y 1 0) + ph (X 1 0) (Y 1 1)) + (pl (X 1 2) (Y 1 0) + pl (X 1 1) (Y 1 1) + pl (X 1 0) (Y 1 2)))) + (((ph (X 1 5) (Y 1 2)) + ((ph (X 1 4) (Y 1 3) + ph (X 1 3) (Y 1 4) + ph (X 1 2) (Y 1 5)) + (pl (X 1 5) (Y 1 3) + pl (X 1 4) (Y 1 4) + pl (X 1 3) (Y 1 5)))) * 24), ((((ph (X 2 5) (Y 2 2)) + ((ph (X 2 4) (Y 2 3) + ph (X 2 3) (Y 2 4) + ph (X 2 2) (Y 2 5)) + (pl (X 2 5) (Y 2 3) + pl (X 2 4) (Y 2 4) + pl (X 2 3) (Y 2 5)))) * 128) + ((ph (X 2 1) (Y 2 0) + ph (X 2 0) (Y 2 1)) + (pl (X 2 2) (Y 2 0) + pl (X 2 1) (Y 2 1) + pl (X 2 0) (Y 2 2)))) + (((ph (X 2 5) (Y 2 2)) + ((ph (X 2 4) (Y 2 3) + ph (X 2 3) (Y 2 4) + ph (X 2 2) (Y 2 5)) + (pl (X 2 5) (Y 2 3) + pl (X 2 4) (Y 2 4) + pl (X 2 3) (Y 2 5)))) * 24), ((((ph (X 3 5) (Y 3 2)) + ((ph (X 3 4) (Y 3 3) + ph (X 3 3) (Y 3 4) + ph (X 3 2) (Y 3 5)) + (pl (X 3 5) (Y 3 3) + pl (X 3 4) (Y 3 4) + pl (X 3 3) (Y 3 5)))) * 128) + ((ph (X 3 1) (Y 3 0) + ph (X 3 0) (Y 3 1)) + (pl (X 3 2) (Y 3 0) + pl (X 3 1) (Y 3 1) + pl (X 3 0) (Y 3 2)))) + (((ph (X 3 5) (Y 3 2)) + ((ph (X 3 4) (Y 3 3) + ph (X 3 3) (Y 3 4) + ph (X 3 2) (Y 3 5)) + (pl (X 3 5) (Y 3 3) + pl (X 3 4) (Y 3 4) + pl (X 3 3) (Y 3 5)))) * 24), (((ph (X 0 5) (Y 0 5)) * 128) + (((ph (X 0 4) (Y 0 0) + ph (X 0 3) (Y 0 1) + ph (X 0 2) (Y 0 2)) + (pl (X 0 5) (Y 0 0) + pl (X 0 4) (Y 0 1) + pl (X 0 3) (Y 0 2))) + ((ph (X 0 1) (Y 0 3) + ph (X 0 0) (Y 0 4)) + (pl (X 0 2) (Y 0 3) + pl (X 0 1) (Y 0 4) + pl (X 0 0) (Y 0 5))))) + ((ph (X 0 5) (Y 0 5)) * 24), (((ph (X 1 5) (Y 1 5)) * 128) + (((ph (X 1 4) (Y 1 0) + ph (X 1 3) (Y 1 1) + ph (X 1 2) (Y 1 2)) + (pl (X 1 5) (Y 1 0) + pl (X 1 4) (Y 1 1) + pl (X 1 3) (Y 1 2))) + ((ph (X 1 1) (Y 1 3) + ph (X 1 0) (Y 1 4)) + (pl (X 1 2) (Y 1 3) + pl (X 1 1) (Y 1 4) + pl (X 1 0) (Y 1 5))))) + ((ph (X 1 5) (Y 1 5)) * 24), (((ph (X 2 5) (Y 2 5)) * 128) + (((ph (X 2 4) (Y 2 0) + ph (X 2 3) (Y 2 1) + ph (X 2 2) (Y 2 2)) + (pl (X 2 5) (Y 2 0) + pl (X 2 4) (Y 2 1) + pl (X 2 3) (Y 2 2))) + ((ph (X 2 1) (Y 2 3) + ph (X 2 0) (Y 2 4)) + (pl (X 2 2) (Y 2 3) + pl (X 2 1) (Y 2 4) + pl (X 2 0) (Y 2 5))))) + ((ph (X 2 5) (Y 2 5)) * 24), (((ph (X 3 5) (Y 3 5)) * 128) + (((ph (X 3 4) (Y 3 0) + ph (X 3 3) (Y 3 1) + ph (X 3 2) (Y 3 2)) + (pl (X 3 5) (Y 3 0) + pl (X 3 4) (Y 3 1) + pl (X 3 3) (Y 3 2))) + ((ph (X 3 1) (Y 3 3) + ph (X 3 0) (Y 3 4)) + (pl (X 3 2) (Y 3 3) + pl (X 3 1) (Y 3 4) + pl (X 3 0) (Y 3 5))))) + ((ph (X 3 5) (Y 3 5)) * 24)]
  have hz25 : v88 = z25 := by quad_vecbin hv88 with quadDualValMem, z25, z25_part, zb25_mul24
  subst hz25
  denote_clear v 88 88

  -- the three stores. `denote_step_all` stops at %88: a store has an
  -- impure operation, so there is nothing left to push into the
  -- valuation. What remains is to identify the three stored values with
  -- the specification, which is the `lane_*` lemmas above, and then to
  -- read the stores off the denotation.
  have ez03 : z03 = (quadMulResult x y).v03.map PoisonOr.value := by
    apply Vector.ext
    intro i hi
    interval_cases i
    all_goals simp only [quadMulResult, quadVec, toBitVecValue,
      z03, X, Y, quadLimb, vlane, Fin.reduceCastAdd, Fin.reduceAddNat,
      Vector.getElem_map, Vector.getElem_mk, List.getElem_toArray,
      List.getElem_cons_zero, List.getElem_cons_succ,
      lane_0, lane_1, lane_2, lane_3, lane_4, lane_5, lane_6, lane_7]
  have ez14 : z14 = (quadMulResult x y).v14.map PoisonOr.value := by
    apply Vector.ext
    intro i hi
    interval_cases i
    all_goals simp only [quadMulResult, quadVec, toBitVecValue,
      z14, X, Y, quadLimb, vlane, Fin.reduceCastAdd, Fin.reduceAddNat,
      Vector.getElem_map, Vector.getElem_mk, List.getElem_toArray,
      List.getElem_cons_zero, List.getElem_cons_succ,
      lane_8, lane_9, lane_10, lane_11, lane_12, lane_13, lane_14, lane_15]
  have ez25 : z25 = (quadMulResult x y).v25.map PoisonOr.value := by
    apply Vector.ext
    intro i hi
    interval_cases i
    all_goals simp only [quadMulResult, quadVec, toBitVecValue,
      z25, X, Y, quadLimb, vlane, Fin.reduceCastAdd, Fin.reduceAddNat,
      Vector.getElem_map, Vector.getElem_mk, List.getElem_toArray,
      List.getElem_cons_zero, List.getElem_cons_succ,
      lane_16, lane_17, lane_18, lane_19, lane_20, lane_21, lane_22, lane_23]
  simp only [Com.denote_var, Expr.denote_unfold, Expr.denoteOp,
    EffectKind.liftEffect_rfl, simp_denote, storeVec, quadDualValMem,
    Function.comp_def, Ctxt.Valuation.nil_append, map_eq_pure_bind,
    bind_assoc, pure_bind, ez03, ez14, ez25]

/-! ## What the kernel writes

The derivation above says the region *is* three whole-vector stores. Combining
it with `Proof/Mem.lean` turns that into a statement about memory; everything
about the *values* -- ring correctness and the width table -- follows below, on
the three vectors the kernel writes. -/

/-- **The kernel's effect on memory.** Given three live, big-enough
destinations, the region runs without UB and leaves exactly the three
specified vectors behind. No aliasing hypothesis is needed: if two
destinations coincide the later write wins, which is what the nested
`writeVec`s say. -/
theorem run_fd_r43x6_quad_mul_fast (x y : Quad)
    (hx03 : R43x6.U47 x.v03) (hx14 : R43x6.U47 x.v14) (hx25 : R43x6.U47 x.v25)
    (hy03 : R43x6.U47 y.v03) (hy14 : R43x6.U47 y.v14) (hy25 : R43x6.U47 y.v25)
    (p₀ p₁ p₂ : Pointer) (s : GlobalState)
    (h₀ : Fits s.mem p₀ 512)
    (h₁ : Fits (s.mem.writeVec p₀ (quadMulResult x y).v03) p₁ 512)
    (h₂ : Fits ((s.mem.writeVec p₀ (quadMulResult x y).v03).writeVec p₁
      (quadMulResult x y).v14) p₂ 512) :
    (fd_r43x6_quad_mul_fast.denote
        (quadDualValMem (.value p₀) (.value p₁) (.value p₂) x y)).run s
      = .value (HVector.nil,
          { s with mem := ((s.mem.writeVec p₀ (quadMulResult x y).v03).writeVec p₁
              (quadMulResult x y).v14).writeVec p₂ (quadMulResult x y).v25 }) := by
  rw [denote_fd_r43x6_quad_mul_fast x y hx03 hx14 hx25 hy03 hy14 hy25]
  exact run_storeVec3 h₀ h₁ h₂

/-- **Correctness, against memory.** Given three live, big-enough and pairwise
distinct destinations, the region runs without UB and each pointer afterwards
addresses the vector the specification predicts for it.

The distinctness hypotheses are an assumption about the *caller*: the kernel's
pointer parameters carry `nocapture noundef writeonly` and not `noalias`, so
nothing in the IR rules out aliasing. At the one call site,
`FD_R43X6_QUAD_MUL_FAST` passes `&_R03, &_R14, &_R25` -- three distinct
locals. -/
theorem fd_r43x6_quad_mul_fast_readback (x y : Quad)
    (hx03 : R43x6.U47 x.v03) (hx14 : R43x6.U47 x.v14) (hx25 : R43x6.U47 x.v25)
    (hy03 : R43x6.U47 y.v03) (hy14 : R43x6.U47 y.v14) (hy25 : R43x6.U47 y.v25)
    (p₀ p₁ p₂ : Pointer) (s : GlobalState)
    (h₀ : Fits s.mem p₀ 512) (h₁ : Fits s.mem p₁ 512) (h₂ : Fits s.mem p₂ 512)
    (d₀₁ : p₀.id ≠ p₁.id) (d₀₂ : p₀.id ≠ p₂.id) (d₁₂ : p₁.id ≠ p₂.id) :
    let m' := ((s.mem.writeVec p₀ (quadMulResult x y).v03).writeVec p₁
      (quadMulResult x y).v14).writeVec p₂ (quadMulResult x y).v25
    (fd_r43x6_quad_mul_fast.denote
          (quadDualValMem (.value p₀) (.value p₁) (.value p₂) x y)).run s
        = .value (HVector.nil, { s with mem := m' })
      ∧ (SLLVM.load (.value p₀) QVecTy).run m'
          = .value ((quadMulResult x y).v03.map PoisonOr.value, m')
      ∧ (SLLVM.load (.value p₁) QVecTy).run m'
          = .value ((quadMulResult x y).v14.map PoisonOr.value, m')
      ∧ (SLLVM.load (.value p₂) QVecTy).run m'
          = .value ((quadMulResult x y).v25.map PoisonOr.value, m') := by
  refine ⟨run_fd_r43x6_quad_mul_fast x y hx03 hx14 hx25 hy03 hy14 hy25 p₀ p₁ p₂ s h₀
      (fits_splice h₁) (fits_splice (fits_splice h₂)), ?_⟩
  exact storeVec3_readback h₀ h₁ h₂ d₀₁ d₀₂ d₁₂

/-! ## What the kernel computes

Stated per QUAD lane `j : Fin 4`, since the kernel is four independent
multiplies. -/

/-- Reading element `j` back out of the result QUAD recovers the specified
limbs. -/
theorem quadMul_limbs (x y : Quad)
    (hx03 : R43x6.U47 x.v03) (hx14 : R43x6.U47 x.v14) (hx25 : R43x6.U47 x.v25)
    (hy03 : R43x6.U47 y.v03) (hy14 : R43x6.U47 y.v14) (hy25 : R43x6.U47 y.v25)
    (j : Fin 4) (k : Fin 6) :
    quadLimb (quadMulResult x y).v03 (quadMulResult x y).v14 (quadMulResult x y).v25 j k
      = quadMulLimb x y j k :=
  quadLimb_quadVec (quadMulLimb x y) j k (fun i k' => by
    have := quadMulLimb_lt_two_pow_63 x y hx03 hx14 hx25 hy03 hy14 hy25 i k'
    omega)

/-- **Correctness.** In each of the four QUAD lanes, the limbs the kernel
produces decode to the product of the two decoded inputs in `GF(2^255 - 19)`. -/
theorem quadMul_zmod (x y : Quad) (j : Fin 4) :
    ((decodeNat (quadMulLimb x y j) : ℕ) : ZMod p)
      = ((decodeNat (laneFunc (x.vector j)) : ℕ) : ZMod p)
        * ((decodeNat (laneFunc (y.vector j)) : ℕ) : ZMod p) :=
  decodeLimbs_quadMulLimb_zmod x y j

/-! ## Output bounds

The `fd_r43x6.h` width table, on each of the three vectors the kernel writes. -/

private theorem quadMul_bounds_of (x y : Quad) (N : ℕ) (hN : N ≤ 2 ^ 63)
    (hb : ∀ (j : Fin 4) (k : Fin 6), quadMulLimb x y j k < N) :
    (R43x6.BoundedUpper ((N : Int) - 1) (quadMulResult x y).v03
      ∧ R43x6.BoundedLower 0 (quadMulResult x y).v03)
    ∧ (R43x6.BoundedUpper ((N : Int) - 1) (quadMulResult x y).v14
      ∧ R43x6.BoundedLower 0 (quadMulResult x y).v14)
    ∧ (R43x6.BoundedUpper ((N : Int) - 1) (quadMulResult x y).v25
      ∧ R43x6.BoundedLower 0 (quadMulResult x y).v25) :=
  ⟨quadVec_bounds _ 0 3 N hN (fun j => ⟨hb j 0, hb j 3⟩),
   quadVec_bounds _ 1 4 N hN (fun j => ⟨hb j 1, hb j 4⟩),
   quadVec_bounds _ 2 5 N hN (fun j => ⟨hb j 2, hb j 5⟩)⟩

/-- **`u47` in, `u63` out**, on every vector the kernel writes. -/
theorem quadMul_u47_u63 (x y : Quad)
    (hx03 : R43x6.U47 x.v03) (hx14 : R43x6.U47 x.v14) (hx25 : R43x6.U47 x.v25)
    (hy03 : R43x6.U47 y.v03) (hy14 : R43x6.U47 y.v14) (hy25 : R43x6.U47 y.v25)
    :
    R43x6.U63 (quadMulResult x y).v03 ∧ R43x6.U63 (quadMulResult x y).v14
      ∧ R43x6.U63 (quadMulResult x y).v25 := by
  have := quadMul_bounds_of x y (2 ^ 63) (by omega)
    (fun j k => quadMulLimb_lt_u47 x y hx03 hx14 hx25 hy03 hy14 hy25 j k)
  exact_mod_cast this

/-- **`u44` in, `u62` out**, on every vector the kernel writes. -/
theorem quadMul_u44_u62 (x y : Quad)
    (hx03 : R43x6.U44 x.v03) (hx14 : R43x6.U44 x.v14) (hx25 : R43x6.U44 x.v25)
    (hy03 : R43x6.U44 y.v03) (hy14 : R43x6.U44 y.v14) (hy25 : R43x6.U44 y.v25)
    :
    R43x6.U62 (quadMulResult x y).v03 ∧ R43x6.U62 (quadMulResult x y).v14
      ∧ R43x6.U62 (quadMulResult x y).v25 := by
  have := quadMul_bounds_of x y (2 ^ 62) (by omega)
    (fun j k => quadMulLimb_lt_u44 x y hx03 hx14 hx25 hy03 hy14 hy25 j k)
  exact_mod_cast this

end Firedancer.Avx512
