/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SSA.Projects.Firedancer.Avx512.Spec.Field.fd_r43x6_biased_carry_propagate_limbs
public import SSA.Projects.Firedancer.Avx512.Spec.Field.fd_r43x6_mod_nearly_reduced_limbs
public import Mathlib.Data.ZMod.Basic
-- callee bindings are evaluated while elaborating
public meta import SSA.Projects.Firedancer.Avx512.Spec.Field.fd_r43x6_biased_carry_propagate_limbs
public meta import SSA.Projects.Firedancer.Avx512.Spec.Field.fd_r43x6_mod_nearly_reduced_limbs

/-!
# What `fd_r43x6_is_nonzero` is specified to compute

`fd_r43x6_is_nonzero` is the first `fd_r43x6` operation here that returns a
*decision* rather than a field element, and the first with no vector data flow
at all. It extracts the six limbs out of the `<8 x i64>` and from there is
scalar code over `long`s: a biased serial carry propagate
(`fd_r43x6_biased_carry_propagate_limbs` at `b = 2^20`) followed by the
conditional subtract of `p` (`fd_r43x6_mod_nearly_reduced_limbs`), and then a
test of whether the six resulting limbs are all zero.

The two macros are modelled and proved a file each --
`Spec/fd_r43x6_biased_carry_propagate_limbs.lean`,
`Spec/fd_r43x6_mod_nearly_reduced_limbs.lean` and the corresponding `Proof/`
files -- because nine other `fd_r43x6` operations expand them. What is left
here is only what is specific to `fd_r43x6_is_nonzero`: the composition of the
two, the decision read off the end, and the obligations.

That pair is the only place in the backend that reduces to the canonical
representative. `fd_r43x6_diagnose` reads the low bit off the end of the same
chain and `fd_r43x6_mod` returns it whole, so the composition is named
`reduce` here rather than folded into `isNonzero`.

## Two things make this unlike `mul_fast`/`sqr_fast`

* **The arithmetic is signed.** The input is in `s62`, the shifts in both
  chains are arithmetic, and that is exactly what makes a negative limb borrow
  correctly. The model is therefore over `R43x6.decodeLimbs` at `ℤ`, where
  `mul_fast` and `sqr_fast` use it at `ℕ`. Nothing in the representation
  distinguishes the two readings: which one applies is part of an operation's
  contract.

* **The precondition is needed by the compiled code, not just by the
  specification.** Every add, subtract and multiply in the two chains is
  emitted `nsw`, and lean-mlir's `LLVM.add` yields *poison* on signed overflow
  (`Dialects/LLVM/Semantics.lean:143`). So the program does not even denote to
  a value without an input range that rules the overflows out. `BcpPre (2^20)`
  is that range, `R43x6.FitsLong` is what it buys, and `ChainFitsLong` below
  is a proof obligation of the *denotation*, not of the arithmetic. `mul_fast`
  and `sqr_fast` had no counterpart: every flag in those two regions is
  `overflow<none>`.

There is also no lane form to recover -- no permutes, no masks, no `alignr` --
so this file has no `<op>_lanes` layer and no `pl`/`ph` column sums.

## The program

`Avx512/Mlir/fd_r43x6_is_nonzero.lean` holds the region as an `[sllvm| … ]`
quotation, verbatim from the build artifact
`build/native/gcc/mlir_canonicalized/avx512/region/fd_r43x6_is_nonzero.mlir`, which is
checked in beside it. Its one callee is `fd_long_if`, lifted in
`Mlir/fd_long_if.lean` and proved in `Proof/fd_long_if.lean`.

## The obligations

Stated as `Prop`-valued definitions at the end of the file, in the style
`Proof/fd_r43x6_sqr_fast.lean` uses for its four width guarantees, and
discharged in `Proof/fd_r43x6_is_nonzero.lean` from the two macro proofs.
`ReducePreservesValue` together with `ReduceIsCanonical` say the chain
computes *the* canonical representative, not merely that it detects zero.
`IsNonzeroDecides` is the corollary the callers (`fd_r43x6_ge_is_eq`,
`fd_r43x6_ge_is_small_order`) actually want, and it needs canonicity: a
limb-wise compare against zero decides the element only once the
representation is known to be the unique one.
-/

@[expose] public section

namespace Firedancer.Avx512

/-- The two macros chained, at the bias `fd_r43x6_is_nonzero` and
`fd_r43x6_diagnose` use. -/
def reduce (x : Fin R43x6.limbCount → ℤ) : Fin R43x6.limbCount → ℤ :=
  mnr (bcp (2 ^ 20) x)

/-- The answer read off the end: `!!(l0|l1|l2|l3|l4|l5)`, as the `i32` the C
returns. The program ORs the limbs bitwise and compares against zero; on the
reduced representation, whose limbs are all non-negative, that is the same as
asking whether every limb is zero. -/
def isNonzero (x : Fin R43x6.limbCount → ℤ) : BitVec 32 :=
  if
      reduce x 0 = 0 ∧
        reduce x 1 = 0 ∧ reduce x 2 = 0 ∧ reduce x 3 = 0 ∧ reduce x 4 = 0 ∧ reduce x 5 = 0 then
    0
  else 1

/-! ## `nsw`/`nuw`: what the denotation needs

Every arithmetic operation in both chains carries `nsw`, so lean-mlir's
semantics turn any overflow into poison before the arithmetic is ever reached.
Part of the second chain carries `nuw` as well. These are the two obligations
that come with that; they are stated here rather than in `Proof/` because they
are determined by the model, not by the lifting. -/

/-- **No `nsw` operand overflows.** What `BcpPre` exists to discharge: until
it holds, the region denotes to poison. -/
def ChainFitsLong (x : Fin R43x6.limbCount → ℤ) : Prop :=
  BcpPre (2 ^ 20) x →
    (∀ v ∈ bcpChain (2 ^ 20) x, R43x6.FitsLong v) ∧
      (∀ v ∈ mnrChain (bcp (2 ^ 20) x), R43x6.FitsLong v)

/-- **No `nuw` operand wraps, and no `lshr` is on a negative value.** The
`x + 19` chain of `fd_r43x6_mod_nearly_reduced_limbs` -- `mnrA`, `%39`-`%56`
-- is the part of the region that carries `nuw` on top of `nsw` and shifts
with `lshr` rather than `ashr`; both require it. The borrow chain that follows,
`%61`-`%71`, is `nsw` alone and shifts with `ashr`: `%61` is where the borrow
is taken, and `mnrE _ 1`-`mnrE _ 4` propagate it as `-1`. -/
def MnrChainNonneg (x : Fin R43x6.limbCount → ℤ) : Prop :=
  BcpPre (2 ^ 20) x → ∀ i, 0 ≤ mnrA (bcp (2 ^ 20) x) i

/-! ## The obligations on the arithmetic -/

/-- **The chain preserves the element.** -/
def ReducePreservesValue (x : Fin R43x6.limbCount → ℤ) : Prop :=
  BcpPre (2 ^ 20) x →
    ((R43x6.decodeLimbs (reduce x) : ℤ) : ZMod p) = ((R43x6.decodeLimbs x : ℤ) : ZMod p)

/-- **The chain lands in the `reduced` class of the `fd_r43x6.h` table**:
limbs 0-4 below `2^43`, limb 5 below `2^40`, all non-negative, and the packed
value in `[0,p)`. That is `R43x6.Reduced`, spelled on the limbs rather than
through the predicate, which is stated of a vector -- the reduction returns
six `long`s and never rebuilds one.

With `ReducePreservesValue` the packed bound pins the output down to *the*
canonical representative -- `decodeLimbs (reduce x)` is `decodeLimbs x % p` on
the nose -- rather than merely bounding it. The limb widths are what the final
`or`-against-zero needs; the packed bound is what canonicity needs. -/
def ReduceIsCanonical (x : Fin R43x6.limbCount → ℤ) : Prop :=
  BcpPre (2 ^ 20) x →
    (∀ i : Fin R43x6.limbCount, (i : ℕ) < 5 → 0 ≤ reduce x i ∧ reduce x i < 2 ^ 43) ∧
      (0 ≤ reduce x 5 ∧ reduce x 5 < 2 ^ 40) ∧
      (0 ≤ R43x6.decodeLimbs (reduce x) ∧ R43x6.decodeLimbs (reduce x) < (p : ℤ))

/-- **The decision is the right one.** The corollary the callers want; it
needs `ReduceIsCanonical` as well as `ReducePreservesValue`, since a limb-wise
compare against zero decides the *element* only once the representation is
known to be unique. -/
def IsNonzeroDecides (x : Fin R43x6.limbCount → ℤ) : Prop :=
  BcpPre (2 ^ 20) x → (isNonzero x = 0 ↔ ((R43x6.decodeLimbs x : ℤ) : ZMod p) = 0)

/-- **The decision, on the vector the C takes.** `IsNonzeroDecides` phrased
over the argument of `fd_r43x6_is_nonzero` rather than over its extracted
limbs: `x.take limbCount` is the `fd_r43x6_t` proper, so the `s62` contract
says nothing about lanes 6 and 7, which the operation never reads. -/
def IsNonzeroDecidesVec (x : Vector (BitVec 64) 8) : Prop :=
  R43x6.S62 (x.take R43x6.limbCount) →
    (isNonzero (R43x6.extractLimbs x) = 0 ↔ ((R43x6.decode' x : ℤ) : ZMod p) = 0)

/-! ## Sanity checks

The model is executable, so the cases random testing does not reach can be
checked by evaluation rather than argued about. Each is stated through
`R43x6.decodeLimbs`, the value the reduction is supposed to preserve. -/

/-- Zero reduces to zero. -/
example : R43x6.decodeLimbs (reduce (R43x6.limbs6 0 0 0 0 0 0)) = 0 := by decide

/-- `fd_r43x6_p()`, the non-trivial nearly reduced representation of `p` itself,
reduces to zero -- the case a random vector never lands on. -/
example :
    R43x6.decodeLimbs
        (reduce
          (R43x6.limbs6 (2 ^ 43 - 19) (2 ^ 43 - 1) (2 ^ 43 - 1) (2 ^ 43 - 1) (2 ^ 43 - 1)
            (2 ^ 40 - 1))) =
      0 := by
  decide

/-- A negative limb borrows: `-1` reduces to `p - 1 = 2^255 - 20`. -/
example : R43x6.decodeLimbs (reduce (R43x6.limbs6 (-1) 0 0 0 0 0)) = 2 ^ 255 - 20 := by decide

/-- A limb well above `2^43` is carried rather than truncated. -/
example :
    R43x6.decodeLimbs
        (reduce (R43x6.limbs6 (2 ^ 61) (2 ^ 61) (2 ^ 61) (2 ^ 61) (2 ^ 61) (2 ^ 61))) =
      R43x6.decodeLimbs (R43x6.limbs6 (2 ^ 61) (2 ^ 61) (2 ^ 61) (2 ^ 61) (2 ^ 61) (2 ^ 61)) %
        (p : ℤ) := by
  decide

/-- And the decision agrees. -/
example : isNonzero (R43x6.limbs6 0 0 0 0 0 0) = 0 := by decide

example :
    isNonzero
        (R43x6.limbs6 (2 ^ 43 - 19) (2 ^ 43 - 1) (2 ^ 43 - 1) (2 ^ 43 - 1) (2 ^ 43 - 1)
          (2 ^ 40 - 1)) =
      0 := by
  decide

example : isNonzero (R43x6.limbs6 (-1) 0 0 0 0 0) = 1 := by decide

example : isNonzero (R43x6.limbs6 1 0 0 0 0 0) = 1 := by decide

end Firedancer.Avx512
