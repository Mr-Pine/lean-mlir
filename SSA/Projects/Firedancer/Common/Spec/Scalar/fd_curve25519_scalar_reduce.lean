/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.SLLVM.Dialect
import SSA.Projects.Firedancer.Common.Mlir.Scalar.fd_curve25519_scalar_reduce
import SSA.Projects.Firedancer.Proof.Memory

/-!
# `fd_curve25519_scalar_reduce` (common) -- the memory footprint

`out = in mod l` is *not* what this file states. What it states is the weaker
claim that the region's only effect on memory is four `i64` stores through
`out`: the run either goes to poison, or it returns `out` and leaves a state
equivalent to the entry state with those four stores applied.

Nothing here says what the four words are. Pinning them is the arithmetic --
the twenty-four 21-bit digits, the reduction rows and the carry chains -- and
that is a much larger job: 224 of the region's operations carry `nsw`, 42 also
`nuw`, and every one is poison unless a bound on the digits is discharged.
That work is parked on the `wip/scalar-reduce-arithmetic` branch, which carries
the lift, the full `out = in mod l` specification and a derivation reaching the
first reduction row, along with the two-sided `toInt` overflow lemmas it needs.
Pick it up there if it is ever worth finishing.

The poison disjunct is not a weakness of the proof but the honest reading of a
region this heavily flagged: with the digit bounds unproved, an `nsw` operation
*may* be poison as far as this statement is concerned, and a poison value
reaching a store is UB (`SLLVM.store` takes `getOrUB` of the flattened value).
So "not poison" is exactly "the arithmetic did not overflow", and on that
branch the memory footprint is as stated.
-/

namespace Firedancer.Common
open LeanMLIR SLLVM
open InstCombine (LLVM)

/-- A 64-byte little-endian scalar at `p`, the input's shape. -/
abbrev IsScalar512Ptr (m : MemoryState) (p : Pointer) : Prop :=
  Fits m p (64 * 8) ∧ p.offset.toNat + 64 ≤ 2 ^ 64

/-- A 32-byte little-endian scalar at `p`, the output's shape. -/
abbrev IsScalar256Ptr (m : MemoryState) (p : Pointer) : Prop :=
  Fits m p (32 * 8) ∧ p.offset.toNat + 32 ≤ 2 ^ 64

/-- The four `i64` stores the region ends with, at `out + 0, 8, 16, 24`.

A `def`, not an `abbrev`, for the reason `pointOutMem` is one: reducible, every
unifier that meets it walks four splices. -/
def scalarOutMem (m : MemoryState) (r : Pointer) (w : Fin 4 → BitVec 64) : MemoryState :=
  (((m.splice r (w 0)).splice (r.withOffset 8) (w 1)).splice
    (r.withOffset 16) (w 2)).splice (r.withOffset 24) (w 3)

/-- **The region writes nowhere but `out`.**

Whatever the run produces, if it produces a value at all then the state it
leaves is the entry state plus the four stores, with the allocation counter, the
symbol table and every other block untouched.

The result is named by `res` and the run pinned to it in one conjunct, so the
run term occurs exactly once. A walk can then step that conjunct in place and
decide what `res` is at the instruction that forces the question -- the first
store handed a poison value -- rather than committing to poison or value before
the walk begins. Phrasing this as `run = .poison ∨ ∃ s', run = .value …` instead
would repeat the run in both disjuncts, which is what makes that form awkward to
step.

Poison is therefore not excluded, it is simply not informative: with the digit
bounds unproved an `nsw` operation may be poison, and `SLLVM.store` takes
`getOrUB` of the value it is handed, so a poison operand sends the whole run to
poison and the implication below is vacuous. On any run that does return, the
footprint is as stated.

`in` and `out` may alias; `fd_curve25519_scalar.h` documents in-place operation
as fine, and nothing here forbids it. The eight loads all precede the first
store, which is why that is sound. -/
abbrev fd_curve25519_scalar_reduce_frame_spec (out inp : Pointer) (s : GlobalState) : Prop :=
  let invocation := runFunction (fd_curve25519_scalar_reduce.denote
    (Ctxt.Valuation.ofHVector [.value inp, .value out]ₕ))

  ∃ res, StateT.run invocation s = res
    ∧ ∀ s' : GlobalState, res = .value ([.value out]ₕ, s') →
        ∃ w : Fin 4 → BitVec 64,
          s' ≈ ({ s with mem := scalarOutMem s.mem out w } : GlobalState)

end Firedancer.Common
