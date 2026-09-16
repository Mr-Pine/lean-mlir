/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.SLLVM.Dialect
import SSA.Projects.Firedancer.Common.Mlir.Scalar.fd_curve25519_scalar_reduce
import SSA.Projects.Firedancer.Proof.Memory
import SSA.Projects.Firedancer.Common.Spec.Scalar.fd_curve25519_scalar_validate

/-!
# `fd_curve25519_scalar_reduce` (common)

The C computes `out = in mod ℓ`. That value is not specified here.
`ScalarReduceDetermined` says only that the call is decided by the 512 bits at `in`: one
function of those bits gives both whether the run returns and the four `i64`s it then stores.
That is what a comparison of two callers needs. Nothing proves it yet.

What is proved is `fd_curve25519_scalar_reduce_frame_spec`, the footprint: a run that returns
leaves the entry state plus the four stores. It allows poison, since with the digit bounds
unproved an `nsw` operation may be poison, and `SLLVM.store` takes `getOrUB` of its value.
-/

namespace Firedancer.Common

open LeanMLIR SLLVM
open InstCombine (LLVM)

/-- The four `i64` stores the region ends with, at `out + 0, 8, 16, 24`.

A `def`, not an `abbrev`, for the reason `pointOutMem` is one: reducible, every
unifier that meets it walks four splices. -/
def scalarOutMem (m : MemoryState) (r : Pointer) (w : Fin 4 → BitVec 64) : MemoryState :=
  (((m.splice r (w 0)).splice (r.withOffset 8) (w 1)).splice (r.withOffset 16) (w 2)).splice
    (r.withOffset 24) (w 3)

/-- The four words as one 256-bit little-endian value, `w 3` most significant. -/
def packWords (w : Fin 4 → BitVec 64) : BitVec 256 :=
  w 3 ++ w 2 ++ w 1 ++ w 0

/-- **The call is decided by the 512 bits at `in`.**

`f` says what the region does with those bits: `none` if the run does not return -- poison, or
the undefined behaviour poison collapses to -- and otherwise the four words it stores at `out`.
What those words are is left open, and `in` and `out` may alias.

`in`'s offset may not wrap: `Fits` alone allows a block so long that `in + 8` comes back round
to its start, and the eight loads would then read bytes these 512 bits do not cover. -/
def ScalarReduceBy (f : BitVec (64 * 8) → Option (Fin 4 → BitVec 64)) : Prop :=
  ∀ (out inp : Pointer) (s : GlobalState),
    s.WF →
      IsByteBufPtr s.mem out →
        inp.offset.toNat + 64 ≤ 2 ^ 64 →
          ∀ hin : Fits s.mem inp (64 * 8),
            let invocation :=
              runFunction
                (fd_curve25519_scalar_reduce.denote
                  (Ctxt.Valuation.ofHVector [.value inp, .value out]ₕ))
            (∀ w,
                f (readWord hin) = some w →
                  ∃ s' : GlobalState,
                    StateT.run invocation s = .value ([.value out]ₕ, s') ∧
                      s' ≈ ({ s with mem := scalarOutMem s.mem out w } : GlobalState)) ∧
              (f (readWord hin) = none → StateT.run invocation s = .poison)

/-- ... for some such `f`, which the caller then names. -/
def ScalarReduceDetermined : Prop :=
  ∃ f, ScalarReduceBy f

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
  let invocation :=
    runFunction
      (fd_curve25519_scalar_reduce.denote (Ctxt.Valuation.ofHVector [.value inp, .value out]ₕ))
  ∃ res,
    StateT.run invocation s = res ∧
      ∀ s' : GlobalState,
        res = .value ([.value out]ₕ, s') →
          ∃ w : Fin 4 → BitVec 64, s' ≈ ({ s with mem := scalarOutMem s.mem out w } : GlobalState)

end Firedancer.Common
