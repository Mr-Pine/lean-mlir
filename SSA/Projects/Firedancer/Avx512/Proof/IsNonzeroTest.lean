/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.Firedancer.Avx512.Mlir.Field.fd_r43x6_is_nonzero
import SSA.Projects.Firedancer.Avx512.Spec.Field.fd_r43x6_is_nonzero

/-!
# The lifted `fd_r43x6_is_nonzero` against its specification

A differential check: the lifted region
evaluated against the `ℤ`-level model of `Spec/fd_r43x6_is_nonzero.lean`, on
the inputs that matter.

`denote_fd_r43x6_is_nonzero` proves that the region and the model agree in
general, so nothing here is load-bearing. What the guards give is a cheap
regression check that runs by evaluation: if a change to the model or to the
lifting made the two disagree, these fail in seconds rather than in the middle
of the eighty-step derivation. The inputs are the ones the two are easiest to
disagree on -- zero, the non-trivial nearly reduced representation of `p`, and
a negative limb -- none of which random testing reaches.

Both sides are closed terms, so `decide` settles them.
-/

namespace Firedancer.Avx512
open LeanMLIR

/-- The lifted program's answer on a concrete input. -/
private def run (x : Vector (BitVec 64) 8) : PoisonOr (BitVec 32) :=
  (fd_r43x6_is_nonzero.denote (Ctxt.Valuation.singleton (x.map PoisonOr.value))).head

/-- The model's answer on the same input. -/
private def model (x : Vector (BitVec 64) 8) : PoisonOr (BitVec 32) :=
  .value (isNonzero (R43x6.extractLimbs x))

private def zeroV : Vector (BitVec 64) 8 := #v[0, 0, 0, 0, 0, 0, 0, 0]
private def oneV : Vector (BitVec 64) 8 := #v[1, 0, 0, 0, 0, 0, 0, 0]
private def negOneV : Vector (BitVec 64) 8 := #v[-1, 0, 0, 0, 0, 0, 0, 0]

/-- `fd_r43x6_p()`: the non-trivial nearly reduced representation of `p`. -/
private def pV : Vector (BitVec 64) 8 :=
  #v[2^43 - 19, 2^43 - 1, 2^43 - 1, 2^43 - 1, 2^43 - 1, 2^40 - 1, 0, 0]

/-- A value congruent to zero that is not syntactically zero: `p` again, with
limb 0 carrying the whole of it. -/
private def bigV : Vector (BitVec 64) 8 := #v[2^61, 2^61, 2^61, 2^61, 2^61, 2^61, 0, 0]

/-! ## The program agrees with the model -/

#guard run zeroV == model zeroV
#guard run oneV == model oneV
#guard run negOneV == model negOneV
#guard run pV == model pV
#guard run bigV == model bigV

/-! ## …and the answers are the expected ones

Stated separately, so that a model and a program that agreed on a *wrong*
answer would still be caught. -/

#guard run zeroV == .value 0#32
#guard run pV == .value 0#32
#guard run oneV == .value 1#32
#guard run negOneV == .value 1#32

end Firedancer.Avx512
