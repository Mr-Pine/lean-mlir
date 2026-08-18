/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.SLLVM.Dialect

/-!
# Reading a poison-carrying denotation back as plain values

A lifted SLLVM program denotes a `vector<8xi64>` as `Vector (PoisonOr (BitVec
64)) 8`, while the ℕ-level specifications (`R43x6.decode'` and friends) are
stated over plain `BitVec`s. `Vector.getValues` bridges the two.

Poison is *not* given a fallback value. A lane that is poison makes the whole
read poison, by traversing in the `PoisonOr` monad — so a specification stated
through `getValues` has to conclude `= .value …`, and that conclusion asserts
poison-freedom of every lane on top of the numeric claim. Reading a poison
lane as `default` would instead let a program that produces poison satisfy a
specification about its value, which is exactly the bug this is meant to
prevent.

This is why there is no `[Inhabited α]` here: there is nothing to fall back
to, on purpose.
-/

-- NOTE: `Vector` lives in the root namespace, so this helper does too, which
-- is what makes `result.getValues` work; cf. `Expr.denoteOpPure` in
-- `DenoteStep.lean`.
namespace Vector

/-- The values carried by every lane of `v`, or `poison` if *any* lane is
poison. -/
def getValues (v : Vector (PoisonOr α) n) : PoisonOr (Vector α n) :=
  v.mapM id

/-- Reading back a vector that was built by injecting plain values yields
exactly those values, and in particular is not poison. This is the shape every
`Avx512/Proof/` theorem produces, so it is what connects a denotation theorem
to a specification stated over `BitVec`s. -/
@[simp] theorem getValues_map_value (v : Vector α n) :
    (@Vector.map α (no_index _) n PoisonOr.value v).getValues = .value v := by
--               ^^^^^^^^^^^^^^
-- NOTE: in a denotation goal the element type is not the syntactic
-- `PoisonOr α` but the dialect's `LLVM.Ty.denote (.bitvec 64)`, which is
-- definitionally equal but is what the discr_tree would key on. Leaving it
-- unindexed is what lets this fire on `(… .denote V).head.getValues`; cf.
-- `bind_if_then_poison_eq_ite_bind` in `LeanMLIR/Util/Poison.lean`.
  unfold getValues
  rw [Vector.mapM_map]
  show Vector.mapM (fun x => (pure (id x) : PoisonOr α)) v = _
  rw [Vector.mapM_pure]
  simp

end Vector
