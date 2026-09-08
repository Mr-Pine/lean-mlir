/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.Firedancer.Avx512.Proof.Fold
import SSA.Projects.Firedancer.Avx512.Proof.Field.fd_r43x6_sqr_fast
import SSA.Projects.Firedancer.Proof.Memory

/-!
# One `fd_r43x6_sqr_fast` call, peeled

The `Ref/Proof/Step/` shape, for the avx512 kernels: the conformance lemma
packaged once into the form a caller's walk consumes, so that no call site
repeats it.

Two things differ from the ref. The kernel is *pure* -- it returns a value
rather than writing an out-parameter -- so the state half is only
`runFunction`'s own frame pop, and there is no `StepFacts` to rebuild. And a
call is never the whole of `FD_R43X6_SQR_INL`: the macro is the call followed
by `fd_r43x6_fold_unsigned`, whose four instructions live in the *caller's*
block. So this file has two halves -- `sqr_step` for the call, which
`peel_call` takes, and `SqrInl` for what the macro leaves once `Fold.lean`'s
`denote_foldVec` has run over those four.

`fd_r43x6_sqr_fast_cfg`, not `fd_r43x6_sqr_fast`, is what a caller's call node
holds -- a callee bound by `@fd_r43x6_sqr_fast := fd_r43x6_sqr_fast_cfg` in
`sllvm_cfg_of`. `peel_call` keys its by-reference step lemmas on that
constant, so the run equation has to be stated over it too; over the `Com` it
matches nothing and fails.
-/

namespace Firedancer.Avx512
open LeanMLIR SLLVM
open InstCombine (LLVM)

/-- **One `fd_r43x6_sqr_fast( x )` call**, in the form `peel_call` takes it.
The kernel neither allocates nor writes, so the only thing that moves is the
frame `runFunction` pops either way. -/
theorem sqr_step (x : Vector (BitVec 64) 8) (hx : R43x6.Unreduced x) (h7 : x[7] = 0)
    (u : GlobalState) :
    StateT.run (runFunction (fd_r43x6_sqr_fast_cfg.denote
        (Ctxt.Valuation.ofHVector [x.map PoisonOr.value]ₕ))) u
      = .value ([(sqrVec x).map PoisonOr.value]ₕ, u.popFrame u.mem) :=
  run_runFunction (by
    simp only [fd_r43x6_sqr_fast_cfg, Cfg.denote_ofCom, Com.denote_castPureToEff]
    show StateT.run (pure (fd_r43x6_sqr_fast.denote
      (Ctxt.Valuation.singleton (x.map PoisonOr.value)))) u = _
    rw [denote_fd_r43x6_sqr_fast x hx h7]
    simp only [EffectM.run_pure])

/-- `sqr_step`'s contract from the `.take limbCount` form the `fd_r43x6` specs
state, with the two zero lanes the kernel also wants -- and the state it lands
in taken as an *argument* rather than written out.

That last part is not cosmetic. `peel_call` puts this state into the goal, and
every later call, load and pop is an `isDefEq` against it. Given the term, the
caller has to name it with `set`, which abstracts the occurrence over the whole
goal -- and on this region that traversal alone is 43s. Given a local plus
`hu'`, the goal carries an opaque `fvar` from the start and nothing has to be
traversed at all. -/
theorem sqr_step_of_take {x : Vector (BitVec 64) 8}
    (hx : R43x6.U47 (x.take R43x6.limbCount)) (h6 : x[6] = 0) (h7 : x[7] = 0)
    (u u' : GlobalState) (hu' : u' = u.popFrame u.mem) :
    StateT.run (runFunction (fd_r43x6_sqr_fast_cfg.denote
        (Ctxt.Valuation.ofHVector [x.map PoisonOr.value]ₕ))) u
      = .value ([(sqrVec x).map PoisonOr.value]ₕ, u') := by
  rw [hu']; exact sqr_step x (UNN_of_take hx h6 h7) h7 u

/-- The bound `Fold.lean`'s `denote_foldVec` and `vecValue_foldVec` take: the
squaring's own limbs are below `2 ^ 63`, so the fold applies to them. -/
theorem limbNat_sqr_lt {x : Vector (BitVec 64) 8}
    (hx : R43x6.U47 (x.take R43x6.limbCount)) (i : Fin 6) :
    limbNat (sqrVec x) i < 2 ^ 63 :=
  limbNat_sqrVec_lt (limbNat_lt_of_take (by omega) hx) i

/-- **What one `FD_R43X6_SQR_INL( z, x )` leaves.** `u44` is what the fold
promises; `u47` is that weakened to the input contract of the *next* kernel,
and is why a chain of these stays in contract without a bound ever being
re-derived. -/
structure SqrInl (x z : Vector (BitVec 64) 8) : Prop where
  /-- `fd_r43x6_sqr_fast`/`fd_r43x6_mul_fast`'s input bound. -/
  u47 : R43x6.U47 (z.take R43x6.limbCount)
  /-- The tighter bound the fold leaves. -/
  u44 : R43x6.U44 (z.take R43x6.limbCount)
  /-- Lane 6 of an `fd_r43x6_t` is zero. -/
  z6 : z[6] = 0
  /-- Lane 7 of an `fd_r43x6_t` is zero: the next kernel's `h7`. -/
  z7 : z[7] = 0
  /-- The element it holds. -/
  value : vecValue z = vecValue x ^ 2

/-- `u44 ⊆ u47`: the fold's output is the next kernel's input. -/
theorem u47_of_u44 {l : Nat} {x : Vector (BitVec 64) l} (h : R43x6.U44 x) :
    R43x6.U47 x :=
  ⟨fun i => le_trans (h.1 i) (by norm_num), h.2⟩

/-- **`FD_R43X6_SQR_INL` conforms**: the call of `sqr_step` and the fold of
`Fold.lean`, at the ℕ level, with nothing about the program left. -/
theorem sqr_inl {x : Vector (BitVec 64) 8} (hx : R43x6.U47 (x.take R43x6.limbCount)) :
    SqrInl x (foldVec (sqrVec x)) :=
  let hb := limbNat_lt_of_take (by omega) hx
  { u47 := u47_of_u44 (UNN_take (foldVec_sqrVec_u44 hb))
    u44 := UNN_take (foldVec_sqrVec_u44 hb)
    z6 := foldVec_getElem_six _
    z7 := foldVec_getElem_seven _
    value := vecValue_foldVec_sqrVec hb }

end Firedancer.Avx512
