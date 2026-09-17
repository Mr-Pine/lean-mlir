/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SSA.Projects.Firedancer.Avx512.Proof.Fold
public import SSA.Projects.Firedancer.Avx512.Proof.Field.fd_r43x6_mul_fast
public import SSA.Projects.Firedancer.Avx512.Proof.Step.fd_r43x6_sqr_fast

/-!
# One `fd_r43x6_mul_fast` call, peeled

`Step/fd_r43x6_sqr_fast.lean` for the multiply: `mul_step` is the call in the
form `peel_call` takes it, and `MulInl` is what the whole
`FD_R43X6_MUL_INL( z, x, y )` leaves once `Fold.lean`'s `denote_foldVec` has
run over the four fold instructions that follow it in the caller's block.

The kernel's contract is asymmetric -- `x` needs only `u47`, while `y` also
needs its two ignored lanes zero, because the accumulators multiply against
them -- so `mul_inl` takes the two operands' hypotheses separately.
-/

@[expose] public section

namespace Firedancer.Avx512
open LeanMLIR SLLVM
open InstCombine (LLVM)

/-- **One `fd_r43x6_mul_fast( x, y )` call**, in the form `peel_call` takes
it. Operands enter the callee's valuation in reverse, so `y` comes first. -/
theorem mul_step (x y : Vector (BitVec 64) 8)
    (hx : R43x6.Unreduced x) (hy : R43x6.Unreduced y) (hy6 : y[6] = 0) (hy7 : y[7] = 0)
    (u : GlobalState) :
    StateT.run (runFunction (fd_r43x6_mul_fast_cfg.denote
        (Ctxt.Valuation.ofHVector [y.map PoisonOr.value, x.map PoisonOr.value]ₕ))) u
      = .value ([(mulVec x y).map PoisonOr.value]ₕ, u.popFrame u.mem) :=
  run_runFunction (by
    simp only [fd_r43x6_mul_fast_cfg, Cfg.denote_ofCom, Com.denote_castPureToEff]
    show StateT.run (pure (fd_r43x6_mul_fast.denote
      (Ctxt.Valuation.ofPair (y.map PoisonOr.value) (x.map PoisonOr.value)))) u = _
    rw [denote_fd_r43x6_mul_fast x y hx hy hy6 hy7]
    simp only [EffectM.run_pure])

/-- `mul_step`'s contract from the `.take limbCount` form the `fd_r43x6` specs
state, with the zero lanes each operand needs -- and, as in
`sqr_step_of_take`, the state it lands in taken as an *argument* rather than
written out, so a block that chains calls carries `fvar`s and no later
`isDefEq` walks a tower of `popFrame`s. -/
theorem mul_step_of_take {x y : Vector (BitVec 64) 8}
    (hx : R43x6.U47 (x.take R43x6.limbCount)) (hx6 : x[6] = 0) (hx7 : x[7] = 0)
    (hy : R43x6.U47 (y.take R43x6.limbCount)) (hy6 : y[6] = 0) (hy7 : y[7] = 0)
    (u u' : GlobalState) (hu' : u' = u.popFrame u.mem) :
    StateT.run (runFunction (fd_r43x6_mul_fast_cfg.denote
        (Ctxt.Valuation.ofHVector [y.map PoisonOr.value, x.map PoisonOr.value]ₕ))) u
      = .value ([(mulVec x y).map PoisonOr.value]ₕ, u') := by
  rw [hu']
  exact mul_step x y (UNN_of_take hx hx6 hx7) (UNN_of_take hy hy6 hy7) hy6 hy7 u

/-- The bound `Fold.lean`'s `denote_foldVec` takes: the product's own limbs
are below `2 ^ 63`, so the fold applies to them. -/
theorem limbNat_mul_lt {x y : Vector (BitVec 64) 8}
    (hx : R43x6.U47 (x.take R43x6.limbCount)) (hy : R43x6.U47 (y.take R43x6.limbCount))
    (i : Fin 6) : limbNat (mulVec x y) i < 2 ^ 63 :=
  limbNat_mulVec_lt (limbNat_lt_of_take (by omega) hx) (limbNat_lt_of_take (by omega) hy) i

/-- **What one `FD_R43X6_MUL_INL( z, x, y )` leaves.** `SqrInl`'s counterpart:
`u44` is what the fold promises, `u47` is that weakened to the next kernel's
input contract, and the two zero lanes come free from `limbVec`. -/
structure MulInl (x y z : Vector (BitVec 64) 8) : Prop where
  /-- `fd_r43x6_sqr_fast`/`fd_r43x6_mul_fast`'s input bound. -/
  u47 : R43x6.U47 (z.take R43x6.limbCount)
  /-- The tighter bound the fold leaves -- what `fd_r43x6.h` promises. -/
  u44 : R43x6.U44 (z.take R43x6.limbCount)
  /-- Lane 6 of an `fd_r43x6_t` is zero. -/
  z6 : z[6] = 0
  /-- Lane 7 of an `fd_r43x6_t` is zero. -/
  z7 : z[7] = 0
  /-- The element it holds. -/
  value : vecValue z = vecValue x * vecValue y

/-- **`FD_R43X6_MUL_INL` conforms**: the call of `mul_step` and the fold of
`Fold.lean`, at the ℕ level, with nothing about the program left. -/
theorem mul_inl {x y : Vector (BitVec 64) 8}
    (hx : R43x6.U47 (x.take R43x6.limbCount)) (hy : R43x6.U47 (y.take R43x6.limbCount)) :
    MulInl x y (foldVec (mulVec x y)) :=
  let hbx := limbNat_lt_of_take (n := 47) (by omega) hx
  let hby := limbNat_lt_of_take (n := 47) (by omega) hy
  { u47 := u47_of_u44 (UNN_take (foldVec_mulVec_u44 hbx hby))
    u44 := UNN_take (foldVec_mulVec_u44 hbx hby)
    z6 := foldVec_getElem_six _
    z7 := foldVec_getElem_seven _
    value := vecValue_foldVec_mulVec hbx hby }

end Firedancer.Avx512
