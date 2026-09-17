/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SSA.Projects.Firedancer.Avx512.Proof.Field.fd_r43x6_diagnose
public import SSA.Projects.Firedancer.Avx512.Proof.Fold

/-!
# One `fd_r43x6_diagnose` call, peeled

`Step/fd_r43x6_is_nonzero.lean`'s shape for the sign test. The kernel is pure
and reads no memory, so the only thing that moves is the frame `runFunction`
pops; the state it lands in is an *argument*, as in `sqr_step_of_take`.

Two small bridges live here rather than at either end. `fd_r43x6_diagnose_spec`
states the return value through `HVector.head` -- the kernel returns one `i32`
and the spec reads it off -- while `peel_call` wants the whole `HVector`;
`hvector_single` is that step. And `s62_of_u44` is what lets a folded chain
reach the sign test: `fd_r43x6_diagnose`'s input contract is signed, and every
caller arrives holding the `u44` a fold left.
-/

@[expose] public section

namespace Firedancer.Avx512
open LeanMLIR SLLVM
open InstCombine (LLVM)

/-- A one-element `HVector` is its head. -/
theorem hvector_single {t : SLLVM.Ty} (h : HVector TyDenote.toType [t]) :
    h = [h.head]ₕ := by
  cases h with | cons _ as => cases as; rfl

/-- `u44 ⊆ s62`: what a fold leaves already meets `fd_r43x6_diagnose`'s signed
input contract, so a chain reaches the sign test with no bound re-derived.
`u47_of_u44`'s counterpart at the signed kernels. -/
theorem s62_of_u44 {l : Nat} {x : Vector (BitVec 64) l} (h : R43x6.U44 x) :
    R43x6.S62 x :=
  ⟨fun i => le_trans (h.1 i) (by norm_num),
   fun i => le_trans (by norm_num) (h.2 i)⟩

/-- **One `fd_r43x6_diagnose( x )` call**, in the form `peel_call` takes it:
the `int` the C returns -- `-1` at zero, else the canonical representative's
low bit -- with the state it lands in supplied by the caller. -/
theorem diagnose_step {x : Vector (BitVec 64) 8}
    (hx : R43x6.S62 (x.take R43x6.limbCount))
    (u u' : GlobalState) (hu' : u' = u.popFrame u.mem) :
    StateT.run (runFunction (fd_r43x6_diagnose_cfg.denote
        (Ctxt.Valuation.ofHVector [x.map PoisonOr.value]ₕ))) u
      = .value ([PoisonOr.value (diagnose (R43x6.extractLimbs x))]ₕ, u') := by
  rw [hu']
  refine run_runFunction ?_
  simp only [fd_r43x6_diagnose_cfg, Cfg.denote_ofCom, Com.denote_castPureToEff]
  show StateT.run (pure (fd_r43x6_diagnose.denote
    (Ctxt.Valuation.singleton (x.map PoisonOr.value)))) u = _
  rw [hvector_single (fd_r43x6_diagnose.denote
      (Ctxt.Valuation.singleton (x.map PoisonOr.value))),
    fd_r43x6_diagnose_conforms x hx]
  simp only [EffectM.run_pure]

end Firedancer.Avx512
