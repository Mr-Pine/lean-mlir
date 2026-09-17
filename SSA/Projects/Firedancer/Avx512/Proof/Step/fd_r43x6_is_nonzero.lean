/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SSA.Projects.Firedancer.Avx512.Proof.Field.fd_r43x6_is_nonzero

/-!
# One `fd_r43x6_is_nonzero` call, peeled

`Step/fd_r43x6_sqr_fast.lean`'s shape for the decision kernel: pure, so the
only thing that moves is the frame `runFunction` pops.

The value is stated through `spec_denote_fd_r43x6_is_nonzero` rather than
`isNonzero`, so a caller sees the decision the C is entitled to -- `0` exactly
when the element is zero -- and never the reduction chain behind it.

`fd_r43x6_is_nonzero_cfg`, not `fd_r43x6_is_nonzero`, is what a caller's call
node holds, so the run equation is stated over that constant.
-/

@[expose] public section

namespace Firedancer.Avx512
open LeanMLIR SLLVM
open InstCombine (LLVM)

/-- **One `fd_r43x6_is_nonzero( x )` call**, in the form `peel_call` takes it.
The state it lands in is an *argument*, as in `sqr_step_of_take`, so the
caller can name it up front. -/
theorem is_nonzero_step {x : Vector (BitVec 64) 8}
    (hx : R43x6.S62 (x.take R43x6.limbCount))
    (u u' : GlobalState) (hu' : u' = u.popFrame u.mem) :
    StateT.run (runFunction (fd_r43x6_is_nonzero_cfg.denote
        (Ctxt.Valuation.ofHVector [x.map PoisonOr.value]ₕ))) u
      = .value ([PoisonOr.value
          (if ((R43x6.decode' x : ℤ) : ZMod p) = 0 then 0 else 1)]ₕ, u') := by
  rw [hu']
  refine run_runFunction ?_
  simp only [fd_r43x6_is_nonzero_cfg, Cfg.denote_ofCom, Com.denote_castPureToEff]
  show StateT.run (pure (fd_r43x6_is_nonzero.denote
    (Ctxt.Valuation.singleton (x.map PoisonOr.value)))) u = _
  rw [spec_denote_fd_r43x6_is_nonzero x hx]
  simp only [EffectM.run_pure]

end Firedancer.Avx512
