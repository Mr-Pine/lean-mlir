/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SSA.Projects.Firedancer.Avx512.Proof.Field.fd_r43x6_unpack

/-!
# One `fd_r43x6_unpack` call, peeled

`Step/fd_r43x6_sqr_fast.lean`'s shape for the unpack. The kernel is pure, so
the only thing that moves is the frame `runFunction` pops.

It is stated in continuation form rather than as a run equation: the vector the
call returns is `fd_r43x6_unpack_spec`'s existential -- the `unpackVec` behind
it is `private` -- so a caller cannot name it. That is no loss: an opaque local
plus the six facts the spec gives is exactly what a walk wants, and it keeps
`unpackVec` out of the residual program.

`fd_r43x6_unpack_cfg`, not `fd_r43x6_unpack`, is what a caller's call node
holds, so the run equation is stated over that constant.
-/

@[expose] public section

namespace Firedancer.Avx512
open LeanMLIR SLLVM
open InstCombine (LLVM)

/-- **One `fd_r43x6_unpack( u )` call**, in the form `peel_call` takes it: the
unpacked limbs arrive as an opaque `v`, with everything
`fd_r43x6_unpack_spec` says about it. The state it lands in is an *argument*,
so the caller can name it up front and the goal carries an `fvar` rather than
a `popFrame` term -- `sqr_step_of_take`'s reason, at 43s a `set`. -/
theorem unpack_step (u : Vector (BitVec 64) 4) (t t' : GlobalState)
    (ht' : t' = t.popFrame t.mem) {P : Prop}
    (k : ∀ v : Vector (BitVec 64) 8,
        StateT.run (runFunction (fd_r43x6_unpack_cfg.denote
            (Ctxt.Valuation.ofHVector [u.map PoisonOr.value]ₕ))) t
          = .value ([v.map PoisonOr.value]ₕ, t') →
        R43x6.Unpacked v →
        R43x6.decode' v = (wvNat u : ℤ) →
        v[6] = 0 → v[7] = 0 →
        (wvNat u < 2 * p → R43x6.NearlyReduced v) →
        (wvNat u < p → R43x6.Reduced v) → P) : P := by
  obtain ⟨v, hout, hunp, hdec, h6, h7, hnr, hred⟩ := fd_r43x6_unpack_conforms u
  refine k v ?_ hunp hdec h6 h7 hnr hred
  rw [denote_fd_r43x6_unpack] at hout
  simp only [HVector.head] at hout
  rw [ht']
  refine run_runFunction ?_
  simp only [fd_r43x6_unpack_cfg, Cfg.denote_ofCom, Com.denote_castPureToEff]
  show StateT.run (pure (fd_r43x6_unpack.denote
    (Ctxt.Valuation.singleton (u.map PoisonOr.value)))) t = _
  rw [denote_fd_r43x6_unpack, hout]
  simp only [EffectM.run_pure]

/-- `unpacked ⊆ u47`: what the unpack returns already meets the input contract
of `fd_r43x6_sqr_fast`/`mul_fast`, so a decoded field element goes straight
into the kernels with no bound re-derived. `u47_of_u44`'s counterpart at the
other end of the chain. -/
theorem u47_take_of_unpacked {v : Vector (BitVec 64) 8} (h : R43x6.Unpacked v) :
    R43x6.U47 (v.take R43x6.limbCount) := by
  have hb : ∀ i : Fin R43x6.limbCount,
      0 ≤ R43x6.extractLimbs v i ∧ R43x6.extractLimbs v i < 2 ^ 43 := by
    intro i
    by_cases hi : (i : ℕ) < 5
    · exact h.1 i hi
    · have h5 : i = (5 : Fin R43x6.limbCount) := by
        have := i.isLt
        apply Fin.ext
        simp only [R43x6.limbCount] at *
        omega
      subst h5
      exact ⟨h.2.1, lt_trans h.2.2 (by norm_num)⟩
  exact ⟨fun i => by rw [R43x6.toInts_take]; have := (hb i).2; omega,
    fun i => by rw [R43x6.toInts_take]; exact (hb i).1⟩

end Firedancer.Avx512
