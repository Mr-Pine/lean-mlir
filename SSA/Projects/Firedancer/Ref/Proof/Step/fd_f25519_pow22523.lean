/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.Firedancer.Ref.Proof.Step.Basic
import SSA.Projects.Firedancer.Ref.Proof.Field.fd_f25519_pow22523

namespace Firedancer.Ref
open LeanMLIR SLLVM

/-- One `fd_f25519_pow22523( dst, src )` call, peeled, in `sqr_step`'s shape. -/
theorem pow_step {dst src : Pointer} {w : GlobalState} (hw : w.WF)
    (hd : IsFieldElemPtr w.mem dst) (h₀ : IsFieldElemPtr w.mem src)
    {x : ZMod _root_.p} (hv : readFieldElem h₀ = x) (hb : LimbBounds.Loose h₀) :
    ∃ w', StateT.run (runFunction (fd_f25519_pow22523.denote
        (Ctxt.Valuation.ofHVector [.value src, .value dst]ₕ))) w
        = .value ([.value dst]ₕ, w')
      ∧ StepFacts dst (x ^ (2 ^ 252 - 3)) w w' := by
  obtain ⟨out, hval, hbnd, w', hrun, heq⟩ := fd_f25519_pow22523_conforms dst src w hw hd h₀ hb
  refine ⟨w', hrun, StepFacts.of_splice hw hd heq ?_ (limbBounds_readLimb? _ hbnd)⟩
  rw [← hv, ← hval]
  exact (Option.some_get _).symm

end Firedancer.Ref
