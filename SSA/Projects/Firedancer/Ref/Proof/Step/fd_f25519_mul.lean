/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.Firedancer.Ref.Proof.Step.Basic
import SSA.Projects.Firedancer.Ref.Proof.Field.fd_f25519_mul

namespace Firedancer.Ref
open LeanMLIR SLLVM

/-- One `fd_f25519_mul( dst, src₀, src₁ )` call, peeled: the run equation for
`peel_call` plus `StepFacts`. `dst` may alias a source -- the kernels read
before they write, and the conformance lemmas carry no disjointness
hypotheses. -/
theorem mul_step {dst src₀ src₁ : Pointer} {u : GlobalState} (hu : u.WF)
    (hd : IsFieldElemPtr u.mem dst)
    (h₀ : IsFieldElemPtr u.mem src₀) (h₁ : IsFieldElemPtr u.mem src₁)
    {w₀ w₁ : ZMod _root_.p}
    (hv₀ : readFieldElem h₀ = w₀) (hv₁ : readFieldElem h₁ = w₁)
    (hb₀ : LimbBounds.Loose h₀) (hb₁ : LimbBounds.Loose h₁) :
    ∃ u', StateT.run (runFunction (fd_f25519_mul.denote
        (Ctxt.Valuation.ofHVector [.value src₁, .value src₀, .value dst]ₕ))) u
        = .value ([.value dst]ₕ, u')
      ∧ StepFacts dst (w₀ * w₁) u u' := by
  obtain ⟨out, hval, hbnd, u', hrun, heq⟩ :=
    fd_f25519_mul_conforms dst src₀ src₁ u hu hd h₀ h₁
      (limbBounds_readLimb? h₀ hb₀) (limbBounds_readLimb? h₁ hb₁)
  refine ⟨u', hrun, StepFacts.of_splice hu hd heq ?_ (limbBounds_readLimb? _ hbnd)⟩
  rw [← hv₀, ← hv₁, ← hval]
  exact (Option.some_get _).symm

end Firedancer.Ref
