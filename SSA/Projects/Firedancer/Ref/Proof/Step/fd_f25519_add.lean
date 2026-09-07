/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.Firedancer.Ref.Proof.Step.Basic
import SSA.Projects.Firedancer.Ref.Proof.Field.fd_f25519_add

namespace Firedancer.Ref
open LeanMLIR SLLVM

/-- One `fd_f25519_add( dst, src₀, src₁ )` call, peeled, in `mul_step`'s
shape. The wrapper carries afterwards, so the result is tight -- but unlike
`mul`/`sqr` *both operands* must already be, since `fiat_25519_add` adds limb
for limb with no headroom. -/
theorem add_step {dst src₀ src₁ : Pointer} {w : GlobalState} (hw : w.WF)
    (hd : IsFieldElemPtr w.mem dst)
    (h₀ : IsFieldElemPtr w.mem src₀) (h₁ : IsFieldElemPtr w.mem src₁)
    {x₀ x₁ : ZMod _root_.p}
    (hv₀ : readFieldElem h₀ = x₀) (hv₁ : readFieldElem h₁ = x₁)
    (hb₀ : LimbBounds h₀) (hb₁ : LimbBounds h₁) :
    ∃ w', StateT.run (runFunction (fd_f25519_add.denote
        (Ctxt.Valuation.ofHVector [.value src₁, .value src₀, .value dst]ₕ))) w
        = .value ([.value dst]ₕ, w')
      ∧ StepFacts dst (x₀ + x₁) w w' := by
  obtain ⟨out, hval, hbnd, w', hrun, heq⟩ :=
    fd_f25519_add_conforms dst src₀ src₁ w hw
      (limbBounds_readLimb? h₀ hb₀) (limbBounds_readLimb? h₁ hb₁) hd h₀ h₁
  refine ⟨w', hrun, StepFacts.of_splice hw hd heq ?_ (limbBounds_readLimb? _ hbnd)⟩
  rw [← hv₀, ← hv₁, ← hval]
  exact (Option.some_get _).symm

end Firedancer.Ref
