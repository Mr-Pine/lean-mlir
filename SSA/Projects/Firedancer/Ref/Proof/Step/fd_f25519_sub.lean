/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.Firedancer.Ref.Proof.Step.Basic
import SSA.Projects.Firedancer.Ref.Proof.Field.fd_f25519_sub

namespace Firedancer.Ref
open LeanMLIR SLLVM

/-- One `fd_f25519_sub( dst, src₀, src₁ )` call, peeled, in `add_step`'s
shape. The subtrahend's bound is per-limb: `fiat_25519_sub` subtracts limb `i`
from `bias i + minuend i`, so it is `BiasBounds` that keeps it from
underflowing, and a tight element is one (`LimbBounds.bias`). -/
theorem sub_step {dst src₀ src₁ : Pointer} {w : GlobalState} (hw : w.WF)
    (hd : IsFieldElemPtr w.mem dst)
    (h₀ : IsFieldElemPtr w.mem src₀) (h₁ : IsFieldElemPtr w.mem src₁)
    {x₀ x₁ : ZMod _root_.p}
    (hv₀ : readFieldElem h₀ = x₀) (hv₁ : readFieldElem h₁ = x₁)
    (hb₀ : LimbBounds h₀) (hb₁ : BiasBounds h₁) :
    ∃ w', StateT.run (runFunction (fd_f25519_sub.denote
        (Ctxt.Valuation.ofHVector [.value src₁, .value src₀, .value dst]ₕ))) w
        = .value ([.value dst]ₕ, w')
      ∧ StepFacts dst (x₀ - x₁) w w' := by
  obtain ⟨out, hval, hbnd, w', hrun, heq⟩ :=
    fd_f25519_sub_conforms dst src₀ src₁ w hw
      (limbBounds_readLimb? h₀ hb₀) (biasBounds_readLimb? h₁ hb₁) hd h₀ h₁
  refine ⟨w', hrun, StepFacts.of_splice hw hd heq ?_ (limbBounds_readLimb? _ hbnd)⟩
  rw [← hv₀, ← hv₁, ← hval]
  exact (Option.some_get _).symm

end Firedancer.Ref
