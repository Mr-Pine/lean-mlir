/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SSA.Projects.Firedancer.Ref.Proof.Step.Basic
public import SSA.Projects.Firedancer.Ref.Proof.Field.fd_f25519_neg

@[expose] public section

namespace Firedancer.Ref

open LeanMLIR SLLVM

/-- One `fd_f25519_neg( dst, src )` call, peeled. The limbs come back at
`fiat_25519_opp`'s bias bound, per limb, not at the tight one -- so this is
`Wrote` plus the value and that bound rather than a `StepFacts`. -/
theorem neg_step {dst src : Pointer} {w : GlobalState} (hw : w.WF) (hd : IsFieldElemPtr w.mem dst)
    (h₀ : IsFieldElemPtr w.mem src) {x : ZMod _root_.p} (hv : readFieldElem h₀ = x)
    (hb : BiasBounds h₀) :
    ∃ w' : GlobalState,
      ∃ hw' : Wrote dst w w',
        StateT.run
              (runFunction
                (fd_f25519_neg.denote (Ctxt.Valuation.ofHVector [.value src, .value dst]ₕ)))
              w =
            .value ([.value dst]ₕ, w') ∧
          readFieldElem hw'.ptr = -x ∧
          BiasBounds hw'.ptr ∧ ∀ i, readLimb? dst i w'.mem = some (biasLimb i - readLimb i h₀) := by
  have hc := fd_f25519_neg_conforms' dst src w hw hd h₀ hb
  obtain ⟨out, hval, hbnd, w', hrun, heq⟩ := hc.1
  exact
    ⟨w', Wrote.of_splice hw hd heq, hrun,
      readFieldElem_of_splice heq
        (by
          rw [← hv, ← hval]; exact (Option.some_get _).symm),
      biasBounds_of_splice heq (biasBounds_readLimb? _ hbnd), hc.2 w' hrun⟩

end Firedancer.Ref
