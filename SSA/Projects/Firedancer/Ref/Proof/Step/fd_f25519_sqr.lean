/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SSA.Projects.Firedancer.Ref.Proof.Step.Basic
public import SSA.Projects.Firedancer.Ref.Proof.Field.fd_f25519_sqr

@[expose] public section

namespace Firedancer.Ref

open LeanMLIR SLLVM

/-- One `fd_f25519_sqr( dst, src )` call, peeled. As with `mul_step`, `dst`
may alias `src`. -/
theorem sqr_step' {dst src : Pointer} {u : GlobalState} (hu : u.WF) (hd : IsFieldElemPtr u.mem dst)
    (h₀ : IsFieldElemPtr u.mem src) {w : ZMod _root_.p} (hv : readFieldElem h₀ = w)
    (hb : LimbBounds.Loose h₀) :
    ∃ u',
      StateT.run
            (runFunction
              (fd_f25519_sqr.denote (Ctxt.Valuation.ofHVector [.value src, .value dst]ₕ)))
            u =
          .value ([.value dst]ₕ, u') ∧
        StepFacts dst (w * w) u u' ∧ (ZeroLimbs dst u'.mem → ZeroLimbs src u.mem) := by
  have hc := fd_f25519_sqr_conforms' dst src u hu hd h₀ (limbBounds_readLimb? h₀ hb)
  obtain ⟨out, hval, hbnd, u', hrun, heq⟩ := hc.1
  refine ⟨u', hrun, StepFacts.of_splice hu hd heq ?_ (limbBounds_readLimb? _ hbnd), hc.2 u' hrun⟩
  rw [readFieldElem?_eq_some (isFieldElemPtr_splice hd) hval, hv]

/-- `sqr_step'` without the zero-limbs clause. -/
theorem sqr_step {dst src : Pointer} {u : GlobalState} (hu : u.WF) (hd : IsFieldElemPtr u.mem dst)
    (h₀ : IsFieldElemPtr u.mem src) {w : ZMod _root_.p} (hv : readFieldElem h₀ = w)
    (hb : LimbBounds.Loose h₀) :
    ∃ u',
      StateT.run
            (runFunction
              (fd_f25519_sqr.denote (Ctxt.Valuation.ofHVector [.value src, .value dst]ₕ)))
            u =
          .value ([.value dst]ₕ, u') ∧
        StepFacts dst (w * w) u u' :=
  let ⟨u', hrun, st, _⟩ := sqr_step' hu hd h₀ hv hb
  ⟨u', hrun, st⟩

end Firedancer.Ref
