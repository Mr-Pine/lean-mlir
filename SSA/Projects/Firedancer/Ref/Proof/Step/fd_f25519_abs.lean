/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SSA.Projects.Firedancer.Ref.Proof.Step.Basic
public import SSA.Projects.Firedancer.Ref.Proof.Field.fd_f25519_abs

@[expose] public section

namespace Firedancer.Ref
open LeanMLIR SLLVM

/-- One `fd_f25519_abs( dst, src )` call, peeled: the non-negative
representative, at `fd_f25519_neg`'s per-limb bound since `fd_f25519_if`
copies out whichever of the two `abs` built, plus the sum bound `abs`
establishes per branch. -/
theorem abs_step {dst src : Pointer} {w : GlobalState} (hw : w.WF)
    (hd : IsFieldElemPtr w.mem dst) (h₀ : IsFieldElemPtr w.mem src)
    {x : ZMod _root_.p} (hv : readFieldElem h₀ = x) (hb : LimbBounds h₀) :
    ∃ w' : GlobalState, ∃ hw' : Wrote dst w w',
      StateT.run (runFunction (fd_f25519_abs.denote
          (Ctxt.Valuation.ofHVector [.value src, .value dst]ₕ))) w
        = .value ([.value dst]ₕ, w')
      ∧ readFieldElem hw'.ptr = (if x.val % 2 = 1 then -x else x)
      ∧ BiasBounds hw'.ptr ∧ limbSum hw'.ptr < 2 ^ 256 - 38
      ∧ (ZeroLimbs dst w'.mem → ZeroLimbs src w.mem) := by
  obtain ⟨out, hval, hbnd, hsum, ⟨w', hrun, heq⟩, hzero⟩ :=
    fd_f25519_abs_conforms dst src w hw hd h₀ hb
  refine ⟨w', Wrote.of_splice hw hd heq, hrun,
    readFieldElem_of_splice heq (by rw [← hv, ← hval]; exact (Option.some_get _).symm),
    biasBounds_of_splice heq (biasBounds_readLimb? _ hbnd), ?_,
    fun hz => hzero (ZeroLimbs.of_equiv heq hz)⟩
  rw [limbSum_of_splice hd heq]
  exact hsum

end Firedancer.Ref
