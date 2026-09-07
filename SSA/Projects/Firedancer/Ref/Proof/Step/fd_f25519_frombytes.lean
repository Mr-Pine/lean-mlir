/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.Firedancer.Ref.Proof.Step.Basic
import SSA.Projects.Firedancer.Ref.Proof.Field.fd_f25519_frombytes

namespace Firedancer.Ref
open LeanMLIR SLLVM

/-- One `fd_f25519_frombytes( dst, src )` call, peeled. Not a `StepFacts`
only because it is stated over the buffer read rather than a value in hand. -/
theorem frombytes_step {dst src : Pointer} {w : GlobalState} (hw : w.WF)
    (hd : IsFieldElemPtr w.mem dst) (hb : IsByteBufPtr w.mem src) :
    ∃ w' : GlobalState, ∃ hw' : Wrote dst w w',
      StateT.run (runFunction (fd_f25519_frombytes.denote
          (Ctxt.Valuation.ofHVector [.value src, .value dst]ₕ))) w
        = .value ([.value dst]ₕ, w')
      ∧ readFieldElem hw'.ptr = decodeBytes (readBuf hb)
      ∧ LimbBounds hw'.ptr := by
  obtain ⟨out, hval, hbnd, w', hrun, heq⟩ := fd_f25519_frombytes_conforms dst src w hw hd hb
  exact ⟨w', Wrote.of_splice hw hd heq, hrun,
    readFieldElem_of_splice heq (by rw [← hval]; exact (Option.some_get _).symm),
    limbBounds_of_splice heq (limbBounds_readLimb? _ hbnd)⟩

end Firedancer.Ref
