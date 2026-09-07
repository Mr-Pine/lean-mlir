/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.Firedancer.Ref.Proof.Step.Basic
import SSA.Projects.Firedancer.Ref.Proof.Field.fd_f25519_sgn

namespace Firedancer.Ref
open LeanMLIR SLLVM
open InstCombine (LLVM)

/-- One `fd_f25519_sgn( src )` call, peeled. Like `eq_step`, not a `Wrote`:
`fd_f25519_sgn` only reads -- its 32-byte buffer is a local, killed on return
-- so the state moves only up to `≈`, and what comes back is the low bit of
the canonical representative.

The bounds are `fiat_25519_to_bytes`'s, weakened to what it actually needs: the
per-limb bias bounds, plus `limbSum < 2 · p` so that one conditional
subtraction canonicalises. A `fd_f25519_opp` result -- which is what
`fd_f25519_abs`, and so `fd_f25519_sqrt_ratio`, can leave -- satisfies the
first outright; the second is where `x ≠ 2 · p` has to come from. -/
theorem sgn_step {src : Pointer} {w : GlobalState} (hw : w.WF)
    (h₀ : IsFieldElemPtr w.mem src) {x : ZMod _root_.p} (hv : readFieldElem h₀ = x)
    (hb : BiasBounds h₀) (hlt : limbSum h₀ < 2 ^ 256 - 38) :
    ∃ w', StateT.run (runFunction (fd_f25519_sgn.denote
        (Ctxt.Valuation.singleton (.value src)))) w
        = .value ([(.value (BitVec.ofNat 32 (x.val % 2)) : LLVM.IntW 32)]ₕ, w')
      ∧ w ≈ w' := by
  obtain ⟨w', hrun, heq⟩ := fd_f25519_sgn_conforms src w hw h₀ hb hlt
  rw [hv] at hrun
  exact ⟨w', hrun, heq⟩

end Firedancer.Ref
