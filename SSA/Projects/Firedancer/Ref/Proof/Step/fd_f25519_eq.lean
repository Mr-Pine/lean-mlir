/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SSA.Projects.Firedancer.Ref.Proof.Step.Basic
public import SSA.Projects.Firedancer.Ref.Proof.Field.fd_f25519_eq

@[expose] public section

namespace Firedancer.Ref
open LeanMLIR SLLVM
open InstCombine (LLVM)

/-- One `fd_f25519_eq( a, b )` call, peeled: the comparison the region branches
on, and the state it leaves -- `eq` only reads, so that is the same state up to
`≈`. -/
theorem eq_step {a b : Pointer} {w : GlobalState} (hw : w.WF)
    (ha : IsFieldElemPtr w.mem a) (hb : IsFieldElemPtr w.mem b)
    (hab : LimbBounds ha) (hbb : BiasBounds hb) {x y : ZMod _root_.p}
    (hva : readFieldElem ha = x) (hvb : readFieldElem hb = y) :
    ∃ w', StateT.run (runFunction (fd_f25519_eq.denote
        (Ctxt.Valuation.ofPair (.value b) (.value a)))) w
        = .value ([(.value (if x = y then 1#32 else 0#32) : LLVM.IntW 32)]ₕ, w')
      ∧ w ≈ w' := by
  obtain ⟨w', hrun, heq⟩ := fd_f25519_eq_conforms a b w hw ha hb hab hbb
  rw [hva, hvb] at hrun
  exact ⟨w', hrun, heq⟩

end Firedancer.Ref
