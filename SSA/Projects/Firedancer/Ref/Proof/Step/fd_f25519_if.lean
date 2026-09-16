/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.Firedancer.Ref.Proof.Step.Basic
import SSA.Projects.Firedancer.Ref.Proof.Field.fd_f25519_if

namespace Firedancer.Ref
open LeanMLIR SLLVM

/-- The flag `fd_f25519_if` branches on: it truncates its condition to a byte,
and the region hands it a 0/1. -/
theorem setWidth_flag {A : Prop} [Decidable A] :
    ((if A then 1#32 else 0#32 : BitVec 32).setWidth 8 ≠ 0) ↔ A := by
  by_cases h : A <;> simp [h]

/-- One `fd_f25519_if( dst, c, a₀, a₁ )` call, peeled. Stated over the *Prop*
the flag stands for, so the region's condition never has to be unfolded again:
everything the spec has to say about the byte truncation is spent here. -/
theorem if_step {dst a₀ a₁ : Pointer} {w : GlobalState} (hw : w.WF)
    (hd : IsFieldElemPtr w.mem dst) (h₀ : IsFieldElemPtr w.mem a₀) (h₁ : IsFieldElemPtr w.mem a₁)
    {x y : ZMod _root_.p} (hv₀ : readFieldElem h₀ = x) (hv₁ : readFieldElem h₁ = y)
    (hb₀ : LimbBounds h₀) (hb₁ : LimbBounds h₁) (c : Prop) [Decidable c] :
    ∃ w' : GlobalState, ∃ hw' : Wrote dst w w',
      StateT.run (runFunction (fd_f25519_if.denote (Ctxt.Valuation.ofHVector
          [.value a₁, .value a₀, .value (if c then 1#32 else 0#32), .value dst]ₕ))) w
        = .value ([.value dst]ₕ, w')
      ∧ readFieldElem hw'.ptr = (if c then x else y) ∧ LimbBounds hw'.ptr
      ∧ (ZeroLimbs dst w'.mem → ZeroLimbs a₀ w.mem ∨ ZeroLimbs a₁ w.mem) := by
  obtain ⟨hval, w', hrun, heq⟩ :=
    fd_f25519_if_conforms dst (if c then 1#32 else 0#32) a₀ a₁ w hw hd h₀ h₁
  simp only [setWidth_flag] at hval heq
  refine ⟨w', Wrote.of_splice hw hd heq, hrun,
    readFieldElem_of_splice heq (by rw [← hv₀, ← hv₁, ← hval]; exact (Option.some_get _).symm),
    limbBounds_of_splice heq fun i l hl => ?bnd, fun hz => ?zero⟩
  case zero =>
    -- the winner's limbs are copied verbatim, so all-zero ones were all-zero there
    have hsrc : ∀ {q : Pointer} (hq : IsFieldElemPtr w.mem q),
        (∀ i, readLimb? dst i (w.mem.splice dst (packLimbs fun i => (readLimb i hq : BitVec 64)))
          = some 0) → ZeroLimbs q w.mem := fun hq hz' i => by
      have h := hz' i
      rw [limbReadbackPack _ _ _ hd.left i, Option.some.injEq] at h
      simp only [BitVec.natCast_eq_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (readLimb_lt i hq)] at h
      rw [← h]; exact (Option.some_get _).symm
    have hz' := hsrc _ fun i => (readLimb?_of_equiv heq dst i).trans (hz i)
    by_cases hc : c
    · simp only [hc, if_true] at hz'
      exact Or.inl hz'
    · simp only [hc, if_false] at hz'
      exact Or.inr hz'
  case bnd =>
    -- the winner's limbs are copied verbatim, and both are tight
    rw [limbReadbackPack _ _ _ hd.left i, Option.some.injEq] at hl
    subst hl
    simp only [BitVec.natCast_eq_ofNat, BitVec.toNat_ofNat]
    refine le_trans (Nat.mod_le _ _) ?_
    by_cases hc : c
    · simpa [hc] using hb₀ i
    · simpa [hc] using hb₁ i

end Firedancer.Ref
