/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SSA.Projects.Firedancer.Proof.Memory

/-!
# A callee's write chain, as the caller meets it

A whole-function specification that writes through four out-parameters states
its result over one memory, `(((m.splice p₁ x₁).splice p₂ x₂).splice p₃ x₃).splice p₄ x₄`,
inside a single `{ s with mem := … }`. The caller has to say two things about
that state -- that it is still well formed, and that it left the frame below the
entry counter alone -- and the obvious ways to say them are both slow.

`GlobalState.WF.splice` and `FrameBelow.splice` each nest *one structure update
per store*, so a tower of four has to be matched against the specification's
single update, and that match is minutes of `whnf`, not seconds. The two lemmas
here state the chain at the shape the specification produces, so the match is
first-order.

They are proved by `intro` and `rw` with no `show`: spelling the chain out first
re-elaborates it, which costs seconds on its own.
-/

@[expose] public section

namespace Firedancer

open LeanMLIR SLLVM

/-- A state well formed before four stores is well formed after them. -/
theorem wf_splice4 {t : GlobalState} {p₁ p₂ p₃ p₄ : Pointer} {w₁ w₂ w₃ w₄ : Nat} {x₁ : BitVec w₁}
    {x₂ : BitVec w₂} {x₃ : BitVec w₃} {x₄ : BitVec w₄} (ht : t.WF) :
    ({ t with mem := (((t.mem.splice p₁ x₁).splice p₂ x₂).splice p₃ x₃).splice p₄ x₄ } :
        GlobalState).WF :=
  fun q hq =>
  live?_splice_eq_none
    (live?_splice_eq_none (live?_splice_eq_none (live?_splice_eq_none (ht q hq))))

/-- ... and four stores to blocks at or above `n₀` keep the frame below `n₀`. -/
theorem frameBelow_splice4 {n₀ : Nat} {s t : GlobalState} {p₁ p₂ p₃ p₄ : Pointer}
    {w₁ w₂ w₃ w₄ : Nat} {x₁ : BitVec w₁} {x₂ : BitVec w₂} {x₃ : BitVec w₃} {x₄ : BitVec w₄}
    (hf : FrameBelow n₀ s t) (h₁ : n₀ ≤ p₁.id.id) (h₂ : n₀ ≤ p₂.id.id) (h₃ : n₀ ≤ p₃.id.id)
    (h₄ : n₀ ≤ p₄.id.id) :
    FrameBelow n₀ s
      ({ t with mem := (((t.mem.splice p₁ x₁).splice p₂ x₂).splice p₃ x₃).splice p₄ x₄ } :
        GlobalState) := by
  intro b hb
  have ne : ∀ p : Pointer, n₀ ≤ p.id.id → p.id ≠ b := fun p hp h =>
    absurd (congrArg BlockId.id h) (by omega)
  rw [live?_splice_ne (ne p₄ h₄), live?_splice_ne (ne p₃ h₃), live?_splice_ne (ne p₂ h₂),
    live?_splice_ne (ne p₁ h₁)]
  exact hf b hb

/-- The live-block equation a callee's `≈` gives, with the write chain already
on the right. Stated over `{ s with mem := m }` so `m` unifies whole: taking
`he.live b` against an ascribed type instead makes the elaborator walk a
projection through every splice, which is seconds per use.

`Ref.live?_of_equiv_mem` is the same lemma, stated before this file existed. -/
theorem live?_of_equiv_mem' {w s : GlobalState} {m : MemoryState}
    (he : w ≈ ({ s with mem := m } : GlobalState)) (b : BlockId) : w.mem.live? b = m.live? b :=
  he.live b

end Firedancer
