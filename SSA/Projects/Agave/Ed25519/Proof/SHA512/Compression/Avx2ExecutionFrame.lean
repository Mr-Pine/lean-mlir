import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2Execution

/-! The scalar tail preserves arguments and all registers outside its local
register interval, including the surrounding compressor's state. -/
namespace Agave.Ed25519.SHA512.Execution.Avx2

open LeanMLIR.RIR

/-- Only the tail's block parameters and instruction destinations may change. -/
def TailFrame (before after : Env program.Γ) : Prop :=
  after.args = before.args ∧
    ∀ i : Fin program.Γ.n, (i.val < 272 ∨ 308 < i.val) →
      after.vals i = before.vals i

theorem TailFrame.refl (E : Env program.Γ) : TailFrame E E :=
  ⟨rfl, fun _ _ => rfl⟩

theorem TailFrame.trans {E₀ E₁ E₂ : Env program.Γ}
    (h₀ : TailFrame E₀ E₁) (h₁ : TailFrame E₁ E₂) : TailFrame E₀ E₂ :=
  ⟨h₁.1.trans h₀.1, fun i hi => (h₁.2 i hi).trans (h₀.2 i hi)⟩

/-- A write to a tail-local register preserves the frame relation. -/
theorem TailFrame.write {E₀ E₁ : Env program.Γ} (h : TailFrame E₀ E₁)
    (dst : Dst program.Γ t) (v : t.denote)
    (hlo : 272 ≤ dst.i.val) (hhi : dst.i.val ≤ 308) :
    TailFrame E₀ (E₁.write dst v) := by
  refine ⟨h.1, ?_⟩
  intro i hi
  have hne : i ≠ dst.i := by
    intro heq
    have hv := congrArg Fin.val heq
    omega
  simpa only [Env.write, Env.set, dite_eq_right hne] using h.2 i hi

theorem tailBodyEnv_frame (E : Env program.Γ) (scratch : Pointer) (r : Nat)
    (s : Spec.State) (kw : Spec.Word) : TailFrame E (tailBodyEnv E scratch r s kw) := by
  unfold tailBodyEnv
  repeat' (apply TailFrame.write <;> try decide)
  exact TailFrame.refl E

theorem tailNextEnv_frame (E : Env program.Γ) (r : Nat) (s : Spec.State) :
    TailFrame E (tailNextEnv E r s) := by
  unfold tailNextEnv
  repeat' (apply TailFrame.write <;> try decide)
  exact TailFrame.refl E

theorem tailRoundEnv_frame (E : Env program.Γ) (scratch : Pointer) (r : Nat)
    (s : Spec.State) (kw : Spec.Word) :
    TailFrame E (tailNextEnv (tailBodyEnv E scratch r s kw) (r + 1) (tailRound s kw)) :=
  (tailBodyEnv_frame E scratch r s kw).trans (tailNextEnv_frame _ _ _)

end Agave.Ed25519.SHA512.Execution.Avx2
