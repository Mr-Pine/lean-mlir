import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullBase

/-! Shared preservation of registers below each exact instruction slice. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 1800000

namespace Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
open LeanMLIR.RIR

def Before (bound : Nat) (E₀ E₁ : Env program.Γ) : Prop :=
  E₁.args = E₀.args ∧ ∀ i : Fin program.Γ.n, i.val < bound → E₁.vals i = E₀.vals i

theorem Before.refl (E : Env program.Γ) (bound : Nat) : Before bound E E :=
  ⟨rfl, fun _ _ => rfl⟩

theorem Before.write (h : Before bound E₀ E₁) (dst : Dst program.Γ t) (v : t.denote)
    (hlo : bound ≤ dst.i.val) : Before bound E₀ (E₁.write dst v) := by
  refine ⟨h.1, ?_⟩
  intro i hi
  have hne : i ≠ dst.i := by intro heq; have := congrArg Fin.val heq; omega
  simpa only [Env.write, Env.set, dite_eq_right hne] using h.2 i hi

theorem Before.read_val (h : Before bound E₀ E₁) (i : Fin program.Γ.n)
    (hi : i.val < bound) (ht : program.Γ.ty i = t) :
    E₁.read (.val i ht) = E₀.read (.val i ht) := by
  simp only [Env.read, h.2 i hi]

theorem Before.frame (h : Before bound E₀ E₁) (hb : 250 ≤ bound) : Frame E₀ E₁ :=
  ⟨h.1, fun i hi => h.2 i (lt_of_lt_of_le hi hb)⟩

end Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
