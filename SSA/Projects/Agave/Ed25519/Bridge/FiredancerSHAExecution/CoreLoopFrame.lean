import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.CoreBranches

namespace Agave.Ed25519.Bridge.FiredancerSHAExecution.Core
open LeanMLIR.RIR Agave.Ed25519.SHA512 Agave.Ed25519.SHA512.Spec
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

/-- Arguments and all registers carrying the enclosing block state survive
both round loops. -/
def LoopFrame (before after : Env program.Γ) : Prop :=
  after.args = before.args ∧ ∀ i : Fin program.Γ.n, i.val < 54 → after.vals i = before.vals i

theorem LoopFrame.refl (E : Env program.Γ) : LoopFrame E E := ⟨rfl, fun _ _ => rfl⟩
theorem LoopFrame.trans {E F G : Env program.Γ} (h : LoopFrame E F) (h' : LoopFrame F G) :
    LoopFrame E G := ⟨h'.1.trans h.1, fun i hi => (h'.2 i hi).trans (h.2 i hi)⟩
theorem LoopFrame.write {E F : Env program.Γ} (h : LoopFrame E F)
    (dst : Dst program.Γ t) (v : t.denote) (hlo : 54 ≤ dst.i.val) :
    LoopFrame E (F.write dst v) := by
  refine ⟨h.1, ?_⟩
  intro i hi
  have hne : i ≠ dst.i := by intro heq; have := congrArg Fin.val heq; omega
  simpa only [Env.write, Env.set, dite_eq_right hne] using h.2 i hi

theorem LoopFrame.read_val {E F : Env program.Γ} (h : LoopFrame E F)
    (i : Fin program.Γ.n) (hi : i.val < 54) (ht : program.Γ.ty i = t) :
    F.read (.val i ht) = E.read (.val i ht) := by
  simp only [Env.read, h.2 i hi]

theorem firstBody_frame (E : Env program.Γ) (stack data kp : Pointer) (r : Nat)
    (s : State) (native constant : Word) :
    LoopFrame E (firstBodyEnv E stack data kp r s native constant) := by
  unfold firstBodyEnv firstEnv inputEnv
  repeat' (apply LoopFrame.write <;> try decide)
  exact LoopFrame.refl E

theorem firstNext_frame (E : Env program.Γ) (r : Nat) (s : State) :
    LoopFrame E (firstNextEnv E r s) := by
  unfold firstNextEnv
  repeat' (apply LoopFrame.write <;> try decide)
  exact LoopFrame.refl E

theorem laterBody_frame (E : Env program.Γ) (stack kp : Pointer) (q : Ring)
    (r : Nat) (s : State) (constant : Word) :
    LoopFrame E (laterBodyEnv E stack kp q r s constant) := by
  unfold laterBodyEnv laterEnv scheduleEnv
  repeat' (apply LoopFrame.write <;> try decide)
  exact LoopFrame.refl E

theorem laterNext_frame (E : Env program.Γ) (r : Nat) (s : State) :
    LoopFrame E (laterNextEnv E r s) := by
  unfold laterNextEnv
  repeat' (apply LoopFrame.write <;> try decide)
  exact LoopFrame.refl E

end Agave.Ed25519.Bridge.FiredancerSHAExecution.Core
