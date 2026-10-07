import SSA.Projects.Agave.Ed25519.Proof.Tables.SerialConstructorRegisters

namespace Agave.Ed25519.Tables.SerialConstructorRegisters
open LeanMLIR.RIR
private theorem ub_eq (s : GlobalState) : (throwUB : EffectM α) s = .poison := rfl

/-- Invert a successful list composition without re-executing its instructions. -/
theorem body_split (left right : List (Instr Γ)) (E F : ⟪Γ⟫) (s t : GlobalState)
    (hr : List.foldlM Instr.run E (left ++ right) s = .value (F, t)) :
    ∃ M u, List.foldlM Instr.run E left s = .value (M, u) ∧
      List.foldlM Instr.run M right u = .value (F, t) := by
  rw [List.foldlM_append, EffectM.bind_eq] at hr
  cases hl : List.foldlM Instr.run E left s with
  | poison => simp only [hl, PoisonOr.poison_bind] at hr; cases hr
  | value result =>
      rcases result with ⟨M, u⟩
      exact ⟨M, u, rfl, by simpa only [hl, PoisonOr.value_bind] using hr⟩

def Instr.readOnly : Instr Γ → Prop
  | .store _ _ | .memset _ _ _ | .memcpy _ _ _ | .alloca _ _ | .call _ _ _ => False
  | _ => True

theorem instruction_readOnly (i : Instr Γ) (h : Instr.readOnly i)
    (E F : ⟪Γ⟫) (s t : GlobalState)
    (hr : Instr.run E i s = .value (F, t)) : t = s := by
  cases i <;> simp only [Instr.readOnly] at h
  all_goals try cases h
  all_goals try
    (simp only [Instr.run, EffectM.pure_eq, EffectM.bind_eq, EffectM.get_eq,
      PoisonOr.value_bind] at hr
     exact (congrArg Prod.snd (PoisonOr.value_inj.mp hr)).symm)
  case assume cond =>
    cases hc : E.read cond using PoisonOr.casesOn' <;>
      simp only [Instr.run, hc, ub_eq] at hr
    · cases hr
    · split at hr
      · exact (congrArg Prod.snd (PoisonOr.value_inj.mp hr)).symm
      · simp only [ub_eq] at hr; cases hr
  case load ty dst ptr =>
    cases hp : E.read ptr using PoisonOr.casesOn' <;>
      simp only [Instr.run, Operation.load, hp, EffectM.bind_eq, EffectM.pure_eq,
        EffectM.get_eq, PoisonOr.value_bind, PoisonOr.poison_bind, ub_eq, throwUBIf] at hr
    · cases hr
    · split at hr <;>
        simp only [EffectM.pure_eq, PoisonOr.value_bind, PoisonOr.poison_bind, ub_eq] at hr
      · cases hr
      · exact (congrArg Prod.snd (PoisonOr.value_inj.mp hr)).symm
  case loadMonotonic dst ptr =>
    cases hp : E.read ptr using PoisonOr.casesOn' <;>
      simp only [Instr.run, Operation.load, hp, EffectM.bind_eq, EffectM.pure_eq,
        EffectM.get_eq, PoisonOr.value_bind, PoisonOr.poison_bind, ub_eq, throwUBIf] at hr
    · cases hr
    · split at hr <;>
        simp only [EffectM.pure_eq, PoisonOr.value_bind, PoisonOr.poison_bind, ub_eq] at hr
      · cases hr
      · exact (congrArg Prod.snd (PoisonOr.value_inj.mp hr)).symm

theorem body_readOnly (body : List (Instr Γ))
    (h : ∀ i ∈ body, Instr.readOnly i)
    (E F : ⟪Γ⟫) (s t : GlobalState)
    (hr : List.foldlM Instr.run E body s = .value (F, t)) : t = s := by
  induction body generalizing E s with
  | nil => exact (congrArg Prod.snd (PoisonOr.value_inj.mp hr)).symm
  | cons i rest ih =>
    rw [List.foldlM_cons, EffectM.bind_eq] at hr
    cases hi : Instr.run E i s with
    | poison => simp only [hi, PoisonOr.poison_bind] at hr; cases hr
    | value result =>
      rcases result with ⟨E', s'⟩
      simp only [hi, PoisonOr.value_bind] at hr
      exact (ih (fun j hj => h j (by simp [hj])) E' s' hr).trans
        (instruction_readOnly i (h i (by simp)) E E' s s' hi)

end Agave.Ed25519.Tables.SerialConstructorRegisters
