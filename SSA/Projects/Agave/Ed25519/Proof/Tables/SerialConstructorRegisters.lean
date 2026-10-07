import SSA.Projects.Agave.Ed25519.Proof.Tables.SerialCacheBody
import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionSerialScanComplete

namespace Agave.Ed25519.Tables.SerialConstructorRegisters
open LeanMLIR.RIR
open DoubleBase.RIR (PrefixEq)

/-- A syntactic bound on every destination, including call return values. -/
def Dsts.above (limit : Nat) : Dsts Γ ts → Prop
  | .nil => True
  | .cons d ds => limit ≤ d.i.val ∧ Dsts.above limit ds

def Instr.above (limit : Nat) : Instr Γ → Prop
  | .gep d _ _ | .gepInbounds d _ _ | .const _ d | .poison d |
    .unop _ d _ | .binop _ d _ _ | .ternop _ d _ _ _ |
    .load d _ | .loadMonotonic d _ | .alloca d _ => limit ≤ d.i.val
  | .call _ _ ds => Dsts.above limit ds
  | _ => True

theorem writeMany_prefix (ds : Dsts Γ ts) (vs : Vals ts)
    (h : Dsts.above limit ds) (E : ⟪Γ⟫) :
    PrefixEq E (E.writeMany ds vs) limit := by
  induction ds generalizing E with
  | nil => cases vs; exact PrefixEq.refl E limit
  | cons d ds ih =>
    cases vs with
    | cons v vs =>
      exact ((PrefixEq.refl E limit).write d v h.1).trans (ih vs h.2 _)

private theorem of_value {E F : ⟪Γ⟫} {s t : GlobalState} (h : PoisonOr.value (E, s) = PoisonOr.value (F, t)) : E = F :=
  congrArg Prod.fst (PoisonOr.value_inj.mp h)

private theorem ub_eq (s : GlobalState) : (throwUB : EffectM α) s = .poison := rfl

/-- Successful execution can alter only explicit instruction destinations. -/
theorem instruction_prefix (i : Instr Γ) (h : Instr.above limit i)
    (E F : ⟪Γ⟫) (s t : GlobalState)
    (hr : Instr.run E i s = .value (F, t)) : PrefixEq E F limit := by
  cases i <;> simp only [Instr.above] at h
  all_goals try
    (simp only [Instr.run, EffectM.pure_eq, EffectM.bind_eq, EffectM.get_eq,
      PoisonOr.value_bind] at hr
     have he := of_value hr
     subst F
     exact (PrefixEq.refl E limit).write _ _ h)
  all_goals try
    (simp only [Instr.run, EffectM.pure_eq] at hr
     have he := of_value hr
     subst F
     exact PrefixEq.refl E limit)
  case call f args ds =>
    simp only [Instr.run, EffectM.bind_eq] at hr
    cases hc : f (args.read E) s with
    | poison => simp only [hc, PoisonOr.poison_bind] at hr; cases hr
    | value result =>
      rcases result with ⟨vs, u⟩
      simp only [hc, PoisonOr.value_bind, EffectM.pure_eq] at hr
      have he := of_value hr
      subst F
      exact writeMany_prefix ds vs h E
  case assume cond =>
    cases hc : E.read cond using PoisonOr.casesOn' <;>
      simp only [Instr.run, hc, ub_eq] at hr
    · cases hr
    · split at hr
      · simp only [EffectM.pure_eq] at hr
        have he := of_value hr; subst F; exact PrefixEq.refl E limit
      · simp only [ub_eq] at hr; cases hr
  case load ty dst ptr =>
    cases hp : E.read ptr using PoisonOr.casesOn' <;>
      simp only [Instr.run, Operation.load, hp, EffectM.bind_eq, EffectM.pure_eq,
        EffectM.get_eq, PoisonOr.value_bind, PoisonOr.poison_bind, ub_eq, throwUBIf] at hr
    · cases hr
    · split at hr <;>
        simp only [EffectM.bind_eq, EffectM.pure_eq, PoisonOr.value_bind,
          PoisonOr.poison_bind, ub_eq] at hr
      · cases hr
      · have he := of_value hr; subst F; exact (PrefixEq.refl E limit).write _ _ h
  case loadMonotonic dst ptr =>
    cases hp : E.read ptr using PoisonOr.casesOn' <;>
      simp only [Instr.run, Operation.load, hp, EffectM.bind_eq, EffectM.pure_eq,
        EffectM.get_eq, PoisonOr.value_bind, PoisonOr.poison_bind, ub_eq, throwUBIf] at hr
    · cases hr
    · split at hr <;>
        simp only [EffectM.bind_eq, EffectM.pure_eq, PoisonOr.value_bind,
          PoisonOr.poison_bind, ub_eq] at hr
      · cases hr
      · have he := of_value hr; subst F; exact (PrefixEq.refl E limit).write _ _ h
  case store ty ptr val =>
    cases hp : E.read ptr using PoisonOr.casesOn' <;>
      simp only [Instr.run, Operation.store, hp, EffectM.bind_eq, EffectM.pure_eq,
        EffectM.get_eq, PoisonOr.value_bind, PoisonOr.poison_bind, ub_eq, throwUBIf] at hr
    · cases hr
    · split at hr <;>
        simp only [EffectM.bind_eq, EffectM.pure_eq, PoisonOr.value_bind,
          PoisonOr.poison_bind, ub_eq] at hr
      · cases hr
      · cases hv : ty.flatten (E.read val) using PoisonOr.casesOn' <;>
          simp only [hv, EffectM.bind_eq, EffectM.pure_eq, EffectM.set_eq,
            PoisonOr.value_bind, PoisonOr.poison_bind, ub_eq] at hr
        · cases hr
        · have he := of_value hr; subst F; exact PrefixEq.refl E limit
  case memset w dst val len =>
    cases hd : E.read dst using PoisonOr.casesOn' <;>
      cases hv : E.read val using PoisonOr.casesOn' <;>
      cases hl : E.read len using PoisonOr.casesOn' <;>
      simp only [Instr.run, Operation.memset, hd, hv, hl, PoisonOr.pure_def,
        PoisonOr.value_bind, PoisonOr.poison_bind, ub_eq, EffectM.bind_eq,
        EffectM.get_eq, throwUBIf] at hr
    all_goals try cases hr
    split at hr <;>
      simp only [EffectM.bind_eq, EffectM.pure_eq, EffectM.set_eq,
        PoisonOr.value_bind, PoisonOr.poison_bind, ub_eq] at hr
    · cases hr
    · have he := of_value hr; subst F; exact PrefixEq.refl E limit
  case memcpy w dst src len =>
    cases hd : E.read dst using PoisonOr.casesOn' <;>
      cases hs : E.read src using PoisonOr.casesOn' <;>
      cases hl : E.read len using PoisonOr.casesOn' <;>
      simp only [Instr.run, Operation.memcpy, hd, hs, hl, PoisonOr.pure_def,
        PoisonOr.value_bind, PoisonOr.poison_bind, ub_eq, EffectM.bind_eq,
        EffectM.get_eq, throwUBIf] at hr
    all_goals try cases hr
    split at hr <;>
      simp only [EffectM.bind_eq, EffectM.pure_eq, EffectM.set_eq,
        PoisonOr.value_bind, PoisonOr.poison_bind, ub_eq] at hr
    · cases hr
    · split at hr <;>
        simp only [EffectM.bind_eq, EffectM.pure_eq, EffectM.set_eq,
          PoisonOr.value_bind, PoisonOr.poison_bind, ub_eq] at hr
      · cases hr
      · split at hr <;>
          simp only [EffectM.bind_eq, EffectM.pure_eq, EffectM.set_eq,
            PoisonOr.value_bind, PoisonOr.poison_bind, ub_eq] at hr
        · cases hr
        · have he := of_value hr; subst F; exact PrefixEq.refl E limit

theorem body_prefix (body : List (Instr Γ))
    (h : ∀ i ∈ body, Instr.above limit i)
    (E F : ⟪Γ⟫) (s t : GlobalState)
    (hr : List.foldlM Instr.run E body s = .value (F, t)) : PrefixEq E F limit := by
  induction body generalizing E s with
  | nil =>
    have he := of_value hr
    subst F
    exact PrefixEq.refl E limit
  | cons i rest ih =>
    rw [List.foldlM_cons, EffectM.bind_eq] at hr
    cases hi : Instr.run E i s with
    | poison => simp only [hi, PoisonOr.poison_bind] at hr; cases hr
    | value result =>
      rcases result with ⟨E', s'⟩
      simp only [hi, PoisonOr.value_bind] at hr
      exact (instruction_prefix i (h i (by simp)) E E' s s' hi).trans
        (ih (fun j hj => h j (by simp [hj])) E' s' hr)

end Agave.Ed25519.Tables.SerialConstructorRegisters
