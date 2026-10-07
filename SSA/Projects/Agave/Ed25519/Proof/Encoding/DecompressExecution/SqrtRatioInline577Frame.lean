import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.Cutpoint

/-! Structural register frames for the supported straight-line fragments.
These lemmas retain all argument registers and every value below a bound. -/
namespace Agave.Ed25519.Encoding.Decompress.Execution.SerializerFrame
open LeanMLIR.RIR
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

@[local simp] theorem ub_apply (s : GlobalState) : (throwUB : EffectM α) s = .poison := rfl

def Frame (n : Nat) (E F : Env Γ) : Prop :=
  F.args = E.args ∧ ∀ i : Fin Γ.n, i.val < n → F.vals i = E.vals i

theorem Frame.refl (E : Env Γ) (n : Nat) : Frame n E E := ⟨rfl,fun _ _ => rfl⟩

theorem Frame.trans {E F G : Env Γ} (h : Frame n E F) (h' : Frame n F G) :
    Frame n E G := ⟨h'.1.trans h.1,fun i hi => (h'.2 i hi).trans (h.2 i hi)⟩

theorem Frame.mono {E F : Env Γ} (h : Frame n E F) (hm : m ≤ n) : Frame m E F :=
  ⟨h.1,fun i hi => h.2 i (Nat.lt_of_lt_of_le hi hm)⟩

theorem Frame.write (E : Env Γ) (d : Dst Γ t) (v : ⟦t⟧) (h : n ≤ d.i.val) :
    Frame n E (E.write d v) := by
  refine ⟨rfl,fun i hi => ?_⟩
  have hn : i ≠ d.i := by intro he; have he' := congrArg Fin.val he; omega
  simp only [Env.write,Env.set,dite_eq_right hn]

def writesAbove (n : Nat) : Instr Γ → Prop
  | .const _ d | .poison d | .unop _ d _ | .binop _ d _ _ |
    .gepInbounds d _ _ | .load d _ => n ≤ d.i.val
  | .store .. | .lifetimeStart .. | .lifetimeEnd .. |
    .noaliasScopeDecl .. => True
  | _ => False

theorem load_frame (E : Env Γ) (s : GlobalState) (d : Dst Γ t)
    (p : PoisonOr Pointer) (h : n ≤ d.i.val) (F : Env Γ) (u : GlobalState)
    (hrun : Operation.load d p E s = .value (F,u)) : Frame n E F := by
  cases p with
  | poison => simp [Operation.load,EffectM.bind_eq,EffectM.pure_eq,EffectM.run_ub,PoisonOr.poison_ne_value] at hrun
  | value p =>
    by_cases hf : Fits s.mem p t.width
    · simp [Operation.load,EffectM.bind_eq,EffectM.pure_eq,EffectM.run_ub,PoisonOr.poison_ne_value,EffectM.get_eq,
        throwUBIf,hf] at hrun
      obtain ⟨rfl,rfl⟩ := hrun
      exact Frame.write E d _ h
    · simp [Operation.load,EffectM.bind_eq,EffectM.pure_eq,EffectM.run_ub,PoisonOr.poison_ne_value,EffectM.get_eq,
        throwUBIf,hf] at hrun

theorem store_frame (E : Env Γ) (s : GlobalState)
    (p : PoisonOr Pointer) (v : ⟦t⟧) (F : Env Γ) (u : GlobalState)
    (hrun : Operation.store p v E s = .value (F,u)) : Frame n E F := by
  cases p with
  | poison => simp [Operation.store,EffectM.bind_eq,EffectM.pure_eq,EffectM.run_ub,PoisonOr.poison_ne_value] at hrun
  | value p =>
    by_cases hf : Fits s.mem p t.width
    · cases hv : t.flatten v with
      | poison =>
        simp [Operation.store,EffectM.bind_eq,EffectM.pure_eq,EffectM.run_ub,PoisonOr.poison_ne_value,EffectM.get_eq,
          EffectM.set_eq,throwUBIf,hf,hv] at hrun
      | value x =>
        simp [Operation.store,EffectM.bind_eq,EffectM.pure_eq,EffectM.run_ub,PoisonOr.poison_ne_value,EffectM.get_eq,
          EffectM.set_eq,throwUBIf,hf,hv] at hrun
        obtain ⟨rfl,rfl⟩ := hrun
        exact Frame.refl _ n
    · simp [Operation.store,EffectM.bind_eq,EffectM.pure_eq,EffectM.run_ub,PoisonOr.poison_ne_value,EffectM.get_eq,
        throwUBIf,hf] at hrun

theorem instr_frame (E : Env Γ) (s : GlobalState) (i : Instr Γ)
    (hi : writesAbove n i) (F : Env Γ) (u : GlobalState)
    (hrun : Instr.run E i s = .value (F,u)) : Frame n E F := by
  cases i <;> simp only [writesAbove] at hi
  all_goals try contradiction
  all_goals try exact load_frame E s _ _ hi F u hrun
  all_goals try exact store_frame E s _ _ F u hrun
  all_goals simp only [Instr.run,EffectM.pure_eq,EffectM.run_ub,PoisonOr.poison_ne_value,EffectM.bind_eq,
    EffectM.get_eq,PoisonOr.value_bind,PoisonOr.value_inj,Prod.mk.injEq] at hrun
  all_goals obtain ⟨rfl,rfl⟩ := hrun
  all_goals first | exact Frame.write E _ _ hi | exact Frame.refl _ n

/-- Success of a bounded-write list preserves all registers outside its write
range. The premise describes only individual destinations, not execution. -/
theorem list_frame (is : List (Instr Γ)) (hi : ∀ i ∈ is, writesAbove n i)
    (E : Env Γ) (s : GlobalState) (F : Env Γ) (u : GlobalState)
    (hrun : List.foldlM Instr.run E is s = .value (F,u)) : Frame n E F := by
  induction is generalizing E s with
  | nil =>
    simp only [List.foldlM_nil,EffectM.pure_eq,EffectM.run_ub,PoisonOr.poison_ne_value,PoisonOr.value_inj,Prod.mk.injEq] at hrun
    obtain ⟨rfl,rfl⟩ := hrun
    exact Frame.refl _ n
  | cons i is ih =>
    simp only [List.foldlM_cons,EffectM.bind_eq] at hrun
    cases hx : Instr.run E i s with
    | poison => simp [hx,PoisonOr.poison_ne_value] at hrun
    | value pair =>
      rcases pair with ⟨E',s'⟩
      simp only [hx,PoisonOr.value_bind] at hrun
      exact (instr_frame E s i (hi i (by simp)) E' s' hx).trans
        (ih (fun j hj => hi j (by simp [hj])) E' s' hrun)

end Agave.Ed25519.Encoding.Decompress.Execution.SerializerFrame
