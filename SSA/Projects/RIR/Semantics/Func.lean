module

public import SSA.Projects.RIR.Func
public import SSA.Projects.RIR.Semantics.Effectful.EffectM
public import SSA.Projects.RIR.Semantics.Env
public import SSA.Projects.RIR.Semantics.Vals
public import SSA.Projects.RIR.Semantics.Instruction

namespace LeanMLIR.RIR

public section

def BasicBlock.run (env : ⟪Γ⟫) {blockParams : Fin n → _} (block : BasicBlock Γ tRets blockParams) :
    EffectM (⟪Γ⟫ × (Vals tRets ⊕ Fin n)) := do
  let bodyResult ← List.foldlM Instr.run env block.body
  let exitResult ← block.exit.run bodyResult
  return (bodyResult, exitResult)

private def Func.evalFrom (func : Func) (args : (i : Fin func.Γ.args.length) → ⟦func.Γ.args[i]⟧) : Nat → ⟪func.Γ⟫ → Fin func.n → EffectM (Option (Vals func.tRets))
| 0, _, _ => pure .none
| fuel + 1, E, blockIndex => do
  let block := func.blocks blockIndex
  let (E', blockRes) ← BasicBlock.run E block
  match blockRes with
  | .inl returnValues =>
    return returnValues
  | .inr nextBlock =>
    Func.evalFrom func args fuel E' nextBlock

def Func.eval (func : Func) (fuel : Nat) (args : (i : Fin func.Γ.args.length) → ⟦func.Γ.args[i]⟧) :
    EffectM (Option (Vals func.tRets)) :=
  func.evalFrom args fuel startEnv ⟨0, func.hhasBlock⟩
where
  startEnv := Env.init args

end

/- Noncomputable, classical execution of Func.eval -/
section NoFuel

/-- More fuel does not change an existing result -/
def FuelMono (f : Nat → Option α) : Prop :=
  ∀ ⦃m n⦄, m ≤ n → ∀ ⦃r⦄, f m = some r → f n = some r

noncomputable def Fuel.limit (f : Nat → Option α) : Option α :=
  open Classical in if h : ∃ n, (f n).isSome then f h.choose else .none

private def Fuel.observe : PoisonOr (Option α × β) → Option (PoisonOr (α × β))
  | .poison => some PoisonOr.poison
  | .value (.none, _) => none
  | .value (.some r, s') => .some (.value (r, s'))

public noncomputable def Func.run (func : Func) (args : (i : Fin func.Γ.args.length) → ⟦func.Γ.args[i]⟧) :
    EffectM (Vals func.tRets) := fun s =>
  let f n := Fuel.observe (func.eval n args s)
  let determined := Fuel.limit f
  match determined with
  | some x => x >>= PoisonOr.value
  | none => .poison

section Lemmas

theorem mono_of_succ {f : Nat → Option α} (h : ∀ n r, f n = some r → f (n + 1) = some r) : FuelMono f := by
  intro m n hmn r hm
  induction hmn with
  | refl => exact hm
  | step _ ih => exact h _ _ ih

theorem Func.observe_evalFrom_succ (f : Func) (args : _) :
      ∀ (fuel : Nat) (E : ⟪f.Γ⟫) (i : Fin f.n) (s : GlobalState) (r),
        Fuel.observe (f.evalFrom args fuel E i s) = some r →
        Fuel.observe (f.evalFrom args (fuel + 1) E i s) = some r := by
  intro fuel
  induction fuel with
  | zero => simp [Func.evalFrom, Fuel.observe]
  | succ fuel ih =>
      intro E i s r h
      simp [Fuel.observe, Func.evalFrom] at h ⊢
      rcases hb : BasicBlock.run E (f.blocks i) s with _ | ⟨⟨E, res⟩, s'⟩ <;> simp [hb] at *
      · exact h
      · cases res <;> simp at h ⊢ <;> try exact h
        rename_i val
        replace ih := ih E val s' r
        unfold Fuel.observe at ih
        simp [h, Func.evalFrom] at ih
        exact ih

theorem Func.eval_mono (f : Func) (args) (s) :
      FuelMono (fun n => Fuel.observe (f.eval n args s)) := by
    refine mono_of_succ fun n r h => ?_
    exact Func.observe_evalFrom_succ _ _ _ _ _ _ _ h

theorem Fuel.limit_eq_of {f : Nat → Option α} (hf : FuelMono f) {n : Nat} {r : α}
      (h : f n = some r) : Fuel.limit f = some r := by
    unfold Fuel.limit
    have ex : ∃ n, (f n).isSome := ⟨n, by simp [h]⟩
    simp [ex]
    generalize hr' : ex.choose = m
    by_cases h' : m < n
    · refine Classical.byContradiction ?_
      intro h!
      have := hr' ▸ ex.choose_spec
      obtain ⟨q, hq⟩ : ∃ q, f m = some q := Option.isSome_iff_exists.mp this
      have := hf (show m ≤ n by omega) hq
      simp [h] at this
      simp [hq, this] at h!
    · exact hf (show n ≤ m by omega) h

public theorem Func.run_eq_of_eval (f : Func) (args) (s) {fuel v s'}
      (h : f.eval fuel args s = .value (some v, s')) :
      f.run args s = .value (v, s') := by
      unfold Func.run
      dsimp only
      replace h' : Fuel.observe (f.eval fuel args s) = some (.value (v, s')) := by simp [Fuel.observe, h]
      simp [Fuel.limit_eq_of (Func.eval_mono f args s) h']


end Lemmas

end NoFuel

end LeanMLIR.RIR
