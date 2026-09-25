module

public import SSA.Projects.RIR.Func
public import SSA.Projects.RIR.Semantics.Effectful.EffectM
public import SSA.Projects.RIR.Semantics.Env
public import SSA.Projects.RIR.Semantics.Vals
public import SSA.Projects.RIR.Semantics.Instruction

namespace LeanMLIR.RIR

public section

abbrev ExitResult (tRets) (n) :=
  Vals tRets ⊕ Fin n

@[expose]
def BasicBlock.run {blockTys : Fin n → List Ty} (params : (k : Fin n) → Dsts Γ (blockTys k))
    (env : ⟪Γ⟫) (block : BasicBlock Γ tRets blockTys) : EffectM (⟪Γ⟫ × ExitResult tRets n) := do
  let bodyResult ← List.foldlM Instr.run env block.body
  block.exit.run params bodyResult

def Func.evalFrom (func : Func) : Nat → ⟪func.Γ⟫ → Fin func.n → EffectM (Option (Vals func.tRets))
  | 0, _, _ => pure .none
  | fuel + 1, E, blockIndex => do
    let block := func.blocks blockIndex
    let (E', blockRes) ← BasicBlock.run func.blockParams E block
    match blockRes with
    | .inl returnValues =>
      return returnValues
    | .inr nextBlock =>
      Func.evalFrom func fuel E' nextBlock

def Func.eval (func : Func) (fuel : Nat) (args : (i : Fin func.Γ.args.length) → ⟦func.Γ.args[i]⟧) :
    EffectM (Option (Vals func.tRets)) :=
  func.evalFrom fuel startEnv ⟨0, func.hhasBlock⟩
where startEnv := Env.init args

end

/- Noncomputable, classical execution of Func.eval -/
section NoFuel

/-- More fuel does not change an existing result -/
def FuelMono (f : Nat → Option α) : Prop :=
  ∀ ⦃m n⦄, m ≤ n → ∀ ⦃r⦄, f m = some r → f n = some r

/-- More fuel does not change an existing result -/
def FuelBased (f : Nat → Option α) : Prop :=
  f 0 = none

noncomputable def Fuel.limit (f : Nat → Option α) : Option α :=
  open Classical in if h : ∃ n, (f n).isSome then f h.choose else .none

private def Fuel.observe : PoisonOr (Option α × β) → Option (PoisonOr (α × β))
  | .poison => some PoisonOr.poison
  | .value (.none, _) => none
  | .value (.some r, s') => .some (.value (r, s'))

public noncomputable def Func.runFrom (func : Func) (env : ⟪func.Γ⟫) (i : Fin func.n) :
    EffectM (Vals func.tRets) := fun s =>
  let f n := Fuel.observe (func.evalFrom n env i s)
  let determined := Fuel.limit f
  match determined with
  | some x => x >>= PoisonOr.value
  | none => .poison

public noncomputable def Func.run (func : Func)
    (args : (i : Fin func.Γ.args.length) → ⟦func.Γ.args[i]⟧) : EffectM (Vals func.tRets) := fun s =>
  let f n := Fuel.observe (func.eval n args s)
  let determined := Fuel.limit f
  match determined with
  | some x => x >>= PoisonOr.value
  | none => .poison

section Lemmas

theorem mono_of_succ {f : Nat → Option α} (h : ∀ n r, f n = some r → f (n + 1) = some r) :
    FuelMono f := by
  intro m n hmn r hm
  induction hmn with
  | refl => exact hm
  | step _ ih => exact h _ _ ih

theorem Func.observe_evalFrom_succ (f : Func) :
    ∀ (fuel : Nat) (E : ⟪f.Γ⟫) (i : Fin f.n) (s : GlobalState) (r),
      Fuel.observe (f.evalFrom fuel E i s) = some r →
        Fuel.observe (f.evalFrom (fuel + 1) E i s) = some r := by
  intro fuel
  induction fuel with
  | zero => simp [Func.evalFrom, Fuel.observe]
  | succ fuel ih =>
    intro E i s r h
    simp [Fuel.observe, Func.evalFrom] at h ⊢
    rcases hb : BasicBlock.run f.blockParams E (f.blocks i) s with _ | ⟨⟨E, res⟩, s'⟩ <;>
      simp [hb] at *
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
  exact Func.observe_evalFrom_succ _ _ _ _ _ _ h

theorem Func.evalFrom_mono (f : Func) (env) (i) (s) :
    FuelMono (fun n => Fuel.observe (f.evalFrom n env i s)) := by
  refine mono_of_succ fun n r h => ?_
  exact Func.observe_evalFrom_succ _ _ _ _ _ _ h

theorem Func.eval_based (f : Func) (args) (s) :
    FuelBased (fun n => Fuel.observe (f.eval n args s)) := by rfl

theorem Func.evalFrom_based (f : Func) (env) (i) (s) :
    FuelBased (fun n => Fuel.observe (f.evalFrom n env i s)) := by rfl

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

theorem Fuel.exists_of_limit_eq_some (hf : FuelMono f) :
    Fuel.limit f = some r ↔ ∃ n, f n = some r := by
  constructor <;> intro h
  · unfold limit at h
    simp at h
    obtain ⟨h, hh⟩ := h
    refine ⟨h.choose, hh⟩
  · obtain ⟨n, hn⟩ := h
    exact limit_eq_of hf hn

theorem Fuel.limit_eq_none_iff : Fuel.limit f = none ↔ ∀ n, f n = none := by
  constructor
  · intro hnolim
    intro n
    simp [limit] at hnolim
    apply Classical.byContradiction
    intro h
    replace h : (f n).isSome := by
      simp [Option.ne_none_iff_isSome] at h; exact h
    replace hnolim := hnolim n h
    have : ∀ (h : ∃ x, (f x).isSome = true), f h.choose ≠ none := by
      intro h
      exact Option.isSome_iff_ne_none.mp (Classical.choose_spec h)
    grind only
  · intro h
    simp [limit]
    intro x h'
    rw [h x] at h'
    simp [Option.isSome] at h'

theorem Fuel.limit_shift (hf : FuelMono f) (hb : FuelBased f) :
    Fuel.limit (fun n => f (n + 1)) = Fuel.limit f := by
  rcases h : limit f
  · rw [limit_eq_none_iff] at h
    rw [limit_eq_none_iff]
    intro n
    exact h (n + 1)
  · rw [exists_of_limit_eq_some hf] at h
    obtain ⟨n, hn⟩ := h
    have : n ≥ 1 := by
      apply Classical.byContradiction
      intro h
      replace h : n = 0 := by omega
      rw [h, hb] at hn
      simp at hn
    rw [exists_of_limit_eq_some ?_]
    refine ⟨n - 1, by simp [this, hn]⟩
    unfold FuelMono
    intro m n h r
    dsimp
    have := hf (show (m + 1) ≤ (n + 1) by omega) (r := r)
    exact this

theorem Func.run_eq_of_eval (f : Func) (args) (s) {fuel v s'}
    (h : f.eval fuel args s = .value (some v, s')) : f.run args s = .value (v, s') := by
  unfold Func.run
  dsimp only
  replace h' : Fuel.observe (f.eval fuel args s) = some (.value (v, s')) := by
    simp [Fuel.observe, h]
  simp [Fuel.limit_eq_of (Func.eval_mono f args s) h']

theorem Func.runFrom_eq_of_eval (f : Func) (s) (env) (i) {fuel v s'}
    (h : f.evalFrom fuel env i s = .value (some v, s')) : f.runFrom env i s = .value (v, s') := by
  unfold Func.runFrom
  dsimp only
  replace h' : Fuel.observe (f.evalFrom fuel env i s) = some (.value (v, s')) := by
    simp [Fuel.observe, h]
  simp [Fuel.limit_eq_of (Func.evalFrom_mono f env i s) h']

end Lemmas

end NoFuel

public section RunTheorems

private theorem Func.eval_init (func : Func) (fuel : Nat) (args : _) :
    func.eval (fuel + 1) args =
      (do
        let (E', res) ← (func.blocks ⟨0, func.hhasBlock⟩).run func.blockParams (Env.init args)
        match res with
        | .inl vals =>
          return (some vals)
        | .inr next =>
          func.evalFrom fuel E' next) :=
  rfl

theorem Func.run_runFrom_eq (func : Func) (args : _) :
    func.run args = func.runFrom (Env.init args) ⟨0, func.hhasBlock⟩ := by
  unfold Func.run Func.runFrom Func.eval
  rfl

noncomputable def Func.continue {func : Func} (env : ⟪func.Γ⟫)
    (bbRes : ExitResult func.tRets func.n) := do
  match bbRes with
  | .inl vals =>
    return vals
  | .inr nextIdx =>
    func.runFrom env nextIdx

theorem Func.runFrom_eq {func : Func} {E} {i} {s} :
    func.runFrom E i s =
      (do
        let ((E', res), s') ← (func.blocks i).run func.blockParams E s
        func.continue E' res s') := by
  unfold Func.continue Func.runFrom
  dsimp
  rw [← Fuel.limit_shift (Func.evalFrom_mono func E i s) (Func.evalFrom_based func E i s)]
  simp [Func.evalFrom, Fuel.observe]
  rcases hb : BasicBlock.run func.blockParams E (func.blocks i) s with _ | ⟨⟨E', res⟩, s'⟩ <;>
    simp [Fuel.limit]
  cases res <;> simp

theorem Func.exit {E} : Func.continue E (Sum.inl vals) S = .value (vals, S) := by rfl

theorem Func.continue_next {E} :
    Func.continue (func := func) E (Sum.inr idx) S = Func.runFrom func E idx S := by rfl

end RunTheorems

end LeanMLIR.RIR
