/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SSA.Projects.RIR.Poison
public import SSA.Projects.RIR.Semantics.Effectful.HasUB
public import SSA.Projects.RIR.Semantics.Effectful.Memory
public import SSA.Projects.RIR.SimpSets

namespace LeanMLIR.RIR

@[expose] public section

/--
`EffectM` is the monad of side-effects
-/
-- v4.34: reducible, or the `EffectM.run_*` lemmas no longer match.
@[implicit_reducible]
def EffectM :=
  StateT GlobalState PoisonOr

/--
`MemorySSAM` is the monad of just the subset of side-effects
which can be purified by expressing them in the SSA def-use chain.
-/
def MemorySSAM :=
  StateT MemoryState PoisonOr

namespace EffectM

/-! ## Instances -/

instance : Monad EffectM := by
  unfold EffectM; infer_instance

instance : LawfulMonad EffectM := by
  unfold EffectM; infer_instance

instance : MonadStateOf GlobalState EffectM := by
  unfold EffectM; infer_instance

instance : MonadStateOf AllocState EffectM where
  get := do
    return (← getThe GlobalState).alloc
  set alloc := modifyThe GlobalState ({ · with alloc })
  modifyGet f :=
    modifyGetThe GlobalState fun { mem, alloc } =>
      let ⟨x, alloc⟩ := f alloc
      ⟨x, { mem, alloc }⟩

instance : MonadStateOf MemoryState EffectM where
  get := do
    return (← getThe GlobalState).mem
  set mem := modifyThe GlobalState ({ · with mem })
  modifyGet f :=
    modifyGetThe GlobalState fun { mem, alloc } =>
      let ⟨x, mem⟩ := f mem
      ⟨x, { mem, alloc }⟩

/-! ## Constructors -/

abbrev poison : EffectM (PoisonOr α) :=
  pure PoisonOr.poison

abbrev value (a : α) : EffectM (PoisonOr α) :=
  pure (PoisonOr.value a)

instance : HasUB EffectM where
  throwUB := StateT.lift PoisonOr.poison

/-! ## Lemmas -/

@[simp, mlir_effect]
theorem pure_eq (x : α) (s) : (pure x : EffectM _) s = .value (x, s) :=
  rfl

@[simp, mlir_effect]
theorem bind_eq (x : EffectM α) (f : α → EffectM β) (s) :
    (x >>= f) s = x s >>= (fun (x, s) => f x s) :=
  rfl

@[simp, mlir_effect]
theorem run_pure : StateT.run (pure x : EffectM α) s = .value (x, s) :=
  rfl

@[simp, mlir_effect]
theorem run_ub : StateT.run (throwUB : EffectM α) s = .poison :=
  rfl

@[simp, mlir_effect]
theorem run_bind (x : EffectM α) :
    StateT.run (x >>= f : EffectM β) s = StateT.run x s >>= (fun p => StateT.run (f p.1) p.2) :=
  rfl

@[simp, mlir_effect]
theorem run_map (x : EffectM α) :
    StateT.run (f <$> x : EffectM β) s = (fun p => (f p.1, p.2)) <$> StateT.run x s :=
  rfl

@[simp, mlir_effect]
theorem get_eq (s : GlobalState) : (get : EffectM GlobalState) s = .value (s, s) :=
  rfl

@[simp, mlir_effect]
theorem set_eq (s s' : GlobalState) : (set s' : EffectM PUnit) s = .value (⟨⟩, s') :=
  rfl

@[simp, mlir_effect]
theorem map_eq (f : α → β) (x : EffectM α) (s) : (f <$> x) s = (fun p => (f p.1, p.2)) <$> x s :=
  rfl

end EffectM

end
