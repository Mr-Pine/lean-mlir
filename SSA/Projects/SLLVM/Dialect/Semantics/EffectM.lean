/-
Released under Apache 2.0 license as described in the file LICENSE.
-/

import LeanMLIR.Util.Poison
import SSA.Projects.SLLVM.Tactic.SimpSet
import SSA.Projects.SLLVM.Dialect.Semantics.HasUB
import SSA.Projects.SLLVM.Dialect.Semantics.Memory

namespace LeanMLIR

/--
`EffectM` is the monad of side-effects for the SLLVM dialect
-/
def EffectM := StateT GlobalState PoisonOr

/--
`MemorySSAM` is the monad of just the subset of side-effects of SLLVM
which can be purified by expressing them in the SSA def-use chain.
-/
def MemorySSAM := StateT MemoryState PoisonOr

namespace EffectM

/-! ## Instances -/

instance : Monad EffectM        := by unfold EffectM; infer_instance
instance : LawfulMonad EffectM  := by unfold EffectM; infer_instance

instance : MonadStateOf GlobalState EffectM := by unfold EffectM; infer_instance

-- NOTE: `globals` is threaded through untouched here and in every other
-- rebuild of a `GlobalState`: the symbol table is write-once, installed by
-- `GlobalState.ofGlobals` and only ever read.
instance : MonadStateOf AllocState EffectM where
  get := do return (← getThe GlobalState).alloc
  set alloc := modifyThe GlobalState ({ · with alloc })
  modifyGet f := modifyGetThe GlobalState fun { mem, alloc, globals } =>
    let ⟨x, alloc⟩ := f alloc
    ⟨x, { mem, alloc, globals }⟩

instance : MonadStateOf MemoryState EffectM where
  get := do return (← getThe GlobalState).mem
  set mem := modifyThe GlobalState ({ · with mem })
  modifyGet f := modifyGetThe GlobalState fun { mem, alloc, globals } =>
    let ⟨x, mem⟩ := f mem
    ⟨x, { mem, alloc, globals }⟩

/-! ## Constructors -/

abbrev poison : EffectM (PoisonOr α) := pure PoisonOr.poison
abbrev value (a : α) : EffectM (PoisonOr α) := pure (PoisonOr.value a)

instance : HasUB EffectM where
  throwUB := StateT.lift PoisonOr.poison

/-! ## Lemmas -/

@[simp, simp_sllvm]
theorem pure_eq (x : α) (s) : (pure x : EffectM _) s = .value (x, s) := rfl

@[simp, simp_sllvm]
theorem bind_eq (x : EffectM α) (f : α → EffectM β) (s) :
    (x >>= f) s = x s >>= (fun (x, s) => f x s) := rfl

@[simp, simp_denote, simp_sllvm]
lemma run_pure : StateT.run (pure x : EffectM α) s = .value (x, s) := rfl

@[simp, simp_denote, simp_sllvm]
lemma run_ub : StateT.run (throwUB : EffectM α) s = .poison := rfl

@[simp, simp_denote, simp_sllvm]
lemma run_bind (x : EffectM α) :
    StateT.run (x >>= f : EffectM β) s
    = StateT.run x s >>= (fun p => StateT.run (f p.1) p.2) :=
  rfl

@[simp, simp_denote, simp_sllvm]
lemma run_map (x : EffectM α) :
    StateT.run (f <$> x : EffectM β) s = (fun p => (f p.1, p.2)) <$> StateT.run x s := rfl

/-! ## Refinement -/
section Refinement
variable {α β} [HRefinement α β]

@[simp, simp_denote]
instance : HRefinement (EffectM α) (EffectM β) where
  IsRefinedBy x y := ∀ s, StateT.run x s ⊑ StateT.run y s

end Refinement

end EffectM

/-! ## MemorySSAM -/
namespace MemorySSAM

instance : Monad MemorySSAM        := by unfold MemorySSAM; infer_instance
instance : LawfulMonad MemorySSAM  := by unfold MemorySSAM; infer_instance
instance : MonadStateOf MemoryState MemorySSAM := by
  unfold MemorySSAM; infer_instance

instance : MonadLift MemorySSAM EffectM where
  monadLift x := fun { mem, alloc, globals } =>
    match x mem with
    | .poison => .poison
    | .value ⟨y, mem⟩ => .value ⟨y, { mem, alloc, globals }⟩

instance : HasUB MemorySSAM where
  throwUB := StateT.lift PoisonOr.poison

/-! ### Lemmas

The same `run` lemmas `EffectM` has above; without them, `simp` cannot see
through a `do`-block of memory operations. -/

@[simp, simp_denote, simp_sllvm]
lemma run_pure {α} (x : α) (m) : StateT.run (pure x : MemorySSAM α) m = .value (x, m) := rfl

@[simp, simp_denote, simp_sllvm]
lemma run_ub {α} (m) : StateT.run (throwUB : MemorySSAM α) m = .poison := rfl

@[simp, simp_denote, simp_sllvm]
lemma run_bind {α β} (x : MemorySSAM α) (f : α → MemorySSAM β) (m) :
    StateT.run (x >>= f : MemorySSAM β) m
      = StateT.run x m >>= (fun p => StateT.run (f p.1) p.2) :=
  rfl

@[simp, simp_denote, simp_sllvm]
lemma run_map {α β} (f : α → β) (x : MemorySSAM α) (m) :
    StateT.run (f <$> x : MemorySSAM β) m = (fun p => (f p.1, p.2)) <$> StateT.run x m := rfl

@[simp, simp_denote, simp_sllvm]
lemma run_getThe (m : MemoryState) :
    StateT.run (getThe MemoryState : MemorySSAM MemoryState) m = .value (m, m) := rfl

@[simp, simp_denote, simp_sllvm]
lemma run_modifyThe (f : MemoryState → MemoryState) (m : MemoryState) :
    StateT.run (modifyThe MemoryState f : MemorySSAM PUnit) m = .value (⟨⟩, f m) := rfl
