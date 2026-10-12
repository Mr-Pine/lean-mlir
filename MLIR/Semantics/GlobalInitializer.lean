module

public import MLIR.GlobalInitializer
public import MLIR.Semantics.Func

namespace MLIR

@[expose] public section

def GlobalInitializer.blockParams {Γ : Ctx} : Fin 1 → Dsts Γ [] := fun _ => Dsts.nil

def GlobalInitializer.initEnv (initializer : GlobalInitializer) :=
  Env.init (Γ := initializer.Γ)
    (fun i => by
      simp [initializer.hΓ] at i
      exact i.elim0)

def GlobalInitializer.value (initializer : GlobalInitializer) := do
  let (_, blockVal) ← initializer.block.run blockParams initializer.initEnv
  let .inl (Vals.cons v Vals.nil) := blockVal | throwUB
  return v

theorem GlobalInitializer.compute_value (initializer : GlobalInitializer) v
    (h :
      ∃ env',
        initializer.block.run blockParams initializer.initEnv s =
          .value ((env', .inl (Vals.cons v Vals.nil)), s)) :
    initializer.value s = .value (v, s) := by
  unfold value
  obtain ⟨env, h'⟩ := h
  rw [EffectM.bind_eq, h']
  dsimp
  rfl

end

end MLIR
