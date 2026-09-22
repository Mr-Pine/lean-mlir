module

public import MLIR.SimpSets
public import MLIR.Ty
public import MLIR.IntPred
public import MLIR.Semantics.Env
public import MLIR.Semantics.Effectful.Memory.Operations
public import MLIR.Semantics.Effectful.EffectM

namespace MLIR.Operation

@[expose] public section

def load (dst : Dst Γ τ) (ptr : PoisonOr Pointer) (env : ⟪Γ⟫) : EffectM ⟪Γ⟫ := do
  let ptr ←
    match ptr with
    | .poison =>
      throwUB
    | .value p =>
      pure p
  let state ← get
  throwUBIf (¬Fits state.mem ptr τ.width)
  let flattened := state.mem.readAt ptr τ.width
  let value : ⟦τ⟧ ←
    match τ.unflatten flattened with
    | .poison =>
      throwUB
    | .value v =>
      pure (.value v)
  return env.write dst value

def store (ptr : PoisonOr Pointer) (v : ⟦τ⟧) (env : ⟪Γ⟫) : EffectM ⟪Γ⟫ := do
  let ptr ←
    match ptr with
    | .poison =>
      throwUB
    | .value p =>
      pure p
  let state ← get
  throwUBIf (¬Fits state.mem ptr τ.width)
  let flattened ←
    match τ.flatten v with
    | .poison =>
      throwUB
    | .value v =>
      pure v
  let updated := { state with mem := state.mem.storeAt ptr flattened }
  _ ← set updated
  return env

end

end MLIR.Operation
