module

public import SSA.Projects.RIR.SimpSets
public import SSA.Projects.RIR.Ty
public import SSA.Projects.RIR.IntPred
public import SSA.Projects.RIR.Semantics.Env
public import SSA.Projects.RIR.Semantics.Effectful.Memory.Operations
public import SSA.Projects.RIR.Semantics.Effectful.EffectM

namespace LeanMLIR.RIR.Operation

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
  let value : ⟦τ⟧ := τ.unflatten flattened
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

def gep (byteOff : PoisonOr (BitVec 64)) (ptr : PoisonOr Pointer) : PoisonOr Pointer := do
  let ptr ← ptr
  let off ← byteOff
  if ptr.offset.uaddOverflow off then
    .poison
  return ptr.add off

end

end LeanMLIR.RIR.Operation
