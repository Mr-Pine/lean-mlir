module

public import SSA.Projects.RIR.SimpSets
public import SSA.Projects.RIR.Ty
public import SSA.Projects.RIR.IntPred
public import SSA.Projects.RIR.Semantics.Env
public import SSA.Projects.RIR.Semantics.Operations.Scalar
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

/-- LLVM GEP without no-wrap flags. Sign extension/truncation happens before scaling;
all offset arithmetic wraps at the (64-bit) pointer index width. Unlike the legacy
`gep` helper, wrapping is defined here, including when a negative index moves backwards. -/
def gepUnflagged (ptr : PoisonOr Pointer) (offsets : List (PoisonOr (BitVec 64))) :
    PoisonOr Pointer := do
  let ptr ← ptr
  let off ← offsets.foldlM (fun acc step => return acc + (← step)) 0
  return ptr.add off

def gepIndex (stride : Nat) (index : PoisonOr (BitVec w)) : PoisonOr (BitVec 64) := do
  let index ← index
  return BitVec.ofInt 64 index.toInt * BitVec.ofNat 64 stride

def memset (dst : PoisonOr Pointer) (val : IntW 8) (len : IntW w) (env : ⟪Γ⟫) : EffectM ⟪Γ⟫ := do
  let .value (dst, val, len) := do
    return (← dst, ← val, (← len).toNat) | throwUB
  let state ← get
  throwUBIf (¬Fits state.mem dst (8 * len))
  let replacement := val.replicate len
  let updated := { state with mem := state.mem.storeAt dst replacement }
  _ ← set updated
  return env

def memcpy (dst : PoisonOr Pointer) (src : PoisonOr Pointer) (len : IntW w) (env : ⟪Γ⟫) :
    EffectM ⟪Γ⟫ := do
  let .value (dst, src, len) := do
    return (← dst, ← src, (← len).toNat) | throwUB
  throwUBIf (¬(Range.of dst (8 * len)).Disjoint (Range.of src (8 * len)))
  let state ← get
  throwUBIf (¬Fits state.mem dst (8 * len))
  throwUBIf (¬Fits state.mem src (8 * len))
  let replacement := state.mem.readAt src (8 * len)
  let updated := { state with mem := state.mem.storeAt dst replacement }
  _ ← set updated
  return env

end

end LeanMLIR.RIR.Operation
