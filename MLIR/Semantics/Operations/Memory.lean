module

public import MLIR.SimpSets
public import MLIR.Ty
public import MLIR.IntPred
public import MLIR.Semantics.Env
public import MLIR.Semantics.Operations.Scalar
public import MLIR.Semantics.Effectful.Memory.Operations
public import MLIR.Semantics.Effectful.EffectM

namespace MLIR.Operation

@[expose] public section

/-- A load: UB outside its block, each leaf poison where a bit is undefined (a dead object's). -/
def load (dst : Dst Γ τ) (ptr : PoisonOr Pointer) (env : ⟪Γ⟫) : EffectM ⟪Γ⟫ := do
  let ptr ←
    match ptr with
    | .poison =>
      throwUB
    | .value p =>
      pure p
  let state ← get
  throwUBIf (¬InBounds state.mem ptr τ.width)
  let value : ⟦τ⟧ := τ.unflattenDef (state.mem.readAt ptr τ.width) (state.mem.definedAt ptr τ.width)
  return env.write dst value

/-- A store: UB unless into a live object; poison leaves and padding stored undefined. A pointer
has no bit pattern: storing one is UB. -/
def store (ptr : PoisonOr Pointer) (v : ⟦τ⟧) (env : ⟪Γ⟫) : EffectM ⟪Γ⟫ := do
  let ptr ←
    match ptr with
    | .poison =>
      throwUB
    | .value p =>
      pure p
  let state ← get
  throwUBIf (¬Room state.mem ptr τ.width)
  throwUBIf τ.hasPtr
  let (bits, defined) := τ.flattenDef v
  let updated := { state with mem := state.mem.storeDef ptr bits defined }
  _ ← set updated
  return env

/-- `icmp eq`/`ne` on pointers: the same block and offset, or not. -/
@[mlir_operation]
def ptrcmp (ne : Bool) (x y : PoisonOr Pointer) : IntW 1 := do
  let a ← x
  let b ← y
  return BitVec.ofBool ((a == b) != ne)

def gep (byteOff : PoisonOr (BitVec 64)) (ptr : PoisonOr Pointer) : PoisonOr Pointer := do
  let ptr ← ptr
  let off ← byteOff
  if ptr.offset.uaddOverflow off then
    .poison
  return ptr.add off

/-- `gep` back by `n` bytes, adding `-n`: poison when that leaves the block below its start. -/
def gepBack (n : Nat) (ptr : PoisonOr Pointer) : PoisonOr Pointer := do
  let ptr ← ptr
  if ptr.offset.toNat < n then
    .poison
  return ptr.add (-BitVec.ofNat 64 n)

/-- `gep` by `byteOff + index * stride` bytes, the index unsigned: poison when that does not fit in
64 bits, as when the pointer's offset overflows. -/
@[mlir_operation]
def gepDyn (byteOff stride : Nat) (ptr : PoisonOr Pointer) (idx : IntW 64) : PoisonOr Pointer := do
  let i ← idx
  let off := byteOff + i.toNat * stride
  if off < 2 ^ 64 then
    gep (.value (BitVec.ofNat 64 off)) ptr
  else
    .poison

def memset (dst : PoisonOr Pointer) (val : IntW 8) (len : IntW w) (env : ⟪Γ⟫) : EffectM ⟪Γ⟫ := do
  let .value (dst, val, len) := do
    return (← dst, ← val, (← len).toNat) | throwUB
  let state ← get
  throwUBIf (¬Room state.mem dst (8 * len))
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
  throwUBIf (¬Room state.mem dst (8 * len))
  -- reading a dead object is an access too
  throwUBIf (¬Room state.mem src (8 * len))
  let replacement := state.mem.readAt src (8 * len)
  let defined := state.mem.definedAt src (8 * len)
  let updated := { state with mem := state.mem.storeDef dst replacement defined }
  _ ← set updated
  return env

/-- `llvm.lifetime.start` of `p`'s object; poison: no effect. -/
def lifetimeStart (p : PoisonOr Pointer) (env : ⟪Γ⟫) : EffectM ⟪Γ⟫ := do
  let .value p := p | return env
  let state ← get
  _ ← set { state with mem := state.mem.lifetimeStart p }
  return env

/-- `llvm.lifetime.end` of `p`'s object; poison: no effect. -/
def lifetimeEnd (p : PoisonOr Pointer) (env : ⟪Γ⟫) : EffectM ⟪Γ⟫ := do
  let .value p := p | return env
  let state ← get
  _ ← set { state with mem := state.mem.lifetimeEnd p }
  return env

/-- `llvm.assume`: UB unless the condition is `1`. -/
def assume (c : IntW 1) (env : ⟪Γ⟫) : EffectM ⟪Γ⟫ := do
  throwUBIf (c ≠ .value 1#1)
  return env

end

end MLIR.Operation
