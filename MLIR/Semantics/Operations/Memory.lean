module

public import MLIR.SimpSets
public import MLIR.Ty
public import MLIR.IntPred
public import MLIR.Semantics.Env
public import MLIR.Semantics.Operations.Scalar
public import MLIR.Semantics.Effectful.Memory.Pointers
public import MLIR.Semantics.Effectful.EffectM

namespace MLIR.Operation

@[expose] public section

/-- A load: UB outside its block, each leaf poison where a bit is undefined (a dead object's), a
pointer leaf the pointer stored there while its bits stay undefined. -/
def load (dst : Dst Γ τ) (ptr : PoisonOr Pointer) (env : ⟪Γ⟫) : EffectM ⟪Γ⟫ := do
  let ptr ←
    match ptr with
    | .poison =>
      throwUB
    | .value p =>
      pure p
  let state ← get
  throwUBIf (¬InBounds state.mem ptr τ.width)
  let value : ⟦τ⟧ :=
    τ.setPtrs 0 (fun o => state.mem.ptrAt ptr.id (ptr.offsetInBits + o))
      (τ.unflattenDef (state.mem.readAt ptr τ.width) (state.mem.definedAt ptr τ.width))
  return env.write dst value

/-- A store: UB unless into a live object; poison leaves and padding stored undefined, pointer
leaves undefined and recorded. -/
def store (ptr : PoisonOr Pointer) (v : ⟦τ⟧) (env : ⟪Γ⟫) : EffectM ⟪Γ⟫ := do
  let ptr ←
    match ptr with
    | .poison =>
      throwUB
    | .value p =>
      pure p
  let state ← get
  throwUBIf (¬Room state.mem ptr τ.width)
  let (bits, defined) := τ.flattenDef v
  let updated :=
    { state with mem := (state.mem.storeDef ptr bits defined).recordPtrs ptr (τ.ptrLeaves 0 v) }
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

/-- `gep` by `off` bytes, signed: poison unless the offset it reaches is in `[0, 2 ^ 64)` (LLVM
poisons `inbounds` out of the object, unchecked: less defined). -/
def gepInt (off : Int) (ptr : PoisonOr Pointer) : PoisonOr Pointer := do
  let p ← ptr
  if 0 ≤ (p.offset.toNat : Int) + off ∧ (p.offset.toNat : Int) + off < 2 ^ 64 then
    .value (p.add (BitVec.ofInt 64 off))
  else
    .poison

/-- `gep` by `byteOff + index * stride` bytes: the index read unsigned where the offset that gives
stays in `[0, 2 ^ 64)`, else signed (`gepInt`), as LLVM sign-extends it; both readings give the same
bits, poison where neither stays. -/
def gepDyn (byteOff stride : Nat) (ptr : PoisonOr Pointer) (idx : IntW 64) : PoisonOr Pointer := do
  let i ← idx
  let off := byteOff + i.toNat * stride
  if off < 2 ^ 64 then
    (gep (.value (BitVec.ofNat 64 off)) ptr).orElse (gepInt (byteOff + i.toInt * stride) ptr)
  else
    gepInt (byteOff + i.toInt * stride) ptr

/-- `gepDyn`'s unsigned reading alone, which the steps simplify first. -/
@[mlir_operation]
def gepDynUnsigned (byteOff stride : Nat) (ptr : PoisonOr Pointer) (idx : IntW 64) :
    PoisonOr Pointer := do
  let i ← idx
  let off := byteOff + i.toNat * stride
  if off < 2 ^ 64 then gep (.value (BitVec.ofNat 64 off)) ptr else .poison

attribute [mlir_operation] PoisonOr.value_orElse PoisonOr.poison_orElse

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

/-- `llvm.memmove`: `memcpy` whose ranges may overlap, `src` read before `dst` is written. -/
def memmove (dst : PoisonOr Pointer) (src : PoisonOr Pointer) (len : IntW w) (env : ⟪Γ⟫) :
    EffectM ⟪Γ⟫ := do
  let .value (dst, src, len) := do
    return (← dst, ← src, (← len).toNat) | throwUB
  let state ← get
  throwUBIf (¬Room state.mem dst (8 * len))
  throwUBIf (¬Room state.mem src (8 * len))
  let replacement := state.mem.readAt src (8 * len)
  let defined := state.mem.definedAt src (8 * len)
  let updated := { state with mem := state.mem.storeDef dst replacement defined }
  _ ← set updated
  return env

/-- `ptrtoaddr`: `p`'s block's address `addr p.id` plus its offset, truncated or zero-extended to
`w` bits as `ptrtoint` is. -/
@[mlir_operation]
def ptrtoaddr (addr : BlockId → BitVec 64) {w : Nat} (p : PoisonOr Pointer) : IntW w := do
  let p ← p
  return (addr p.id + p.offset).setWidth w

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
