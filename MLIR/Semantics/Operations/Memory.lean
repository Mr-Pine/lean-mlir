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

/-- A store: UB unless into a live writable object; poison leaves and padding stored undefined,
pointer leaves undefined and recorded. -/
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

/-- `gep` by `byteOff` bytes (the offset's bits, the address wrapping): poison when `nuw` and the
address wraps unsigned, or `nusw` and the offset, signed, takes it out of `[0, 2 ^ 64)`: below the
block's start for a negative one, past `2 ^ 64` for another (`gep_nusw_iff`). -/
def gep (f : GepFlags) (byteOff : PoisonOr (BitVec 64)) (ptr : PoisonOr Pointer) :
    PoisonOr Pointer := do
  let ptr ← ptr
  let off ← byteOff
  if f.nuw ∧ ptr.offset.uaddOverflow off then
    .poison
  if f.nusw ∧
      (if off.msb then ptr.offset.toNat < (-off).toNat else ptr.offset.uaddOverflow off) then
    .poison
  return ptr.add off

/-- `gep` back by `n` bytes, adding `-n`: poison when `nusw` and that leaves the block below its
start, or `nuw` and the address wraps unsigned. -/
def gepBack (f : GepFlags) (n : Nat) (ptr : PoisonOr Pointer) : PoisonOr Pointer := do
  let ptr ← ptr
  if f.nusw ∧ ptr.offset.toNat < n then
    .poison
  if f.nuw ∧ ptr.offset.uaddOverflow (-BitVec.ofNat 64 n) then
    .poison
  return ptr.add (-BitVec.ofNat 64 n)

/-- `gep` by `byteOff + i * stride` bytes, `i` signed (`nusw`): poison unless the offset and the
addresses it passes through stay in range, its constant and dynamic parts in either order (LangRef's
`nusw` rules, checked for both orders: less defined), and for `nuw` the unsigned address too. -/
def gepSigned (f : GepFlags) (byteOff stride : Nat) (i : BitVec 64) (ptr : PoisonOr Pointer) :
    PoisonOr Pointer := do
  let p ← ptr
  let a : Int := p.offset.toNat
  let d : Int := i.toInt * stride
  if -2 ^ 63 ≤ d ∧ byteOff + d < 2 ^ 63 ∧ byteOff < (2 ^ 63 : Int) ∧ a + byteOff < 2 ^ 64 ∧
      0 ≤ a + d ∧ 0 ≤ a + byteOff + d ∧ a + byteOff + d < 2 ^ 64 ∧
      (f.nuw → p.offset.toNat + (byteOff + i.toNat * stride) < 2 ^ 64) then
    .value (p.add (BitVec.ofInt 64 (byteOff + d)))
  else
    .poison

/-- `gep` by `byteOff + index * stride` bytes: for `nusw` the index signed (`gepSigned`) unless the
offset is below `2 ^ 63`, where signed and unsigned agree; for `nuw` poison when the offset wraps
unsigned; the address then as `gep` adds it. -/
def gepDyn (f : GepFlags) (byteOff stride : Nat) (ptr : PoisonOr Pointer) (idx : IntW 64) :
    PoisonOr Pointer := do
  let i ← idx
  if f.nusw ∧ 2 ^ 63 ≤ byteOff + i.toNat * stride then
    gepSigned f byteOff stride i ptr
  else if f.nuw ∧ ¬byteOff + i.toNat * stride < 2 ^ 64 then
    .poison
  else
    gep f (.value (BitVec.ofNat 64 (byteOff + i.toNat * stride))) ptr

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
  throwUBIf (¬Live state.mem src (8 * len))
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
  throwUBIf (¬Live state.mem src (8 * len))
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
