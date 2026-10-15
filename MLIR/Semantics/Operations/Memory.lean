module

public import MLIR.SimpSets
public import MLIR.Ty
public import MLIR.IntPred
public import MLIR.Semantics.Env
public import MLIR.Semantics.Operations.Scalar
public import MLIR.Semantics.Effectful.Memory.Copy
public import MLIR.Semantics.Effectful.EffectM

namespace MLIR.Operation

@[expose] public section

/-- A load: UB outside its block, each integer leaf poison where a bit is not known (undefined, a
dead object's, and not a live stored pointer's), a pointer leaf the pointer stored there while it
stays live. -/
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
      (τ.unflattenDef (state.mem.readAt ptr τ.width) (state.mem.knownAt ptr τ.width))
  return env.write dst value

/-- A store: UB unless into a live writable object; poison leaves and padding stored undefined,
pointer leaves their addresses, recorded. -/
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

/-- Lane `i` of a `vector<l x iw>` at `p`: `i * (w / 8)` bytes on. -/
def lanePtr (p : Pointer) (w : Nat) (i : Nat) : Pointer :=
  p.add (BitVec.ofNat 64 (i * (w / 8)))

/-- A masked access of lane `i` is in bounds: its offset does not wrap, and `w` bits fit. -/
def LaneInBounds (m : MemoryState) (p : Pointer) (w i : Nat) : Prop :=
  p.offset.toNat + i * (w / 8) < 2 ^ 64 ∧ InBounds m (lanePtr p w i) w

instance : Decidable (LaneInBounds m p w i) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- `llvm.masked.load`: lane `i` loaded as `load` does where `mask[i]` is set, UB out of bounds,
else `passthru[i]`, no memory read; UB for a poison pointer or mask lane, where LLVM may access
nothing (less defined). -/
def maskedLoad {l w : Nat} (dst : Dst Γ (.vec l w)) (ptr : PoisonOr Pointer) (mask : ⟦.vec l 1⟧)
    (passthru : ⟦.vec l w⟧) (env : ⟪Γ⟫) : EffectM ⟪Γ⟫ := do
  let .value p := ptr | throwUB
  throwUBIf (mask.toList.any (·.isPoison))
  let state ← get
  throwUBIf (¬∀ i : Fin l, mask[i] = .value 1#1 → LaneInBounds state.mem p w i)
  let value : ⟦.vec l w⟧ :=
    Vector.ofFn fun i =>
      if mask[i] = .value 1#1 then
        (Ty.bv w).unflattenDef (state.mem.readAt (lanePtr p w i) w)
          (state.mem.knownAt (lanePtr p w i) w)
      else passthru[i]
  return env.write dst value

/-- `llvm.masked.store`: lane `i` stored as `store` does where `mask[i]` is set, first to last;
UB for a poison pointer or mask lane, where LLVM may access nothing (less defined). -/
def maskedStore {l w : Nat} (v : ⟦.vec l w⟧) (ptr : PoisonOr Pointer) (mask : ⟦.vec l 1⟧)
    (env : ⟪Γ⟫) : EffectM ⟪Γ⟫ := do
  let .value p := ptr | throwUB
  throwUBIf (mask.toList.any (·.isPoison))
  throwUBIf (¬∀ i : Fin l, mask[i] = .value 1#1 → p.offset.toNat + i * (w / 8) < 2 ^ 64)
  (List.finRange l).foldlM (init := env) fun env (i : Fin l) =>
      if mask[i] = .value 1#1 then store (τ := .bv w) (.value (lanePtr p w i)) v[i] env
      else pure env

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

/-- `llvm.memcpy`: UB unless `dst` is room for `len` bytes, `src` live and the ranges disjoint; the
bits, their definedness and the live pointers wholly inside them copied. -/
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
  let ptrs := state.mem.ptrsIn src (8 * len)
  let updated := { state with mem := state.mem.storeCopy dst replacement defined ptrs }
  _ ← set updated
  return env

/-- `llvm.memmove`: `memcpy` whose ranges may overlap, `src` (its bits and pointers) read before
`dst` is written. -/
def memmove (dst : PoisonOr Pointer) (src : PoisonOr Pointer) (len : IntW w) (env : ⟪Γ⟫) :
    EffectM ⟪Γ⟫ := do
  let .value (dst, src, len) := do
    return (← dst, ← src, (← len).toNat) | throwUB
  let state ← get
  throwUBIf (¬Room state.mem dst (8 * len))
  throwUBIf (¬Live state.mem src (8 * len))
  let replacement := state.mem.readAt src (8 * len)
  let defined := state.mem.definedAt src (8 * len)
  let ptrs := state.mem.ptrsIn src (8 * len)
  let updated := { state with mem := state.mem.storeCopy dst replacement defined ptrs }
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
