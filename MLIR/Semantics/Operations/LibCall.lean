module

public import MLIR.Semantics.Operations.Memory
public import MLIR.Semantics.Vals

/-!
# Library functions

Calls of external library functions the optimizer treats by their meaning (LLVM's `LibFunc`),
as callees: `Translate.libCall` binds an unbound call of one of these names and signatures to it.
What the C standard leaves unspecified (`memcmp`'s magnitude, `bcmp`'s nonzero value) is the
state's `Unspecified` choice.
-/

namespace MLIR.Operation

@[expose] public section

/-- Whether the first byte, lowest first, at which `x` and `y` differ is less in `x`, unsigned:
`memcmp`'s order. -/
def bytesLt : (n : Nat) → BitVec (8 * n) → BitVec (8 * n) → Bool
  | 0, _, _ => false
  | n + 1, x, y =>
    let a := x.extractLsb' 0 8
    let b := y.extractLsb' 0 8
    if a = b then bytesLt n (x.extractLsb' 8 (8 * n)) (y.extractLsb' 8 (8 * n)) else a.ult b

/-- `memcmp`'s result for bytes `x` and `y`: `0` if equal, else of the order's sign with `u`'s
magnitude; every value of that sign is some choice's. -/
def memcmpResult (u : Unspecified) (n : Nat) (x y : BitVec (8 * n)) : BitVec 32 :=
  if x = y then 0
  else if bytesLt n x y then -BitVec.ofNat 32 ((u.memcmp n x y).toNat % 2 ^ 31 + 1)
  else BitVec.ofNat 32 ((u.memcmp n x y).toNat % (2 ^ 31 - 1) + 1)

/-- `bcmp`'s result for bytes `x` and `y`: `0` if equal, else `u`'s nonzero choice. -/
def bcmpResult (u : Unspecified) (n : Nat) (x y : BitVec (8 * n)) : BitVec 32 :=
  if x = y then 0 else if u.bcmp n x y = 0 then 1 else u.bcmp n x y

@[simp]
theorem bcmpResult_self : bcmpResult u n x x = 0 := by
  simp [bcmpResult]

@[simp]
theorem memcmpResult_self : memcmpResult u n x x = 0 := by
  simp [memcmpResult]

theorem bcmpResult_eq_zero_iff : bcmpResult u n x y = 0 ↔ x = y := by
  unfold bcmpResult
  split
  · simp [*]
  · split <;> simp_all

theorem memcmpResult_eq_zero_iff : memcmpResult u n x y = 0 ↔ x = y := by
  unfold memcmpResult
  split
  · simp [*]
  · split <;> simp only [*, iff_false] <;> bv_omega

/-- The comparison of `n` bytes at `a` and `b` by `cmp`: UB unless both ranges are in live
objects, poison if a byte is undefined. -/
def compareBytes (cmp : Unspecified → (n : Nat) → BitVec (8 * n) → BitVec (8 * n) → BitVec 32) :
    Vals [.ptr, .ptr, .bv 64] → EffectM (Vals [.bv 32])
  | .cons a (.cons b (.cons n .nil)) => do
    let .value (a, b, n) := (do return (← a, ← b, (← n).toNat) : PoisonOr _) | throwUB
    let s ← get
    throwUBIf (¬Room s.mem a (8 * n) ∨ ¬Room s.mem b (8 * n))
    let r : IntW 32 :=
      if Fits s.mem a (8 * n) ∧ Fits s.mem b (8 * n) then
        .value (cmp s.mem.unspec n (s.mem.readAt a (8 * n)) (s.mem.readAt b (8 * n)))
      else .poison
    return .cons r .nil

/-- `memcmp(a, b, n)`. -/
def memcmp : Vals [.ptr, .ptr, .bv 64] → EffectM (Vals [.bv 32]) :=
  compareBytes memcmpResult

/-- `bcmp(a, b, n)`: `0` iff the bytes are equal. -/
def bcmp : Vals [.ptr, .ptr, .bv 64] → EffectM (Vals [.bv 32]) :=
  compareBytes bcmpResult

/-- `n` zero bytes at `p`: UB unless into a live object. -/
def storeZeros (p : PoisonOr Pointer) (n : IntW 64) : EffectM Unit := do
  let .value (p, n) := (do return (← p, (← n).toNat) : PoisonOr _) | throwUB
  let s ← get
  throwUBIf (¬Room s.mem p (8 * n))
  set { s with mem := s.mem.storeAt p (0 : BitVec (8 * n)) }

/-- `explicit_bzero(p, n)`: `memset(p, 0, n)`. -/
def explicitBzero : Vals [.ptr, .bv 64] → EffectM (Vals [])
  | .cons p (.cons n .nil) => do
    storeZeros p n
    return .nil

/-- `__explicit_bzero_chk(p, n, size)`, FORTIFY's `explicit_bzero` into an object of `size` bytes
(`-1`: unknown): UB if `n` exceeds it, which aborts. -/
def explicitBzeroChk : Vals [.ptr, .bv 64, .bv 64] → EffectM (Vals [])
  | .cons p (.cons n (.cons size .nil)) => do
    let .value (n', size) := (do return (← n, ← size) : PoisonOr _) | throwUB
    throwUBIf (size ≠ -1 ∧ size < n')
    storeZeros p n
    return .nil

/-- `memset_explicit(p, c, n)`: `memset(p, c, n)`, returning `p`. -/
def memsetExplicit : Vals [.ptr, .bv 32, .bv 64] → EffectM (Vals [.ptr])
  | .cons p (.cons c (.cons n .nil)) => do
    let .value (p', c, n) := (do return (← p, ← c, (← n).toNat) : PoisonOr _) | throwUB
    let s ← get
    throwUBIf (¬Room s.mem p' (8 * n))
    set { s with mem := s.mem.storeAt p' ((c.setWidth 8).replicate n) }
    return .cons p .nil

/-- A call that never returns (`noreturn`: a panic, `abort`): UB. Less defined than LLVM, where
it unwinds or exits, so a proof that never reaches one is sound. -/
def noreturn : Vals ts → EffectM (Vals us) :=
  fun _ => throwUB

/-! ## Runs -/

theorem compareBytes_eq {a b : Pointer} {n : BitVec 64} (ha : Fits s.mem a (8 * n.toNat))
    (hb : Fits s.mem b (8 * n.toNat)) :
    compareBytes cmp (.cons (.value a) (.cons (.value b) (.cons (.value n) .nil))) s =
      .value
        (.cons
            (.value
              (cmp s.mem.unspec n.toNat (s.mem.readAt a (8 * n.toNat))
                (s.mem.readAt b (8 * n.toNat))))
            .nil,
          s) := by
  simp [compareBytes, ha, hb, ha.room, hb.room, throwUBIf, mlir_effect]

theorem memcmp_eq {a b : Pointer} {n : BitVec 64} (ha : Fits s.mem a (8 * n.toNat))
    (hb : Fits s.mem b (8 * n.toNat)) :
    memcmp (.cons (.value a) (.cons (.value b) (.cons (.value n) .nil))) s =
      .value
        (.cons
            (.value
              (memcmpResult s.mem.unspec n.toNat (s.mem.readAt a (8 * n.toNat))
                (s.mem.readAt b (8 * n.toNat))))
            .nil,
          s) :=
  compareBytes_eq ha hb

theorem bcmp_eq {a b : Pointer} {n : BitVec 64} (ha : Fits s.mem a (8 * n.toNat))
    (hb : Fits s.mem b (8 * n.toNat)) :
    bcmp (.cons (.value a) (.cons (.value b) (.cons (.value n) .nil))) s =
      .value
        (.cons
            (.value
              (bcmpResult s.mem.unspec n.toNat (s.mem.readAt a (8 * n.toNat))
                (s.mem.readAt b (8 * n.toNat))))
            .nil,
          s) :=
  compareBytes_eq ha hb

theorem explicitBzero_eq {p : Pointer} {n : BitVec 64} (hp : Room s.mem p (8 * n.toNat)) :
    explicitBzero (.cons (.value p) (.cons (.value n) .nil)) s =
      .value (.nil, { s with mem := s.mem.storeAt p (0 : BitVec (8 * n.toNat)) }) := by
  simp [explicitBzero, storeZeros, hp, throwUBIf, mlir_effect]

theorem explicitBzeroChk_eq {p : Pointer} {n size : BitVec 64} (hp : Room s.mem p (8 * n.toNat))
    (hsize : size = -1 ∨ n ≤ size) :
    explicitBzeroChk (.cons (.value p) (.cons (.value n) (.cons (.value size) .nil))) s =
      .value (.nil, { s with mem := s.mem.storeAt p (0 : BitVec (8 * n.toNat)) }) := by
  rcases hsize with rfl | h
  · simp [explicitBzeroChk, storeZeros, hp, throwUBIf, mlir_effect]
  · have : ¬size < n := by bv_omega
    simp [explicitBzeroChk, storeZeros, hp, this, throwUBIf, mlir_effect]

end

end MLIR.Operation
