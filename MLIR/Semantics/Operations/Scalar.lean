module

public import MLIR.SimpSets
public import MLIR.Ty
public import MLIR.IntPred
public import MLIR.OverflowFlags

namespace MLIR.Operation

@[expose] public section

/- Enables `simp only [mlir_operation]` to also reduce the do notation if the inputs are .value -/
attribute [mlir_operation] PoisonOr.value_bind PoisonOr.poison_bind PoisonOr.bind_poison
  PoisonOr.pure_def

abbrev IntW w :=
  (Ty.bv w).denote

section BVBinOp

@[mlir_operation]
def and {w : Nat} (x y : IntW w) : IntW w := do
  let a ← x
  let b ← y
  return (a &&& b)

/-- `disjoint`: poison if `x` and `y` share a set bit. -/
@[mlir_operation]
def or (disjoint : Bool) {w : Nat} (x y : IntW w) : IntW w := do
  let a ← x
  let b ← y
  if disjoint ∧ a &&& b ≠ 0 then
    .poison
  return (a ||| b)

@[mlir_operation]
def xor {w : Nat} (x y : IntW w) : IntW w := do
  let a ← x
  let b ← y
  return (a ^^^ b)

@[mlir_operation]
def add (flags : OverflowFlags) {w : Nat} (x y : IntW w) : IntW w := do
  let a : BitVec w ← x
  let b ← y
  if flags.nsw ∧ a.saddOverflow b then
    .poison
  if flags.nuw ∧ a.uaddOverflow b then
    .poison
  return (a + b)

@[mlir_operation]
def sub (flags : OverflowFlags) {w : Nat} (x y : IntW w) : IntW w := do
  let a : BitVec w ← x
  let b ← y
  if flags.nsw ∧ a.ssubOverflow b then
    .poison
  if flags.nuw ∧ a.usubOverflow b then
    .poison
  return (a - b)

@[mlir_operation]
def mul (flags : OverflowFlags) {w : Nat} (x y : IntW w) : IntW w := do
  let a : BitVec w ← x
  let b ← y
  if flags.nsw ∧ a.smulOverflow b then
    .poison
  if flags.nuw ∧ a.umulOverflow b then
    .poison
  return (a * b)

/-- Poison for a shift by `w` or more; `nuw`/`nsw`: also when a shifted-out bit is set / differs
from the result's sign. -/
@[mlir_operation]
def shl (flags : OverflowFlags) {w : Nat} (x amount : IntW w) : IntW w := do
  let a : BitVec w ← x
  let s := (← amount).toNat
  if s ≥ w then
    .poison
  let r := a <<< s
  if flags.nuw ∧ r >>> s ≠ a then
    .poison
  if flags.nsw ∧ r.sshiftRight s ≠ a then
    .poison
  return r

@[mlir_operation]
def lshr (isExact : Bool) {w : Nat} (val amount : IntW w) : IntW w := do
  let val : BitVec w ← val
  let amount := (← amount).toNat
  if amount ≥ w then
    .poison
  if isExact then
    if val.extractLsb' 0 amount != 0 then
      .poison
  return (val.ushiftRight amount)

@[mlir_operation]
def ashr (isExact : Bool) {w : Nat} (val amount : IntW w) : IntW w := do
  let val : BitVec w ← val
  let amount := (← amount).toNat
  if amount ≥ w then
    .poison
  if isExact then
    if val.extractLsb' 0 amount != 0 then
      .poison
  return (val.sshiftRight amount)

@[mlir_operation]
def smin {w : Nat} (x y : IntW w) : IntW w := do
  let a ← x
  let b ← y
  let result := if a.slt b then a else b
  return result

@[mlir_operation]
def icmp {w : Nat} (pred : IntPred) (x y : IntW w) : IntW 1 := do
  let a ← x
  let b ← y
  let result :=
    match pred with
    | .eq => a == b
    | .ne => a != b
    | .slt => a.slt b
    | .sle => a.sle b
    | .sgt => b.slt a
    | .sge => b.sle a
    | .ult => a.ult b
    | .ule => a.ule b
    | .ugt => b.ult a
    | .uge => b.ule a
  return BitVec.ofBool result

end BVBinOp

section Intrinsics

/-- `llvm.intr.fshl`: the high `w` bits of `x ++ y` shifted left by `z mod w`. -/
@[mlir_operation]
def fshl {w : Nat} (x y z : IntW w) : IntW w := do
  let a ← x
  let b ← y
  let c ← z
  return ((a ++ b) <<< (c.toNat % w)).extractLsb' w w

/-- `llvm.intr.fshr`: the low `w` bits of `x ++ y` shifted right by `z mod w`. -/
@[mlir_operation]
def fshr {w : Nat} (x y z : IntW w) : IntW w := do
  let a ← x
  let b ← y
  let c ← z
  return ((a ++ b) >>> (c.toNat % w)).setWidth w

/-- `llvm.intr.bswap`: `x`'s bytes in reverse order (`w` a multiple of 8). -/
@[mlir_operation]
def bswap {w : Nat} (x : IntW w) : IntW w := do
  let a ← x
  return (List.range (w / 8)).foldl
      (fun acc i => acc ||| ((a >>> (8 * i)) &&& 0xFF) <<< (w - 8 * (i + 1))) 0

end Intrinsics

section Cast

/-- The low `w'` bits; `nuw`/`nsw`: poison unless they zero/sign-extend back to `x`. -/
@[mlir_operation]
def trunc (flags : OverflowFlags) {w w' : Nat} (x : IntW w) : IntW w' := do
  let a : BitVec w ← x
  let r := a.setWidth w'
  if flags.nuw ∧ r.setWidth w ≠ a then
    .poison
  if flags.nsw ∧ r.signExtend w ≠ a then
    .poison
  return r

/-- Zero-extended to `w'` bits; `nneg`: poison if `x` is negative. -/
@[mlir_operation]
def zext (nneg : Bool) {w w' : Nat} (x : IntW w) : IntW w' := do
  let a : BitVec w ← x
  if nneg ∧ a.msb then
    .poison
  return a.setWidth w'

/-- Sign-extended to `w'` bits -/
@[mlir_operation]
def sext {w w' : Nat} (x : IntW w) : IntW w' := do
  let a : BitVec w ← x
  return a.signExtend w'

/-- The same bits at a type of the same width. Poison if any lane is: coarser than LLVM, which
keeps the other lanes, but sound, as poison refines to any value. -/
@[mlir_operation]
def bitcast {t t' : Ty} (h : t.width = t'.width) (x : ⟦t⟧) : ⟦t'⟧ :=
  match t.flatten x with
  | .value b => t'.unflatten (b.cast h)
  | .poison => t'.poisoned

end Cast

@[mlir_operation]
def select {τ : Ty} (cond : IntW 1) (x y : ⟦τ⟧) : ⟦τ⟧ :=
  match cond with
  | .poison => τ.poisoned
  | .value cond => if cond == 1#1 then x else y

@[simp, mlir_operation]
def constant {w} (x : BitVec w) : IntW w :=
  PoisonOr.value x

end

end MLIR.Operation
