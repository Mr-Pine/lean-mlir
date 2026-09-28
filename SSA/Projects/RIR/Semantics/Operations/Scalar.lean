module

public import SSA.Projects.RIR.SimpSets
public import SSA.Projects.RIR.Ty
public import SSA.Projects.RIR.IntPred
public import SSA.Projects.RIR.OverflowFlags

namespace LeanMLIR.RIR.Operation

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
  if isExact then
    if val.extractLsb' 0 amount != 0 then
      .poison
  return (val.ushiftRight amount)

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
  return BitVec.ofBool result

end BVBinOp

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

end Cast

@[mlir_operation]
def select {τ : Ty} (cond : IntW 1) (x y : ⟦τ⟧) : ⟦τ⟧ := do
  let cond ← cond
  if cond == 1#1 then
    x
  else
    y

@[simp, mlir_operation]
def constant {w} (x : BitVec w) : IntW w :=
  PoisonOr.value x

end

end LeanMLIR.RIR.Operation
