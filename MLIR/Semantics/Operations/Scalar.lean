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

end MLIR.Operation
