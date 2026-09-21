module

public import SSA.Projects.RIR.SimpSets
public import SSA.Projects.RIR.Ty
public import SSA.Projects.RIR.IntPred

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

end LeanMLIR.RIR.Operation
