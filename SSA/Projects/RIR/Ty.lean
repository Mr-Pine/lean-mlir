module

public import SSA.Projects.RIR.Poison
public import SSA.Projects.RIR.Memory.Pointer
public import Lean.ToExpr

namespace LeanMLIR.RIR

public inductive Ty
  | bv (w : Nat)
  | ptr

namespace Ty

@[expose] public section

deriving instance DecidableEq, Lean.ToExpr, Repr for Ty

@[reducible]
def denote τ :=
  PoisonOr
    (match τ with
    | bv w => BitVec w
    | ptr => Pointer)

/-- `⟦t⟧` is the `Type` of values of (MLIR) type `t` --/
notation "⟦" t "⟧" => LeanMLIR.RIR.Ty.denote t

end

public section

def width : Ty → Nat
  | bv w => w
  | ptr => 64

def poisoned : (t : Ty) → ⟦t⟧ := fun _ => PoisonOr.poison

@[simp]
theorem width_bv : (bv w).width = w := by rfl

@[simp]
theorem poisoned_bv : poisoned (bv w) = (.poison : PoisonOr (BitVec w)) := by rfl

@[simp]
theorem poisoned_ptr : poisoned ptr = (.poison : PoisonOr Pointer) := by rfl

end

end LeanMLIR.RIR.Ty
