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
def denote : Ty → Type
  | bv w => PoisonOr (BitVec w)
  | ptr => PoisonOr Pointer

end

public section

def width : Ty → Nat
  | bv w => w
  | ptr => 64

def poisoned : (t : Ty) → t.denote
  | bv _ => .poison
  | ptr => .poison

@[simp]
theorem width_bv : (bv w).width = w := by rfl

@[simp]
theorem poisoned_bv : poisoned (bv w) = (.poison : PoisonOr (BitVec w)) := by rfl

@[simp]
theorem poisoned_ptr : poisoned ptr = (.poison : PoisonOr Pointer) := by rfl

end

end LeanMLIR.RIR.Ty
