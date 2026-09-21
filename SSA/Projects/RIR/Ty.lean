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

@[expose] def width : Ty → Nat
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

public section FlattenUnflatten

def flatten : (t : Ty) → ⟦t⟧ → PoisonOr (BitVec t.width)
| bv _, x => x
| ptr, _ => .poison

def unflatten : (t : Ty) → BitVec t.width → ⟦t⟧
| bv _, x => .value x
| ptr, _ => .poison

@[simp] theorem flatten_bv (x : ⟦bv w⟧) : flatten (bv w) x = x := by rfl
@[simp] theorem unflatten_bv (b : BitVec w) : unflatten (bv w) b = .value b := by rfl
@[simp] theorem flatten_ptr (x : ⟦ptr⟧) : flatten ptr x = .poison := by rfl

theorem unflatten_flatten {t : Ty} {v : ⟦t⟧} {b : BitVec t.width}
    (h : flatten t v = .value b) : unflatten t b = v := by
  cases t with
  | bv w => cases v; simp_all [flatten, unflatten]; rfl
  | ptr => exact absurd h (PoisonOr.poison_ne_value b)

end FlattenUnflatten

end LeanMLIR.RIR.Ty
