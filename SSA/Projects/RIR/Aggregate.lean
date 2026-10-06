module

public import SSA.Projects.RIR.Ty

namespace LeanMLIR.RIR

@[expose] public section

/-- A statically checked field of a heterogeneous LLVM structure. -/
inductive FieldIndex : List Ty → Ty → Type
  | head : FieldIndex (t :: ts) t
  | tail (index : FieldIndex ts t) : FieldIndex (s :: ts) t

namespace FieldIndex

def get : {fs : List Ty} → FieldIndex fs t → Ty.denoteFields fs → ⟦t⟧
  | [_], .head, v => v
  | _ :: _ :: _, .head, v => v.1
  | _ :: [], .tail i, _ => nomatch i
  | _ :: _ :: _, .tail i, v => i.get v.2

def set : {fs : List Ty} → FieldIndex fs t → Ty.denoteFields fs → ⟦t⟧ → Ty.denoteFields fs
  | [_], .head, _, x => x
  | _ :: _ :: _, .head, v, x => (x, v.2)
  | _ :: [], .tail i, _, _ => nomatch i
  | _ :: _ :: _, .tail i, v, x => (v.1, i.set v.2 x)

@[simp]
theorem get_set (i : FieldIndex fs t) (v : Ty.denoteFields fs) (x : ⟦t⟧) :
    i.get (i.set v x) = x := by
  induction i with
  | @head t ts => cases ts <;> rfl
  | @tail ts t s i ih =>
    cases ts with
    | nil => cases i
    | cons u us => exact ih v.2 x

end FieldIndex

/-- A checked nested aggregate position. Vectors are leaves: LLVM `extractvalue`
and `insertvalue` index only arrays and structures. -/
inductive AggregatePath : Ty → Ty → Type
  | here : AggregatePath t t
  | array (index : Fin n) (rest : AggregatePath s t) : AggregatePath (.array n s) t
  | field (index : FieldIndex fs s) (rest : AggregatePath s t) : AggregatePath (.struct fs) t

namespace AggregatePath

/-- Extraction preserves poison only in the selected component. -/
def get : AggregatePath s t → ⟦s⟧ → ⟦t⟧
  | .here, v => v
  | .array i rest, v => rest.get v[i]
  | .field i rest, v => rest.get (i.get v)

/-- Insertion overwrites the selected component, even if it was poison. -/
def set : AggregatePath s t → ⟦s⟧ → ⟦t⟧ → ⟦s⟧
  | .here, _, x => x
  | .array i rest, v, x => v.set i (rest.set v[i] x)
  | .field i rest, v, x => i.set v (rest.set (i.get v) x)

@[simp]
theorem get_set (path : AggregatePath s t) (v : ⟦s⟧) (x : ⟦t⟧) :
    path.get (path.set v x) = x := by
  induction path with
  | here => rfl
  | array i rest ih => simp [get, set, ih]
  | field i rest ih => simp [get, set, ih]

end AggregatePath
end
end LeanMLIR.RIR
