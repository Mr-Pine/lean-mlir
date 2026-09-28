module

public import SSA.Projects.RIR.Ty
public import SSA.Projects.RIR.SimpSets
public meta import Lean.Meta.Tactic.Simp

namespace LeanMLIR.RIR

@[expose] public section

inductive Vals : List Ty → Type
  | nil : Vals []
  | cons (v : ⟦t⟧) (vs : Vals ts) : Vals (t :: ts)

/-- The `i`-th value. -/
def Vals.get : Vals ts → (i : Fin ts.length) → ⟦ts[i]⟧
  | .cons v _, ⟨0, _⟩ => v
  | .cons _ vs, ⟨k + 1, h⟩ => vs.get ⟨k, Nat.lt_of_succ_lt_succ h⟩

open Lean Meta in
/-- Reduce `vs.get i` when `vs` is a literal `Vals.cons …` and `i` a literal index. -/
dsimproc [simp, mlir_env]reduceValsGet (Vals.get _ _) := fun e => do
  let_expr Vals.get _ vs _ := e | return .continue
  unless vs.isAppOf ``Vals.cons do
    return .continue
  let e' ← withTransparency .default (whnf e)
  return if e' == e then .continue else .visit e'

end

end LeanMLIR.RIR
