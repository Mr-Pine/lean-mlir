module

public import MLIR.Semantics.Func
public meta import Lean.Meta.Tactic.Simp.BuiltinSimprocs.BitVec

namespace MLIR

public section

theorem ofBool_eq_one_iff (b : Bool) : BitVec.ofBool b = 1#1 ↔ b = true := by cases b <;> decide

open Lean Meta in
/-- A flag's overflow test on literals (`(0#64).saddOverflow 1#64`), evaluated: an `nsw`/`nuw`
operation on constants is no `if` left to a lemma. -/
meta def overflowLit? (e : Expr) : SimpM (Option Bool) := do
  let some f := e.getAppFn.constName? | return none
  let fs : List (Name × (∀ {w}, BitVec w → BitVec w → Bool)) :=
    [(``BitVec.uaddOverflow, BitVec.uaddOverflow), (``BitVec.saddOverflow, BitVec.saddOverflow),
      (``BitVec.usubOverflow, BitVec.usubOverflow), (``BitVec.ssubOverflow, BitVec.ssubOverflow),
      (``BitVec.umulOverflow, BitVec.umulOverflow), (``BitVec.smulOverflow, BitVec.smulOverflow)]
  let some (_, op) := fs.find? (·.1 == f) | return none
  unless e.getAppNumArgs == 3 do
    return none
  let some ⟨w, x⟩ ← getBitVecValue? e.appFn!.appArg! | return none
  let some ⟨w', y⟩ ← getBitVecValue? e.appArg! | return none
  if h : w = w' then
    return some (op (h ▸ x) y)
  return none

open Lean Meta in
/-- `uaddOverflow` on literals. -/
dsimproc [simp] reduceUaddOverflowLit (BitVec.uaddOverflow _ _) := fun e => do
  let some b ← overflowLit? e | return .continue
  return .done (toExpr b)

open Lean Meta in
/-- `saddOverflow` on literals. -/
dsimproc [simp] reduceSaddOverflowLit (BitVec.saddOverflow _ _) := fun e => do
  let some b ← overflowLit? e | return .continue
  return .done (toExpr b)

open Lean Meta in
/-- `usubOverflow` on literals. -/
dsimproc [simp] reduceUsubOverflowLit (BitVec.usubOverflow _ _) := fun e => do
  let some b ← overflowLit? e | return .continue
  return .done (toExpr b)

open Lean Meta in
/-- `ssubOverflow` on literals. -/
dsimproc [simp] reduceSsubOverflowLit (BitVec.ssubOverflow _ _) := fun e => do
  let some b ← overflowLit? e | return .continue
  return .done (toExpr b)

open Lean Meta in
/-- `umulOverflow` on literals. -/
dsimproc [simp] reduceUmulOverflowLit (BitVec.umulOverflow _ _) := fun e => do
  let some b ← overflowLit? e | return .continue
  return .done (toExpr b)

open Lean Meta in
/-- `smulOverflow` on literals. -/
dsimproc [simp] reduceSmulOverflowLit (BitVec.smulOverflow _ _) := fun e => do
  let some b ← overflowLit? e | return .continue
  return .done (toExpr b)

end

end MLIR
