module

public import SSA.Projects.RIR.Semantics.Func
public meta import Lean.Elab.Tactic

namespace LeanMLIR.RIR.Tactic

open Lean Elab Tactic Meta

public meta section

def getGoalType := do
  let g ← getMainGoal
  let ty ← instantiateMVars (← g.getType)
  return (g, ty)

abbrev ParseM (E T : Type) [ToMessageData E] :=
  ExceptT E MetaM T

@[inline]
private def fail (e : Err) [ToMessageData Err] : ParseM Err α :=
  throwThe Err e

section FuncRunGoal

structure FuncRunGoal where
  app : Expr
  func : Expr
  env : Expr
  state : Expr

inductive FuncRunGoalError where
  | noRunApp (goal : Expr)
  | notEnoughArgs (runApp : Expr) (got expected : Nat)

instance : ToMessageData FuncRunGoalError where
  toMessageData
    | .noRunApp goal => m!"Did not find application of {``Func.run} in the goal {indentExpr goal}"
    | .notEnoughArgs runApp got expected =>
      m!"Expected {expected} args, got {got} in {indentExpr runApp}"

def getFuncRunGoal? (goal : Expr) : ParseM FuncRunGoalError FuncRunGoal := do
  let some runApp := goal.find? (·.isAppOf ``Func.run)
    | fail (.noRunApp goal)
  let args := runApp.getAppArgs
  if args.size < 3 then
    fail (.notEnoughArgs runApp args.size 3)
  return ⟨runApp, args[0]!, args[1]!, args[2]!⟩

def getFuncRunGoal (goal : Expr) : MetaM FuncRunGoal := do
  match ← getFuncRunGoal? goal with
  | .ok g =>
    return g
  | .error e =>
    throwError "{e}"

end FuncRunGoal

section FuncRunFromGoal

structure FuncRunFromGoal where
  app : Expr
  func : Expr
  blockIndex : Expr
  env : Expr
  state : Expr

inductive FuncRunFromGoalError where
  | noRunFromApp (goal : Expr)
  | notEnoughArgs (runApp : Expr) (got expected : Nat)

instance : ToMessageData FuncRunFromGoalError where
  toMessageData
    | .noRunFromApp goal =>
      m!"Did not find application of {``Func.runFrom} in the goal {indentExpr goal}"
    | .notEnoughArgs runApp got expected =>
      m!"Expected {expected} args, got {got} in {indentExpr runApp}"

def getFuncRunFromGoal? (goal : Expr) : ParseM FuncRunFromGoalError FuncRunFromGoal := do
  let some runApp := goal.find? (·.isAppOf ``Func.runFrom)
    | fail (.noRunFromApp goal)
  let args := runApp.getAppArgs
  if args.size < 4 then
    fail (.notEnoughArgs runApp args.size 4)
  return ⟨runApp, args[0]!, args[2]!, args[1]!, args[3]!⟩

def getFuncRunFromGoal (goal : Expr) : MetaM FuncRunFromGoal := do
  match ← getFuncRunFromGoal? goal with
  | .ok g =>
    return g
  | .error e =>
    throwError "{e}"

end FuncRunFromGoal

end

end LeanMLIR.RIR.Tactic
