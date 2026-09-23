module

public import SSA.Projects.RIR.Semantics.Func
public import SSA.Projects.RIR.Run.BasicBlock
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

section RunBodyFromGoal

structure RunBodyFrom where
  app : Expr
  block : Expr
  env : Expr
  idx : Expr
  state : Expr

inductive RunBodyFromError where
  | noRunBodyFromApp (goal : Expr)
  | notEnoughArgs (runApp : Expr) (got expected : Nat)

instance : ToMessageData RunBodyFromError where
  toMessageData
    | .noRunBodyFromApp goal =>
      m!"Did not find application of {``BasicBlock.runBodyFrom} in the goal {indentExpr goal}"
    | .notEnoughArgs runApp got expected =>
      m!"Expected {expected} args, got {got} in {indentExpr runApp}"

def getRunBodyFrom? (goal : Expr) : ParseM RunBodyFromError RunBodyFrom := do
  let some runApp := goal.find? (·.isAppOf ``BasicBlock.runBodyFrom)
    | fail (.noRunBodyFromApp goal)
  let args := runApp.getAppArgs
  if args.size < 8 then
    fail (.notEnoughArgs runApp args.size 8)
  return ⟨runApp, args[4]!, args[5]!, args[6]!, args[7]!⟩

def getRunBodyFrom (goal : Expr) : MetaM RunBodyFrom := do
  match ← getRunBodyFrom? goal with
  | .ok g =>
    return g
  | .error e =>
    throwError "{e}"

end RunBodyFromGoal

@[inline]
def _root_.Lean.Expr.app5? (e : Expr) (fName : Name) : Option (Expr × Expr × Expr × Expr × Expr) :=
  if e.isAppOfArity fName 5 then
    some
      (e.appFn!.appFn!.appFn!.appArg!.appArg!, e.appFn!.appFn!.appFn!.appArg!,
        e.appFn!.appFn!.appArg!, e.appFn!.appArg!, e.appArg!)
  else none

section RunBodyFromGoal

structure EnvWrite where
  base : Expr
  dst : Expr
  value : Expr

def getEnvWrite (e : Expr) : MetaM EnvWrite := do
  let some (_, _, base, dst, value) :=
    e.app5? ``Env.write | throwError m!"Env {e} is not a {``Env.write}"
  return ⟨base, dst, value⟩

end RunBodyFromGoal

end

end LeanMLIR.RIR.Tactic
