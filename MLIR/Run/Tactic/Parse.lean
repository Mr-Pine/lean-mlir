module

public import MLIR.Semantics.Func
public import MLIR.Run.BasicBlock
public meta import Lean.Elab.Tactic

namespace MLIR.Tactic

open Lean Elab Tactic Meta

public meta section

def getGoalType := do
  let g ← getMainGoal
  let ty ← instantiateMVars (← g.getType)
  return (g, ty)

/-- The first application of `fn` in `goal`, with its arguments, when it has at least `n`. -/
def appArgs? (goal : Expr) (fn : Name) (n : Nat) : Option (Expr × Array Expr) := do
  let app ← goal.find? (·.isAppOf fn)
  guard (app.getAppNumArgs ≥ n)
  return (app, app.getAppArgs)

private def noApp (fn : Name) (goal : Expr) : MetaM α :=
  throwError "no application of `{fn}` in the goal{indentExpr goal}"

/-- A goal's `Func.runFrom f env k state`. -/
structure FuncRunFromGoal where
  app : Expr
  env : Expr
  state : Expr

def getFuncRunFromGoal (goal : Expr) : MetaM FuncRunFromGoal := do
  let some (app, args) := appArgs? goal ``Func.runFrom 4 | noApp ``Func.runFrom goal
  return ⟨app, args[1]!, args[3]!⟩

/-- A goal's `block.runBodyFrom env idx state`. -/
structure RunBodyFrom where
  block : Expr
  env : Expr
  idx : Expr
  state : Expr

def getRunBodyFrom? (goal : Expr) : Option RunBodyFrom := do
  let (_, args) ← appArgs? goal ``BasicBlock.runBodyFrom 8
  return ⟨args[4]!, args[5]!, args[6]!, args[7]!⟩

def getRunBodyFrom (goal : Expr) : MetaM RunBodyFrom := do
  let some r := getRunBodyFrom? goal | noApp ``BasicBlock.runBodyFrom goal
  return r

section RunBodyFromGoal

/-- A local equation `decl : lhs = rhs`. -/
structure LocalEq where
  decl : LocalDecl
  /-- The equation, instantiated, without a named value's tag. -/
  type : Expr
  lhs : Expr
  rhs : Expr

/-- The context's equations. -/
def localEqs : MetaM (Array LocalEq) := do
  (← getLCtx).foldlM (init := #[]) fun acc d => do
      if d.isImplementationDetail then
        return acc
      let type := (← instantiateMVars d.type).consumeMData
      let some (_, lhs, rhs) := type.eq? | return acc
      return acc.push { decl := d, type, lhs, rhs }

/-- `(n, b)` for a body fact's left side `b.body.drop n`. -/
def bodyDrop? (lhs : Expr) : Option (Expr × Expr) := do
  let_expr List.drop _ n body := lhs | none
  let_expr BasicBlock.body _ _ _ _ b := body | none
  return (n, b)

/-- A local `h : block.body.drop idx = x :: xs`, for a `block` whose body does not reduce: `h`
(typed with the `cons` exposed), `x` and `xs`. -/
def bodyFact? (block idx : Expr) : MetaM (Option (Expr × Expr × Expr)) := do
  for e in ← localEqs do
    let some (n, b) := bodyDrop? e.lhs | continue
    unless ← isDefEq b block <&&> isDefEq n idx do
      continue
    let rhs ← whnfD e.rhs
    let_expr List.cons _ x xs := rhs | continue
    return some (mkExpectedPropHint e.decl.toExpr (← mkEq e.lhs rhs), x, xs)
  return none

/-- `block.body.drop idx`, reduced to its first `cons`, by unfolding or from a body fact. -/
def bodyFrom (block idx : Expr) : MetaM Expr := do
  let rest ← whnfD (← mkAppM ``List.drop #[idx, ← mkAppM ``BasicBlock.body #[block]])
  if rest.isAppOfArity ``List.cons 3 || rest.isAppOfArity ``List.nil 1 then
    return rest
  let some (_, x, xs) ← bodyFact? block idx | return rest
  mkAppM ``List.cons #[x, xs]

end RunBodyFromGoal

end

end MLIR.Tactic
