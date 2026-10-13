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

/-- Exit and instructions in `block` from `pos` on. -/
def blockParts (block pos : Expr) : MetaM (Array Expr) := do
  let mut parts := #[← whnfD (← mkAppM ``BasicBlock.exit #[block])] -- Check all used in exit
  let mut rest :=
    ←
      whnfD
          (←
            mkAppM ``List.drop
                #[pos, (← mkAppM ``BasicBlock.body #[block])]) -- Ignore previous instructions
  while rest.isAppOfArity ``List.cons 3 do
    parts := parts.push rest.appFn!.appArg! -- `x` of `List.cons α x xs` (`x::xs`)
    rest ← whnfD rest.appArg! -- `xs`
  return parts

/-- A closed block's instructions: each step takes the one at its position, where unfolding
`body[pos]` walks the list to it. -/
initialize blockInstrsCache : IO.Ref (Std.HashMap Expr (Array Expr)) ← IO.mkRef {}

/-- `block`'s instructions, when its body unfolds to a list literal; a closed block's from
`blockInstrsCache`. -/
def blockInstrs? (block : Expr) : MetaM (Option (Array Expr)) := do
  let block ← instantiateMVars block
  if block.hasMVar then
    return none
  if let some instrs := (← blockInstrsCache.get)[block]? then
    return instrs
  let mut instrs := #[]
  let mut rest ← whnfD (← mkAppM ``BasicBlock.body #[block])
  while rest.isAppOfArity ``List.cons 3 do
    instrs := instrs.push rest.appFn!.appArg!
    rest ← whnfD rest.appArg!
  unless rest.isAppOfArity ``List.nil 1 do
    return none
  unless block.hasFVar do
    blockInstrsCache.modify (·.insert block instrs)
  return instrs

/-- Instruction `pos` of a closed `block` at a literal `pos`, from `blockInstrsCache`. -/
def blockInstr? (block pos : Expr) : MetaM (Option Expr) := do
  let block ← instantiateMVars block
  if block.hasFVar then
    return none
  let pos ← instantiateMVars pos
  let some i := pos.nat? <|> pos.rawNatLit? | return none
  return (← blockInstrs? block).bind (·[i]?)

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

/-- The body facts `block.body.drop idx = xs` in context, the hidden ones a concrete block's steps
carry included. -/
def bodyFactEqs : MetaM (Array LocalEq) := do
  (← getLCtx).foldlM (init := #[]) fun acc d => do
      if d.isAuxDecl then
        return acc
      let type := (← instantiateMVars d.type).consumeMData
      let some (_, lhs, rhs) := type.eq? | return acc
      unless (bodyDrop? lhs).isSome do
        return acc
      return acc.push { decl := d, type, lhs, rhs }

/-- A body fact `h : block.body.drop idx = x :: xs`. -/
structure BodyFact where
  /-- `h`, typed with the `cons` exposed. -/
  proof : Expr
  instr : Expr
  rest : Expr
  /-- Whether `h` is a concrete block's, hidden: the steps' own. -/
  hidden : Bool

/-- A local body fact `block.body.drop idx = x :: xs`. -/
def bodyFact? (block idx : Expr) : MetaM (Option BodyFact) := do
  for e in ← bodyFactEqs do
    let some (n, b) := bodyDrop? e.lhs | continue
    unless ← isDefEq b block <&&> isDefEq n idx do
      continue
    let rhs ← whnfD e.rhs
    let_expr List.cons _ x xs := rhs | continue
    return some
        { proof := mkExpectedPropHint e.decl.toExpr (← mkEq e.lhs rhs), instr := x, rest := xs,
          hidden := !(← instantiateMVars b).hasFVar }
  return none

/-- A local body fact `block.body.drop idx = []`, at the body's end. -/
def bodyEndFact? (block idx : Expr) : MetaM (Option Expr) := do
  for e in ← bodyFactEqs do
    let some (n, b) := bodyDrop? e.lhs | continue
    unless ← isDefEq b block <&&> isDefEq n idx do
      continue
    if (← whnfR e.rhs).isAppOf ``List.nil then
      return some (mkExpectedPropHint e.decl.toExpr (← mkEq e.lhs (← whnfR e.rhs)))
  return none

/-- `lhs = rhs` for a body `lhs := block.body.drop idx` that does not reduce, from a local body fact
`block.body.drop idx = xs` whose `xs` unifies with `rhs` (a pattern's `pat ++ ?rest`). -/
def bodyFactAs? (lhs rhs : Expr) : MetaM (Option Expr) := do
  let some (idx, block) := bodyDrop? lhs | return none
  for e in ← bodyFactEqs do
    let some (n, b) := bodyDrop? e.lhs | continue
    unless ← isDefEq b block <&&> isDefEq n idx do
      continue
    if ← withDefault (isDefEq e.rhs rhs) then
      return some (mkExpectedPropHint e.decl.toExpr (← mkEq lhs (← instantiateMVars rhs)))
  return none

/-- A body fact `block.body.drop i = xs` for a closed `block` at a literal `i`, `xs` its
instructions from `i` on as a literal: its type and proof. The kernel evaluates the `drop` once;
the steps carry the fact on, each in constant time. -/
def literalBodyFact? (block idx : Expr) : MetaM (Option (Expr × Expr)) := do
  let some instrs ← blockInstrs? block | return none
  let idx ← instantiateMVars idx
  let some i := idx.nat? <|> idx.rawNatLit? | return none
  let body ← mkAppM ``BasicBlock.body #[block]
  let_expr List α := ← whnfR (← inferType body) | return none
  let lhs ← mkAppM ``List.drop #[mkNatLit i, body]
  let ty ← mkEq lhs (← mkListLit α (instrs.toList.drop i))
  return some (ty, mkExpectedPropHint (← mkEqRefl lhs) ty)

/-- `g` with the local `h` hidden (an implementation detail): a concrete block's body fact, whose
type spells out the instructions left. -/
def hideLocal (g : MVarId) (h : FVarId) : MetaM MVarId :=
  g.withContext do
    let lctx := (← getLCtx).setKind h .implDetail
    let g' ←
      mkFreshExprMVarAt lctx (← getLocalInstances) (← g.getType) .syntheticOpaque (← g.getTag)
    g.assign g'
    return g'.mvarId!

/-- Assert a body fact `h : ty` in `g`, hidden if `hidden`. -/
def assertBodyFact (g : MVarId) (ty pf : Expr) (hidden : Bool) : MetaM MVarId := do
  let (h, g) ← (← g.assert `hbody ty pf).intro1P
  if hidden then hideLocal g h else pure g

/-- `block.body.drop idx`, reduced to its first `cons`, from a body fact or by unfolding. -/
def bodyFrom (block idx : Expr) : MetaM Expr := do
  if let some f ← bodyFact? block idx then
    return ← mkAppM ``List.cons #[f.instr, f.rest]
  if (← bodyEndFact? block idx).isSome then
    return ← mkAppOptM ``List.nil #[(← inferType (← mkAppM ``BasicBlock.body #[block])).appArg!]
  if let some (ty, _) ← literalBodyFact? block idx then
    if let some (_, _, rhs) := ty.eq? then
      return rhs
  whnfD (← mkAppM ``List.drop #[idx, ← mkAppM ``BasicBlock.body #[block]])

end RunBodyFromGoal

end

end MLIR.Tactic
