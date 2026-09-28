module

public import MLIR.Semantics.Func
public import MLIR.Run.Tactic.Parse
public import MLIR.Run.Tactic.Memory
public import MLIR.Run.Tactic.Util
public meta import Lean.Elab.Tactic

namespace MLIR.Tactic

open Lean Elab Tactic Meta

public meta section

section SealEnv

def sealEnvAt (env : Expr) : TacticM Unit :=
  withMainContext do
    let g ← getMainGoal
    if env.isFVar then
      return
    -- the chain's root: a jump writes several parameters
    let mut E := (← getEnvWrite env).base
    while E.isAppOfArity ``Env.write 5 do
      E := E.getArg! 2
    -- without `hE`, `E` is a root (a loop's env, or a continuation's): it stays
    let hE? ← findEqWithLhs? E m!"of the form `{E} = _`"
    let hEargs? ←
      findEqWithLhs? (← mkAppM ``Env.args #[E]) m!"of the form `{(← mkAppM ``Env.args #[E])} = _"
    let abstractWrite := Expr.lam `e (← inferType E) (← kabstract env E) .default
    let (E₀chain, hEpf) ←
      match hE? with
      | some hE =>
        do
          let some (_, _, c) :=
            (← instantiateMVars (← hE.getType)).eq? | throwError "expected an equation"
          pure (c, ← mkCongrArg abstractWrite (mkFVar hE))
      | none =>
        pure (E, ← mkEqRefl env)
    let stmtEq := (mkEq · (abstractWrite.beta #[E₀chain]))
    let mut facts := #[⟨`hE, stmtEq, hEpf⟩]
    if let some hEargs := hEargs? then
      let some (_, _, args) :=
        (← instantiateMVars (← hEargs.getType)).eq? | throwError "expected an equation"
      let stmtArgs (e) : MetaM _ := do
        mkEq (← mkAppM ``Env.args #[e]) args
      facts := facts.push ⟨`hArgs, stmtArgs, mkExpectedPropHint (mkFVar hEargs) (← stmtArgs env)⟩
    let (_, g) ←
      g.withContext do
          generalizeOpaque g (hyps := #[]) env `E facts
    let mut g := g
    if let some hEargs := hEargs? then
      g ← g.clear hEargs
    if let some hE := hE? then
      g ← g.clear hE
      g ← g.clear E.fvarId!
    replaceMainGoal [g]

def sealEnv : TacticM Unit := do
  let (_, goal) ← getGoalType
  let runBodyFrom ← getRunBodyFrom goal
  sealEnvAt runBodyFrom.env

elab "seal_env" : tactic => sealEnv

end SealEnv

section ResolveReads

/-- Reduce `args i` access by unfolding -/
def reduceArgsApp : Simp.DSimproc := fun app => do
  let index := app.appArg!
  let some finBound := (← whnf (← inferType index)).app1? ``Fin | return .continue
  let some literal ← finNLit? index | return .continue
  let inBounds ← mkDecideProof (← mkAppM ``LT.lt #[mkNatLit literal, finBound])
  let litIndex ← mkAppOptM ``Fin.mk #[finBound, mkNatLit literal, inBounds]
  let some unfolded ← withDefault (unfoldDefinition? (mkApp app.appFn! litIndex)) | return .continue
  let reduced ← whnfCore unfolded
  return if reduced == app then .continue else .done reduced

/-- For a fact `h : _.args = argsFn`, this keys `reduceArgsApp` on applications of `argsFn` -/
def argsSimprocs (fact : FVarId) : MetaM Simp.Simprocs := do
  let simprocs ← Simp.getSimprocs
  let some (_, _, argsFn) := (← instantiateMVars (← fact.getType)).eq? | return simprocs -- Find
  let .forallE _ indexType _ _ := ← whnf (← inferType argsFn) | return simprocs
  let keys ← DiscrTree.mkPath (mkApp argsFn (← mkFreshExprMVar indexType))
  return simprocs.addCore keys ``reduceArgsApp false (.inr reduceArgsApp)

-- Currently, this could also be acheived by `Simp.mkContext (config := { decide := true })`
def decideDischarge : Simp.Discharge := fun prop => do
  let .some inst ← trySynthInstance (← mkAppM ``Decidable #[prop]) | return none
  let value ← withDefault <| whnf (mkApp2 (mkConst ``Decidable.decide) prop inst)
  if value.isConstOf ``Bool.true then
    return (← mkDecideProof prop)
  else
    return none

/-- One `mlir_env` pass over `e`, with `facts` as extra rewrite rules and `readThroughStore`.
The first fact is the one `argsSimprocs` reduces `Env.args` with. -/
def simpPass (only : Bool) (simpArgs : Syntax) (e : Expr) (facts : Array FVarId) :
    TacticM Simp.Result := do
  let some ext ← getSimpExtension? `mlir_env | throwError "no `mlir_env` simp set"
  let mut thms ←
    if only then
      pure {}
    else
      getSimpTheorems
  for fact in facts do
    thms ← thms.add (.fvar fact) #[] (mkFVar fact)
  let ctx ←
    Simp.mkContext (simpTheorems := #[thms, (← ext.getTheorems)]) (congrTheorems :=
        ← getSimpCongrTheorems)
  let procs :=
    #[←
        if h : 0 < facts.size then
          argsSimprocs facts[0]
        else
          Simp.getSimprocs,
      ← ({} : Simp.Simprocs).add ``readThroughStore (post := true),
      ← ({} : Simp.Simprocs).add ``gepValue (post := true)]
  let elaborated ← elabSimpArgs simpArgs ctx procs (eraseLocal := false) (kind := .simp)
  return (←
        simp e elaborated.ctx (simprocs := elaborated.simprocs) (discharge? := decideDischarge)).1

/-- The state equations `S = …` in context -/
def stateFacts : MetaM (Array FVarId) := do
  (← getLCtx).foldlM (init := #[]) fun acc d => do
      if d.isImplementationDetail then
        return acc
      let some (_, l, _) := (← instantiateMVars d.type).eq? | return acc
      return if l.isFVar && (← inferType l).isConstOf ``GlobalState then acc.push d.fvarId else acc

/-- The equations `x = _` of the locals in `e`: the state `S = …` and the step values `v = …`
it reads. -/
private def valueStateFacts (e : Expr) : MetaM (Array FVarId) := do
  let xs := (collectFVars {} e).fvarSet
  (← getLCtx).foldlM (init := #[]) fun acc d => do
      if d.isImplementationDetail then
        return acc
      let some (_, .fvar x, _) := (← instantiateMVars d.type).eq? | return acc
      return if xs.contains x then acc.push d.fvarId else acc

/-- Resolve the reads in `e`: arguments first, against `argsFact : E.args = _`,
then values, unfolding the write chain with `chainFact : E = _`.
Unfolding first would send the argument reads past `E` down to the root env. -/
def simpValue (only : Bool) (simpArgs : Syntax) (e : Expr) (env : Expr) (expand : Bool) :
    TacticM Simp.Result := do
  let argsFact := (← findEqWithLhs? (← mkAppM ``Env.args #[env]) m!"`{env}.args = _`").toArray
  let chainFact := (← findEqWithLhs? env m!"`{env} = _`").toArray
  let args ← simpPass only simpArgs e argsFact
  let vals ← simpPass only simpArgs args.expr chainFact
  let r ← args.mkEqTrans vals
  let facts ←
    if expand then
      valueStateFacts r.expr
    else
      stateFacts
  if facts.isEmpty then
    return r
  r.mkEqTrans (← simpPass only simpArgs r.expr (argsFact ++ facts))

end ResolveReads

end

end MLIR.Tactic
