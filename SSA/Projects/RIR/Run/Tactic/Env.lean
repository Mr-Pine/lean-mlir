module

public import SSA.Projects.RIR.Semantics.Func
public import SSA.Projects.RIR.Run.Tactic.Parse
public import SSA.Projects.RIR.Run.Tactic.Util
public meta import Lean.Elab.Tactic

namespace LeanMLIR.RIR.Tactic

open Lean Elab Tactic Meta

public meta section

section SealEnv

def sealEnv : TacticM Unit :=
  withMainContext do
    let (g, goal) ← getGoalType
    let runBodyFrom ← getRunBodyFrom goal
    if runBodyFrom.env.isFVar then
      return
    let envWrite ← getEnvWrite runBodyFrom.env
    let E := envWrite.base
    let hE ← findEqWithLhs E m!"of the form `{E} = _`"
    let hEargs ←
      findEqWithLhs (← mkAppM ``Env.args #[E]) m!"of the form `{(← mkAppM ``Env.args #[E])} = _"
    let some (_, _, E₀chain) :=
      (← instantiateMVars (← hE.getType)).eq? | throwError "expected an equation"
    let some (_, _, args) :=
      (← instantiateMVars (← hEargs.getType)).eq? | throwError "expected an equation"
    if (← hE.getType).eq?.get!.2.1 != envWrite.base then
      throwError
          m!"env base {envWrite.base} from goal is different from the one in {← hE.getType} differ"
    let abstractWrite := Expr.lam `e (← inferType E) (← kabstract runBodyFrom.env E) .default
    let stmtEq := (mkEq · (abstractWrite.beta #[E₀chain]))
    let stmtArgs (e) : MetaM _ := do
      mkEq (← mkAppM ``Env.args #[e]) args
    let (_, g) ←
      g.withContext do
          generalizeOpaque g (hyps := #[]) runBodyFrom.env `E
              #[⟨`hE, stmtEq, ← mkCongrArg abstractWrite (mkFVar hE)⟩,
                ⟨`hArgs, stmtArgs, mkExpectedPropHint (mkFVar hEargs) (← stmtArgs runBodyFrom.env)⟩]
    let g ← g.clear hE
    let g ← g.clear hEargs
    let g ← g.clear E.fvarId!
    replaceMainGoal [g]

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

/-- One `mlir_env` pass over `e`, with `fact` as an extra rewrite rule -/
def simpPass (only : Bool) (simpArgs : Syntax) (e : Expr) (fact : FVarId) : TacticM Simp.Result :=
  do
  let some ext ← getSimpExtension? `mlir_env | throwError "no `mlir_env` simp set"
  let mut thms ←
    if only then
      pure {}
    else
      getSimpTheorems
  thms ← thms.add (.fvar fact) #[] (mkFVar fact)
  let ctx ←
    Simp.mkContext (simpTheorems := #[thms, (← ext.getTheorems)]) (congrTheorems :=
        ← getSimpCongrTheorems)
  let elaborated ←
    elabSimpArgs simpArgs ctx #[← argsSimprocs fact] (eraseLocal := false) (kind := .simp)
  return (←
        simp e elaborated.ctx (simprocs := elaborated.simprocs) (discharge? := decideDischarge)).1

/-- Resolve the reads in `e`: arguments first, against `argsFact : E.args = _`,
then values, unfolding the write chain with `chainFact : E = _`.
Unfolding first would send the argument reads past `E` down to the root env. -/
def simpValue (only : Bool) (simpArgs : Syntax) (e : Expr) (env : Expr) : TacticM Simp.Result := do
  let argsFact ← findEqWithLhs (← mkAppM ``Env.args #[env]) m!"`{env}.args = _`"
  let chainFact ← findEqWithLhs env m!"`{env} = _`"
  let args ← simpPass only simpArgs e argsFact
  let vals ← simpPass only simpArgs args.expr chainFact
  args.mkEqTrans vals

end ResolveReads

end

end LeanMLIR.RIR.Tactic
