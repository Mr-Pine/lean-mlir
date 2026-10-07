module

public meta import MLIR.Run.Tactic.Parse
public meta import MLIR.Run.Tactic.Util
public meta import MLIR.Run.Tactic.Memory
public meta import MLIR.Run.Tactic.Env
public meta import MLIR.Run.Tactic.Seal
public meta import MLIR.Run.Tactic.State
public meta import MLIR.Run.BasicBlock
public meta import Lean.Elab.Tactic

namespace MLIR

open Lean Elab Tactic Meta

public meta section

/-- Close `E' = E`, where `E'` is a lemma's write chain over an unknown base: the base becomes
`E`, and each write a goal `E.read r = v` (`Env.write_eq_of`), returned. -/
partial def matchEnv (g : MVarId) : MetaM (List MVarId) := do
  let some (_, lhs, _) := (← instantiateMVars (← g.getType)).eq? | throwError "not an equation"
  -- a lemma's env may be a function of its base, applied, or an abbreviation of one
  let lhs ← whnfR lhs
  unless lhs.isAppOfArity ``Env.write 5 do
    g.refl
    return []
  let mut reads := []
  for g' in ← g.apply (← mkConstWithFreshMVarLevels ``Env.write_eq_of) do
    if ← g'.isAssigned then
      continue
    let some (_, l, _) := (← instantiateMVars (← g'.getType)).eq? | continue
    if l.isAppOf ``Env.read then
      reads := reads ++ [g']
    else
      reads := reads ++ (← matchEnv g')
  return reads

/-- Enter a continuation `∀ E₀, E₀.args = E.args → runFrom (E₀[…]) k S = K`: `E₀` becomes the
root, with its args fact chained through `E`'s, the env is sealed and the state simplified as after
a step. `E`, its chain and the step values only it read are cleared. -/
def enterContinuation (g : MVarId) (E : Expr) : TacticM Unit := do
  let (hE?, hArgs?) ←
    g.withContext do
        return (← Tactic.findLocalEq? E, ← Tactic.findEqWithLhs? (← mkAppM ``Env.args #[E]))
  let (fvs, g) ← g.introN 2 [`E₀, `hArgs₀]
  -- the lemma's env and state may be functions of `E₀`, applied, or abbreviations: unfolded
  let g ←
    g.withContext do
        let ty ← instantiateMVars (← g.getType)
        let r ← Tactic.getFuncRunFromGoal ty
        let env' ← whnfR r.env
        let st' ← whnfR r.state
        g.replaceTargetDefEq
            (ty.replace fun e =>
              if e == r.env then some env' else if e == r.state then some st' else none)
  replaceMainGoal [g]
  withMainContext do
      let hA := fvs[1]!
      -- `E`'s args fact, or else its chain's root's args: writes keep the args (`rfl`). Only for a
      -- premise `E₀.args = E.args`: one naming the args (`(args …).get`) stays as it is
      let some (_, _, argsA) := (← inferType (mkFVar hA)).eq? | return
      let onE ← withReducible <| isDefEq argsA (← mkAppM ``Env.args #[E])
      let pf? ←
        if !onE then
          pure none
        else
          match hArgs?, hE? with
          | some hArgs, _ =>
            pure (some (← mkEqTrans (mkFVar hA) (mkFVar hArgs)))
          | none, some hE =>
            do
              let root := Tactic.envRoot hE.rhs
              let args ←
                withLocalDeclD `e (← inferType E) fun e => do
                    mkLambdaFVars #[e] (← mkAppM ``Env.args #[e])
              let pf ← mkEqTrans (mkFVar hA) (← mkCongrArg args hE.decl.toExpr)
              let some (_, l, _) := (← inferType pf).eq? | pure none
              pure (some (mkExpectedPropHint pf (← mkEq l (← mkAppM ``Env.args #[root]))))
          | none, none =>
            pure none
      if let some pf := pf? then
        let (_, g) ← (← (← getMainGoal).assert `hArgs₀ (← inferType pf) pf).intro1P
        replaceMainGoal [← g.clear hA]
  withMainContext do
      let (_, goal) ← Tactic.getGoalType
      Tactic.sealEnvAt (← Tactic.getFuncRunFromGoal goal).env
  withMainContext do
      let (g, goal) ← Tactic.getGoalType
      let s := (← Tactic.getFuncRunFromGoal goal).state
      let r ← Tactic.simpState s
      if r.expr != s then
        replaceMainGoal [← Tactic.replaceBySimp g s r]
  withMainContext do
      let mut g ← getMainGoal
      let some hE := hE? | return
      let chain := hE.rhs
      for x in #[hE.decl.fvarId] ++ hArgs?.toArray ++ E.fvarId?.toArray do
        g ← g.tryClear x
      -- the chain's locals: its root, and the values with their `v = …`
      for x in (collectFVars {} chain).fvarIds do
        g ← tryClearValue g x
        g ← g.tryClear x
      replaceMainGoal [g]
  -- named again, the facts carried over from the earlier state `S` while it is still a local, as
  -- a step's
  Tactic.ensureStateEq
  -- then `S` (kept for applying the lemma) substituted by its definition, so later
  -- generalizations do not nest over it
  withMainContext do
      let S' := (← Tactic.getFuncRunFromGoal (← getMainTarget)).state
      let some hS' ← Tactic.findLocalEq? S' | return
      let g ← Tactic.substStates (← getMainGoal) hS'.rhs
      replaceMainGoal [g]
      -- the substituted state's projections reduced, as a step's
      let some hS' ← g.withContext (Tactic.findEqWithLhs? S') | return
      replaceMainGoal [← Tactic.dsimpStateEq g hS']

/-- Close a read goal `E.read r = v` through `E`'s write chain (`walkRead`, else `simpValue`);
unless the result is `v` itself, leave `result = v` open. -/
def closeRead (g : MVarId) : TacticM (List MVarId) :=
  g.withContext do
    let some (_, lhs, rhs) := (← instantiateMVars (← g.getType)).eq? | return [g]
    unless lhs.isAppOfArity ``Env.read 4 do
      return [g]
    if let some (v, pf)← Tactic.walkRead (lhs.getArg! 2) (lhs.getArg! 3) then
      if ← withReducible (isDefEq v rhs) then
        g.assign (mkExpectedPropHint pf (← mkEq lhs v))
        return []
    setGoals [g]
    let r ← Tactic.simpValue true mkNullNode lhs (lhs.getArg! 2) false
    let pf ← r.getProof
    if ← withReducible (isDefEq r.expr rhs) then
      g.assign pf
      return []
    let rest ← mkFreshExprSyntheticOpaqueMVar (← mkEq r.expr rhs) (tag := ← g.getTag)
    g.assign (← mkEqTrans pf rest)
    return [rest.mvarId!]

/-- Close `E.read r = v`, or a conjunction of such (`E ⊨ [r := v, …]`), through `E`'s writes,
assigning `v` where it is a metavariable; the rest by `rfl`, else returned. -/
partial def closeReads (g : MVarId) : TacticM (List MVarId) := do
  let ty ←
    g.withContext do
        whnfR (← instantiateMVars (← g.getType))
  if let some (ga, gb)← Tactic.splitAnd? g ty then
    return (← closeReads ga) ++ (← closeReads gb)
  let mut open_ := []
  for g' in ← closeRead g do
    unless
      ←
        (do
              g'.refl;
              pure true) <|>
            pure false do
      open_ := open_ ++ [g']
  return open_

/-- Whether `g` is a read, or a conjunction of reads, of an env. -/
partial def isReadGoal (ty : Expr) : Bool :=
  match ty.and? with
  | some (a, b) => isReadGoal a && isReadGoal b
  | none => Tactic.isEnvReadEq ty

/-- `env_reads` closes `E.read r = v`, or `E ⊨ [r := v, …]`, through `E`'s writes as `step_loop`
closes its reads; what remains, by `rfl`. -/
elab "env_reads" : tactic => do
  replaceMainGoal (← closeReads (← getMainGoal))

/-- `step_loop using h` closes a `runFrom E k S` goal, or `runFrom E k S >>= g`, with the loop
lemma `h` (or the induction hypothesis at a back-edge), whose env is a write chain over a base: the
base becomes `E`, and each write a goal `E.read r = v`. Those and `h`'s premises get
`simp [*, mlir_env]`, or `omega`; what they cannot close stays open, a run's as it was. A continuation premise is
entered, as the last goal. -/
syntax (name := stepLoop) "step_loop" " using " term : tactic

/-- `step_loop`'s lemma application, with `S` first substituted by its definition if `subst`:
the goal's env, the env goal, and the lemma's premises. -/
def stepLoopApply (stx : Syntax) (subst : Bool) : TacticM (Expr × MVarId × List MVarId) := do
  if subst then
    withMainContext do
        let (g, goal) ← Tactic.getGoalType
        let S := (← Tactic.getFuncRunFromGoal goal).state
        if S.isFVar then
          if let some hS← Tactic.findEqWithLhs? S then
            -- eliminate `S`, keeping the name the lemma's premises use
            replaceMainGoal [(← substCore g hS (symm := false)).2]
  let E ←
    withMainContext do
        return (← Tactic.getFuncRunFromGoal (← getMainTarget)).env
  -- `apply`, not `refine`: the lemma's env `?E'` must stay assignable. Under a bind (a framed
  -- function's run, before its frame erase) the lemma is stated with the same bind.
  let g ← getMainGoal
  let gs ←
    try
      g.apply (← mkConstWithFreshMVarLevels ``Func.runFrom_of_env_eq)
    catch _ =>
      g.apply (← mkConstWithFreshMVarLevels ``Func.runFrom_bind_of_env_eq)
  replaceMainGoal gs
  -- `?he : ?E' = E` and `?run : runFrom ?E' k S = K`, told apart by their types
  let mut he? := none
  let mut run? := none
  for g in ← getGoals do
    let ty ← instantiateMVars (← g.getType)
    if !(← isProp ty) then
      continue
    if (ty.find? (·.isAppOf ``Func.runFrom)).isSome then
      run? := some g
    else if ty.isEq then
      he? := some g
  let (some he, some run) := (he?, run?) | throwError "`step_loop`: no env or run goal"
  setGoals [run]
  evalTactic (← `(tactic| apply $(⟨stx[2]⟩)))
  return (E, he, ← getGoals)

/-- `step_loop` after the lemma applied: the env's reads, the premises, the continuation. -/
def stepLoopFinish (E : Expr) (he : MVarId) (premises : List MVarId) : TacticM Unit := do
  let reads ← matchEnv he
  let mut rest : List MVarId := []
  for g in reads do
    unless ← g.isAssigned do
      rest := rest ++ (← closeRead g)
  let mut open_ := #[]
  let mut conts := #[]
  for g in rest ++ premises do
    if ← g.isAssigned then
      continue
    let ty ← whnfR (← instantiateMVars (← g.getType))
    if let .forallE _ d _ _ := ty then
      if (← whnfR d).isAppOf ``Env then
        conts := conts.push g
        continue
    -- reads through the env's writes first: `simp [*]` would assign their values from any fact;
    -- what they leave has its values fixed, so `simp [*]` may close it
    let gs ←
      if isReadGoal (← instantiateMVars (← g.getType)) then
        g.withContext (closeReads g)
      else
        pure [g]
    for g in gs do
      setGoals [g]
      -- a fact, or `omega`, first: cheap, and `simp [*]` scans the whole context; a premise about
      -- a run (a continuation like `(if c then runFrom … else …) = K`) stays as it is
      let aboutRun := ((← instantiateMVars (← g.getType)).find? (·.isAppOf ``Func.runFrom)).isSome
      evalTactic
          (←
            if aboutRun then
              `(tactic|
                  first
                  | with_reducible assumption
                  | skip)
            else
              `(tactic|
                  first
                  | with_reducible assumption
                  | omega
                  | mem_fact
                  | try simp [*, $(mkIdent `mlir_env):ident, $(mkIdent ``Tactic.gepValue):ident]))
      open_ := open_ ++ (← getGoals)
  for g in conts do
    setGoals [g]
    enterContinuation g E
    open_ := open_ ++ (← getGoals)
  setGoals open_.toList

/-- Whether the loop lemma `stx` is about a fixed state: its run's state mentions a local, not only
the lemma's binders (an induction hypothesis, a continuation). -/
def fixedStateLemma (stx : Syntax) : TacticM Bool :=
  withoutModifyingState <|
    withMainContext do
      try
        let e ← Term.withoutErrToSorry (elabTerm stx none (mayPostpone := true))
        forallTelescopeReducing (← instantiateMVars (← inferType e)) fun xs concl => do
            let some run := concl.find? (·.isAppOfArity ``Func.runFrom 4) | return false
            let bound := xs.map (·.fvarId!)
            return run.appArg!.hasAnyFVar (!bound.contains ·)
      catch _ =>
        return false

@[tactic stepLoop]
def evalStepLoop : Tactic := fun stx => do
  -- keep the state `S` when the lemma applies to it: its facts stay usable; an induction
  -- hypothesis about a fixed state needs `S` substituted first
  let saved ← saveState
  let (E, he, premises) ←
    try
      stepLoopApply stx false
    catch ex =>
      saved.restore
      -- a warning, unless the lemma is about a fixed state, which needs `S` substituted: the steps
      -- after a loop lemma would work on `S`'s definition, not on `S`
      unless ← fixedStateLemma stx[2] do
        logWarning
            m!"`step_loop`: the lemma does not apply to the state `S`, so `S` is \
          substituted by its definition:{indentD ex.toMessageData}"
      stepLoopApply stx true
  stepLoopFinish E he premises

end

end MLIR
