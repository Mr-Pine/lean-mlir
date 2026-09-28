module

public meta import SSA.Projects.RIR.Run.Tactic.Parse
public meta import SSA.Projects.RIR.Run.Tactic.Util
public meta import SSA.Projects.RIR.Run.Tactic.Memory
public meta import SSA.Projects.RIR.Run.Tactic.Env
public meta import SSA.Projects.RIR.Run.Tactic.Seal
public meta import SSA.Projects.RIR.Run.BasicBlock
public meta import Lean.Elab.Tactic

namespace LeanMLIR.RIR

open Lean Elab Tactic Meta

public meta section

/-- Close `E' = E`, where `E'` is a lemma's write chain over an unknown base: the base becomes
`E`, and each write a goal `E.read r = v` (`Env.write_eq_of`), returned. -/
partial def matchEnv (g : MVarId) : MetaM (List MVarId) := do
  let some (_, lhs, _) := (← instantiateMVars (← g.getType)).eq? | throwError "not an equation"
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
root, with its args fact chained through `E`'s, and the env is sealed as after a step. `E`, its
chain and the step values only it read are cleared. -/
def enterContinuation (g : MVarId) (E : Expr) : TacticM Unit := do
  let (hE?, hArgs?) ←
    g.withContext do
        return (← Tactic.findEqWithLhs? E m!"`{E} = _`",
            ← Tactic.findEqWithLhs? (← mkAppM ``Env.args #[E]) m!"`{E}.args = _`")
  let (fvs, g) ← g.introN 2 [`E₀, `hArgs₀]
  replaceMainGoal [g]
  withMainContext do
      let hA := fvs[1]!
      -- `E`'s args fact, or else its chain's root's args: writes keep the args (`rfl`)
      let pf? ←
        match hArgs?, hE? with
        | some hArgs, _ =>
          pure (some (← mkEqTrans (mkFVar hA) (mkFVar hArgs)))
        | none, some hE =>
          do
            let some (_, _, chain) := (← instantiateMVars (← hE.getType)).eq? | pure none
            let mut root := chain
            while root.isAppOfArity ``Env.write 5 do
              root := root.getArg! 2
            let args ←
              withLocalDeclD `e (← inferType E) fun e => do
                  mkLambdaFVars #[e] (← mkAppM ``Env.args #[e])
            let pf ← mkEqTrans (mkFVar hA) (← mkCongrArg args (mkFVar hE))
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
      let mut g ← getMainGoal
      let some hE := hE? | return
      let some (_, _, chain) := (← instantiateMVars (← hE.getType)).eq? | return
      for x in #[hE] ++ hArgs?.toArray ++ E.fvarId?.toArray do
        g ← g.tryClear x
      -- the chain's locals: its root, and the values with their `v = …`
      for x in (collectFVars {} chain).fvarIds do
        g ← tryClearValue g x
        g ← g.tryClear x
      replaceMainGoal [g]

/-- `step_loop using h` closes a `runFrom E k S` goal with the loop lemma `h` (or the induction
hypothesis at a back-edge), whose env is a write chain over a base: the base becomes `E`, and each
write a goal `E.read r = v`. Those and `h`'s premises get `simp [*, mlir_env]`, or `omega`; what
they cannot close stays open. A continuation premise is entered, as the last goal. -/
syntax (name := stepLoop) "step_loop" " using " term : tactic

@[tactic stepLoop]
def evalStepLoop : Tactic := fun stx => do
  withMainContext do
      let (g, goal) ← Tactic.getGoalType
      let S := (← Tactic.getFuncRunFromGoal goal).state
      if S.isFVar then
        if let some hS← Tactic.findEqWithLhs? S m!"`{S} = _`" then
          -- eliminate `S`, keeping the name the lemma's premises use
          replaceMainGoal [(← substCore g hS (symm := false)).2]
  let E ←
    withMainContext do
        return (← Tactic.getFuncRunFromGoal (← getMainTarget)).env
  -- `apply`, not `refine`: the lemma's env `?E'` must stay assignable
  replaceMainGoal (← (← getMainGoal).apply (← mkConstWithFreshMVarLevels ``Func.runFrom_of_env_eq))
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
  let premises ← getGoals
  let reads ← matchEnv he
  let mut open_ := #[]
  let mut conts := #[]
  for g in reads ++ premises do
    if ← g.isAssigned then
      continue
    let ty ← whnfR (← instantiateMVars (← g.getType))
    if let .forallE _ d _ _ := ty then
      if (← whnfR d).isAppOf ``Env then
        conts := conts.push g
        continue
    setGoals [g]
    evalTactic
        (←
          `(tactic|
              first
              | (simp [*, $(mkIdent `mlir_env):ident, $(mkIdent ``Tactic.gepValue):ident]; done)
              | omega
              | try simp [*, $(mkIdent `mlir_env):ident, $(mkIdent ``Tactic.gepValue):ident]))
    open_ := open_ ++ (← getGoals)
  for g in conts do
    setGoals [g]
    enterContinuation g E
    open_ := open_ ++ (← getGoals)
  setGoals open_.toList

end

end LeanMLIR.RIR
