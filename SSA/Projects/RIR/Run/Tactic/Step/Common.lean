module

public meta import SSA.Projects.RIR.Run.Tactic.Util
public meta import SSA.Projects.RIR.Run.Tactic.Env
public meta import SSA.Projects.RIR.Run.Tactic.Seal
public meta import Lean.Elab.Tactic

namespace LeanMLIR.RIR

open Lean Elab Tactic Meta

public meta section

inductive EnvName
  | inline
  | auto
  | named (s : TSyntax `ident)

structure RewriteStepResult where
  stepGoal : MVarId
  mainGoal : MVarId

/-- Rewrite the goal `g` with `lem`, closing the `hpos` goal by `decide`,
returning the remaining goals. -/
def rewriteStep (g : MVarId) (lem : Name) : MetaM RewriteStepResult := do
  let lem ← mkConstWithFreshMVarLevels lem
  -- an abstract block's instructions come from a body fact `blk.body.drop pos = x :: xs`
  let run ←
    g.withContext do
        getRunBodyFrom (← instantiateMVars (← g.getType))
  let fact? ←
    g.withContext do
        bodyFact? run.block run.idx
  let r ← g.rewrite (← g.getType) lem -- Rewrite
  let mut stepGoal? := none
  for m in r.mvarIds do
    let ty := (← instantiateMVars (← m.getType)).consumeTypeAnnotations
    if ty.isAppOf ``LT.lt then -- hpos
      match fact? with
      | some (h, _, _) =>
        m.assign (← mkAppM ``List.lt_length_of_drop_eq_cons #[h])
      | none =>
        m.assign (← mkDecideProof ty)
    else if ty.isEq then -- h
      stepGoal? := some m
  let some stepGoal := stepGoal? | throwError "no run goal (hyp `h`)"
  stepGoal.setTag `insn
  -- Resolve block.body[idx]
  let ty ← instantiateMVars (← stepGoal.getType)
  let some instr := ty.find? (·.isAppOf ``GetElem.getElem) | throwError "no body[pos]"
  let stepGoal ←
    match fact? with
    | some (h, _, _) =>
      stepGoal.withContext do
          let eq ← mkAppM ``List.getElem_of_drop_eq_cons #[h]
          let rw ← stepGoal.rewrite ty eq
          unless rw.mvarIds.isEmpty do
            throwError "body fact: unexpected side goals"
          stepGoal.replaceTargetEq rw.eNew rw.eqProof
    | none =>
      stepGoal.replaceTargetDefEq ((← kabstract ty instr).instantiate1 (← whnfD instr))
  let main ← g.replaceTargetEq (← instantiateMVars r.eNew) r.eqProof
  -- carry the body fact on to the next instruction
  let main ←
    match fact? with
    | some (h, _, _) =>
      main.withContext do
          let h' ← mkAppM ``List.drop_succ_of_drop_eq_cons #[h]
          -- `[…].append rest` from unfolding the pattern, back to `[…] ++ rest`
          let some (_, l, xs) := (← inferType h').eq? | throwError "body fact: not an equation"
          let xs ←
            match_expr xs with
            | List.append _ ys zs =>
              mkAppM ``HAppend.hAppend #[ys, zs]
            | _ =>
              pure xs
          let (_, main) ← (← main.assert `hbody (← mkEq l xs) h').intro1P
          pure main
    | none =>
      pure main
  return ⟨stepGoal, ← reduceIndex main⟩

/-- `dsimp [mlir_instr]` -/
def dsimpMlirInstr? (m : MVarId) : MetaM (Option MVarId) := do
  let some ext ← getSimpExtension? `mlir_instr | throwError "no `mlir_instr` simp set"
  let ctx ←
    Simp.mkContext (simpTheorems := #[← ext.getTheorems]) (congrTheorems := ← getSimpCongrTheorems)
  let (m?, _) ← dsimpGoal m ctx (simprocs := #[← Simp.getSimprocs])
  return m?

/-- Clear the body facts `block.body.drop i = _` behind the goal's position. -/
def clearStaleBodyFacts : TacticM Unit :=
  withMainContext do
    let .ok run ← (getRunBodyFrom? (← getMainTarget)).run | return
    let mut g ← getMainGoal
    for d in ← getLCtx do
      let some (_, lhs, _) := (← instantiateMVars d.type).eq? | continue
      let_expr List.drop _ n body := lhs | continue
      let_expr BasicBlock.body _ _ _ _ b := body | continue
      if (← isDefEq b run.block) && !(← isDefEq n run.idx) then
        g ← g.tryClear d.fvarId
    replaceMainGoal [g]

def finishStep (value : EnvName) (hyp : EnvName) (only : Bool) (simpArgs : Syntax) (expand : Bool) :
    TacticM Unit :=
  withMainContext do
    clearStaleBodyFacts
    -- a call writes its results with `writeMany`: unfold it into single writes (none for `void`)
    evalTactic
        (←
          `(tactic|
              try
                dsimp only [$(mkIdent ``Env.writeMany_nil):ident,
                  $(mkIdent ``Env.writeMany_cons):ident]))
    -- Resolve any env reads
    let (g, goal) ← getGoalType
    let runBodyFrom ← getRunBodyFrom goal
    if runBodyFrom.env.isFVar then
      do
        runSeal
        return -- Nothing to do; Env is not modified
    let envWrite ← getEnvWrite runBodyFrom.env
    let env := envWrite.base
    let resultValue ←
      simpValue only simpArgs envWrite.value env expand -- Let simp work on the newly written value
    replaceMainGoal [← replaceBySimp g envWrite.value resultValue]
    -- If not `inline`, extract the value into a local variable with a hypothesis
    match value with
    | .inline =>
      pure ()
    | _ =>
      do
        let (g, goal) ← getGoalType
        let runBodyFrom ← getRunBodyFrom goal
        let envWrite ← getEnvWrite runBodyFrom.env
        let var_name ←
          match value with
          | .inline =>
            throwError m!"Unreachable: inline var name"
          | .named s =>
            pure s.getId
          | .auto =>
            do
              let some idx ←
                dstIndex? envWrite.dst | throwError m!"Could not get dst index from {envWrite.dst}"
              pure ((`v).appendAfter (toString idx))
        let hyp_name ←
          match hyp with
          | .inline =>
            throwError m!"Cannot have hyp inline but not value"
          | .named s =>
            pure s.getId
          | .auto =>
            pure (var_name.appendBefore "h")
        -- Abstract only the inner `x` of `.value x`. Helps for not carrying the `PoisonOr` Monad.
        let abstractionTarget :=
          if envWrite.value.isAppOfArity ``PoisonOr.value 2 then envWrite.value.appArg!
          else
            if envWrite.value.isAppOfArity ``Ty.wrap 2 then envWrite.value.appArg!
            else envWrite.value
        -- a value that already is a local stays: naming it would capture that local everywhere
        unless abstractionTarget.isFVar do
          let (_, g) ←
            g.withContext do
                generalizeOpaque g (hyps := #[]) abstractionTarget var_name
                    #[⟨hyp_name, (mkEq · abstractionTarget), ← mkEqRefl abstractionTarget⟩]
          replaceMainGoal [g]
    -- Extract new `E`
    sealEnv
    runSeal

end

end LeanMLIR.RIR
