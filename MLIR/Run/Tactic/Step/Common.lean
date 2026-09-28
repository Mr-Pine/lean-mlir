module

public meta import MLIR.Run.Tactic.Util
public meta import MLIR.Run.Tactic.Env
public meta import MLIR.Run.Tactic.Seal
public meta import Lean.Elab.Tactic

namespace MLIR

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
  let r ← g.rewrite (← g.getType) lem -- Rewrite
  let mut stepGoal? := none
  for m in r.mvarIds do
    let ty := (← instantiateMVars (← m.getType)).consumeTypeAnnotations
    if ty.isAppOf ``LT.lt then -- hpos
      m.assign (← mkDecideProof ty)
    else if ty.isEq then -- h
      stepGoal? := some m
  let some stepGoal := stepGoal? | throwError "no run goal (hyp `h`)"
  stepGoal.setTag `insn
  -- Resolve block.body[idx]
  let ty ← instantiateMVars (← stepGoal.getType)
  let some instr := ty.find? (·.isAppOf ``GetElem.getElem) | throwError "no body[pos]"
  let stepGoal ← stepGoal.replaceTargetDefEq ((← kabstract ty instr).instantiate1 (← whnfD instr))
  let main ← g.replaceTargetEq (← instantiateMVars r.eNew) r.eqProof
  return ⟨stepGoal, ← reduceIndex main⟩

/-- `dsimp [mlir_instr]` -/
def dsimpMlirInstr? (m : MVarId) : MetaM (Option MVarId) := do
  let some ext ← getSimpExtension? `mlir_instr | throwError "no `mlir_instr` simp set"
  let ctx ←
    Simp.mkContext (simpTheorems := #[← ext.getTheorems]) (congrTheorems := ← getSimpCongrTheorems)
  let (m?, _) ← dsimpGoal m ctx (simprocs := #[← Simp.getSimprocs])
  return m?

def finishStep (value : EnvName) (hyp : EnvName) (only : Bool) (simpArgs : Syntax) (expand : Bool) :
    TacticM Unit :=
  withMainContext do
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

end MLIR
