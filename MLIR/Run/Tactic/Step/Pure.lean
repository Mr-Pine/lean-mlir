module

public import MLIR.Semantics.Func
public meta import MLIR.Run.BasicBlock
public meta import MLIR.Run.Tactic.Env
public meta import MLIR.Run.Tactic.Seal
public meta import Lean.Elab.Tactic
public import MLIR.Run.Tactic.Trace

namespace MLIR

open Lean Elab Tactic Meta

public meta section

syntax (name :=
  stepPure) "step_pure" (&" only")? (" [" withoutPosition(Lean.Parser.Tactic.simpArg,*,?) "]")? (" with " ident (colGt ident)?)? :
  tactic

syntax (name :=
  stepPureInline) "step_pure" (&" only")? (" [" withoutPosition(Lean.Parser.Tactic.simpArg,*,?) "]")? &" inline" :
  tactic

inductive EnvName
  | inline
  | auto
  | named (s : TSyntax `ident)

/-- dsimp [mlir_instr]; rfl -/
def dsimpPureInstr (m : MVarId) : MetaM Unit := do
  let some ext ← getSimpExtension? `mlir_instr | throwError "no `mlir_instr` simp set"
  let ctx ←
    Simp.mkContext (simpTheorems := #[← ext.getTheorems]) (congrTheorems := ← getSimpCongrTheorems)
  let (m?, _) ← dsimpGoal m ctx (simprocs := #[← Simp.getSimprocs])
  match m? with
  | some m =>
    m.refl
  | none =>
    return ()

/-- Step a pure instruction, extending the env with the new value -/
def runStepPure (value : EnvName) (hyp : EnvName) (only : Bool) (simpArgs : Syntax) :
    TacticM Unit :=
  withMainContext do
    let g ← getMainGoal
    let lem ← mkConstWithFreshMVarLevels ``BasicBlock.runBodyFrom_step_pure
    let r ← g.rewrite (← g.getType) lem -- Rewrite
    let props ←
      r.mvarIds.filterM fun m => do
          isProp (← m.getType) -- Open goals of the rewrite
    -- We want to use simp with `reduceBodyGetElem` `dsimproc` (registered in `simp`) and
    -- the `mlir_instr` simp set on the `h` goal, the only one with an equality
    for m in props do
      if (← instantiateMVars (← m.getType)).isEq then
        dsimpPureInstr m
    -- The remaining `hpos` can be `decide`ed
    for m in props do
      unless ← m.isAssigned do
        m.assign (← mkDecideProof (← whnfR (← instantiateMVars (← m.getType))))
    replaceMainGoal [← g.replaceTargetEq (← instantiateMVars r.eNew) r.eqProof]
    -- Resolve any env reads
    let (g, goal) ← getGoalType
    let envWrite ← getEnvWrite (← getRunBodyFrom goal).env
    let env := envWrite.base
    let resultValue ←
      simpValue only simpArgs envWrite.value env -- Let simp work on the newly written value
    let body ← kabstract goal envWrite.value -- Abstract the written value in the goal
    let motive := Expr.lam `val (← inferType envWrite.value) body .default -- As a lambda
    replaceMainGoal
        [←
            g.replaceTargetEq (body.instantiate1 resultValue.expr)
                (←
                  mkCongrArg motive
                      (←
                        resultValue.getProof'
                            envWrite.value))] -- Using congruence, get proof over goal
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
        let (_, g) ←
          g.withContext do
              generalizeOpaque g (hyps := #[]) envWrite.value var_name
                  #[⟨hyp_name, (mkEq · envWrite.value), ← mkEqRefl envWrite.value⟩]
        replaceMainGoal [g]
    -- Extract new `E`
    evalTactic (← `(tactic| seal_env))
    replaceMainGoal [← reduceIndex (← getMainGoal)]
    runSeal

@[tactic stepPure]
def evalStepPure : Tactic := fun stx => do
  let withStx := stx[3]
  let (value, hyp) : EnvName × EnvName :=
    if withStx.isNone then (.auto, .auto)
    else
        let hypStx := withStx[2]
        (.named ⟨withStx[1]⟩, if hypStx.isNone then .auto else .named ⟨hypStx[0]⟩)
  runStepPure value hyp (only := !stx[1].isNone) (simpArgs := stx[2])

@[tactic stepPureInline]
def evalStepPureInline : Tactic := fun stx =>
  runStepPure .inline .inline (only := !stx[1].isNone) (simpArgs := stx[2])

end

end MLIR
