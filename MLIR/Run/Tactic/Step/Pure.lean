module

public import MLIR.Semantics.Func
public meta import MLIR.Run.BasicBlock
public meta import MLIR.Run.Tactic.Env
public meta import MLIR.Run.Tactic.Seal
public meta import MLIR.Run.Tactic.Step.Common
public meta import MLIR.Run.Tactic.Step.Syntax
public meta import MLIR.Run.Tactic.Step.Impure
public meta import Lean.Elab.Tactic
public import MLIR.Run.Tactic.Trace

namespace MLIR

open Lean Elab Tactic Meta

public meta section

syntax (name := stepPure) "step_pure" (stepOpaque)? stepSimpArgs (stepNames)? : tactic

/-- dsimp [mlir_instr]; rfl -/
def dsimpPureInstr (m : MVarId) : MetaM Unit := do
  match ← dsimpMlirInstr? m with
  | some m =>
    m.refl
  | none =>
    return ()

/-- Step a pure instruction, extending the env with the new value; a lifetime marker or an `assume`,
effectful, as `step_lifetime` or `step_assume` does. -/
def runStepPure (args : StepArgs) : TacticM Unit :=
  withMainContext do
    let saved ← saveState
    let ⟨stepGoal, main⟩ ← rewriteStep (← getMainGoal) ``BasicBlock.runBodyFrom_step_pure
    -- `h : Instr.run E instr = pure ?E'`
    let instr := ((← instantiateMVars (← stepGoal.getType)).eq?.map (·.2.1.appArg!)).getD default
    if instr.isAppOf ``Instr.lifetimeStart || instr.isAppOf ``Instr.lifetimeEnd then
      saved.restore
      return ← runLifetimeStep args
    if instr.isAppOf ``Instr.assume then
      saved.restore
      return ← runAssumeStep args
    -- unfolding `Instr.run` makes both sides `pure`
    dsimpPureInstr stepGoal
    replaceMainGoal [main]
    finishStep args

@[tactic stepPure]
def evalStepPure : Tactic := fun stx =>
  Tactic.atStepDepth <| runStepPure (StepArgs.parse stx[2] stx[3] mkNullNode stx[1])

end

end MLIR
