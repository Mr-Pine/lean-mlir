module

public import SSA.Projects.RIR.Semantics.Func
public meta import SSA.Projects.RIR.Run.BasicBlock
public meta import SSA.Projects.RIR.Run.Tactic.Env
public meta import SSA.Projects.RIR.Run.Tactic.Seal
public meta import SSA.Projects.RIR.Run.Tactic.Step.Common
public meta import SSA.Projects.RIR.Run.Tactic.Step.Syntax
public meta import Lean.Elab.Tactic
public import SSA.Projects.RIR.Run.Tactic.Trace

namespace LeanMLIR.RIR

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

/-- Step a pure instruction, extending the env with the new value -/
def runStepPure (args : StepArgs) : TacticM Unit :=
  withMainContext do
    let ⟨stepGoal, main⟩ ← rewriteStep (← getMainGoal) ``BasicBlock.runBodyFrom_step_pure
    -- `h : Instr.run E instr = pure ?E'`: unfolding `Instr.run` makes both sides `pure`
    dsimpPureInstr stepGoal
    replaceMainGoal [main]
    finishStep args

@[tactic stepPure]
def evalStepPure : Tactic := fun stx =>
  Tactic.atStepDepth <| runStepPure (StepArgs.parse stx[2] stx[3] mkNullNode stx[1])

end

end LeanMLIR.RIR
