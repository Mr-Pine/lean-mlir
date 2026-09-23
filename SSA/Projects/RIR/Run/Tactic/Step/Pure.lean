module

public import SSA.Projects.RIR.Semantics.Func
public meta import SSA.Projects.RIR.Run.BasicBlock
public meta import SSA.Projects.RIR.Run.Tactic.Env
public meta import SSA.Projects.RIR.Run.Tactic.Seal
public meta import SSA.Projects.RIR.Run.Tactic.Step.Common
public meta import Lean.Elab.Tactic
public import SSA.Projects.RIR.Run.Tactic.Trace

namespace LeanMLIR.RIR

open Lean Elab Tactic Meta

public meta section

syntax (name :=
  stepPure) "step_pure" (&" only")? (" [" withoutPosition(Lean.Parser.Tactic.simpArg,*,?) "]")? (" with " ident (colGt ident)?)? :
  tactic

syntax (name :=
  stepPureInline) "step_pure" (&" only")? (" [" withoutPosition(Lean.Parser.Tactic.simpArg,*,?) "]")? &" inline" :
  tactic

/-- dsimp [mlir_instr]; rfl -/
def dsimpPureInstr (m : MVarId) : MetaM Unit := do
  match ← dsimpMlirInstr? m with
  | some m =>
    m.refl
  | none =>
    return ()

/-- Step a pure instruction, extending the env with the new value -/
def runStepPure (value : EnvName) (hyp : EnvName) (only : Bool) (simpArgs : Syntax) :
    TacticM Unit :=
  withMainContext do
    let ⟨stepGoal, main⟩ ← rewriteStep (← getMainGoal) ``BasicBlock.runBodyFrom_step_pure
    -- `h : Instr.run E instr = pure ?E'`: unfolding `Instr.run` makes both sides `pure`
    dsimpPureInstr stepGoal
    replaceMainGoal [main]
    finishStep value hyp only simpArgs

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

end LeanMLIR.RIR
