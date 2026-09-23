module

public import MLIR.Semantics.Func
public import MLIR.Run.Memory
public meta import MLIR.Run.BasicBlock
public meta import MLIR.Run.Tactic.Env
public meta import MLIR.Run.Tactic.State
public meta import MLIR.Run.Tactic.Seal
public meta import MLIR.Run.Tactic.Step.Common
public meta import Lean.Elab.Tactic
public import MLIR.Run.Tactic.Trace

namespace MLIR

open Lean Elab Tactic Meta

public meta section

syntax (name :=
  stepImpure) "step_impure" (&" only")? (" [" withoutPosition(Lean.Parser.Tactic.simpArg,*,?) "]")? (" with " ident (colGt ident)?)? (&" consuming" (ppSpace colGt ident)+)? " => " tacticSeq :
  tactic

syntax (name :=
  stepImpureInline) "step_impure" (&" only")? (" [" withoutPosition(Lean.Parser.Tactic.simpArg,*,?) "]")? &" inline" (&" consuming" (ppSpace colGt ident)+)? " => " tacticSeq :
  tactic

/-- The hypotheses named in an optional `consuming h₁ h₂ …` group. -/
def consumedIdents (stx : Syntax) : Array Ident :=
  if stx.isNone then #[] else stx[1].getArgs.map (⟨·⟩)

/-- Step a pure instruction, extending the env with the new value -/
def runStepImpure (value : EnvName) (hyp : EnvName) (only : Bool) (simpArgs : Syntax)
    (runTactics : Syntax) (consumed : Array Ident) : TacticM Unit :=
  withMainContext do
    let (g, goal) ← getGoalType
    let inState := (← getRunBodyFrom goal).state
    let ⟨runGoal, main⟩ ← rewriteStep g ``BasicBlock.runBodyFrom_step_of_run
    let some runGoal ← dsimpMlirInstr? runGoal | throwError "Could not `dsimp` runGoal"
    let_expr Eq _ op_run _ :=
      ← instantiateMVars (← runGoal.getType) | throwError m!"{← runGoal.getType} not an equality"
    unless op_run.getAppNumArgs >= 2 do
      throwError m!"Run goal lhs {op_run} not application with env and state"
    let operation := op_run.appFn!.appFn!
    let resultValue ←
      simpValue only simpArgs operation
          (← getRunBodyFrom goal).env -- Let simp work on the newly written value
    let runGoal ← replaceBySimp runGoal operation resultValue
    -- Apply runTactics to runGoal
    setGoals [runGoal]
    evalTactic runTactics
    unless (← getUnsolvedGoals).isEmpty do
      throwError "`step_impure =>` left `insn` unsolved"
    setGoals [main]
    finishStep value hyp only simpArgs
    let ⟨S', hS', hS⟩ ← sealState inState
    -- Drop the consumed facts, where nothing else depends on them
    withMainContext do
        let mut g ← getMainGoal
        for h in consumed do
          let fvarId ← getFVarId h
          g ←
            try
              g.clear fvarId
            catch _ =>
              pure g
        replaceMainGoal [g]
    -- Get facts to preserve
    withMainContext do
        let preserveHyps ← hypsMentioning inState (except := #[hS', hS])
        let mut g ← getMainGoal
        let mut goals := #[]
        let hSId := mkIdent (← hS.getUserName)
        let mlirMem := mkIdent `mlir_mem
        for hyp in preserveHyps do
          let decl ← hyp.getDecl
          -- P S ↦ P S'
          let newTy := (← kabstract (← instantiateMVars decl.type) inState).instantiate1 (.fvar S')
          let pg ← mkFreshExprSyntheticOpaqueMVar newTy (tag := decl.userName) -- New goal
          let (_, g') ← (← g.assert decl.userName newTy pg).intro1P
          g ← g'.clear hyp
          setGoals [pg.mvarId!]
          evalTactic
              (←
                `(tactic|
                    first
                    | (subst $hSId:ident; simp (disch := assumption) [$mlirMem:ident, *]; done)
                    | skip))
          unless ← pg.mvarId!.isAssigned do
            goals := goals.push pg.mvarId!
        let_expr Eq _ S _ :=
          ← instantiateMVars (← hS.getType) | throwError m!"{← hS.getType} is no Equation"
        g ← g.clear hS
        g ← g.clear S.fvarId!
        g ← g.rename S' `S
        g ← g.rename hS' `hS
        setGoals (goals.toList ++ [g])

@[tactic stepImpure]
def evalStepImpure : Tactic := fun stx => do
  let withStx := stx[3]
  let (value, hyp) : EnvName × EnvName :=
    if withStx.isNone then (.auto, .auto)
    else
        let hypStx := withStx[2]
        (.named ⟨withStx[1]⟩, if hypStx.isNone then .auto else .named ⟨hypStx[0]⟩)
  runStepImpure value hyp (only := !stx[1].isNone) (simpArgs := stx[2]) (runTactics := stx[6])
      (consumed := consumedIdents stx[4])

@[tactic stepImpureInline]
def evalStepImpureInline : Tactic := fun stx =>
  runStepImpure .inline .inline (only := !stx[1].isNone) (simpArgs := stx[2]) (runTactics := stx[6])
    (consumed := consumedIdents stx[4])

section InstructionSpecific

macro "step_store" : tactic =>
  `(tactic|
    (step_impure =>
        exact
          run_store (by simp_all)
            (by
              simp; rfl)))

macro "step_load" : tactic =>
  `(tactic|
    (step_impure =>
        exact
          run_load (by simp_all)
            (by
              simp; rfl)))

end InstructionSpecific

end

end MLIR
