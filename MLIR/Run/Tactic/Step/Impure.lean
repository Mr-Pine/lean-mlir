module

public import MLIR.Semantics.Func
public import MLIR.Run.Memory
public meta import MLIR.Run.BasicBlock
public meta import MLIR.Run.Tactic.Env
public meta import MLIR.Run.Tactic.State
public meta import MLIR.Run.Tactic.Seal
public meta import MLIR.Run.Tactic.Step.Common
public meta import MLIR.Run.Tactic.Step.Syntax
public meta import Lean.Elab.Tactic
public import MLIR.Run.Tactic.Trace

namespace MLIR

open Lean Elab Tactic Meta

public meta section

syntax (name := stepImpure)
  "step_impure" stepSimpArgs (stepNames)? (stepConsuming)? " => " tacticSeq : tactic

/-- `step_impure` for a `load`, closing the instruction with `run_load`. -/
syntax (name := stepLoad) "step_load" stepSimpArgs (stepNames)? (stepConsuming)? : tactic

/-- `step_impure` for a `store`, closing the instruction with `run_store`. -/
syntax (name := stepStore) "step_store" stepSimpArgs (stepConsuming)? : tactic

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
    setGoals [runGoal] -- Makes the following simp work
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
    let ⟨S', hS', hS⟩ ← sealState inState
    -- Drop the consumed facts, where nothing else depends on them
    withMainContext do
        let mut g ← getMainGoal
        for h in consumed do
          let fvarId ← getFVarId h
          g ← g.clear fvarId
        replaceMainGoal [g]
    -- Get facts to preserve
    let goals ←
      withMainContext do
          let preserveHyps ← hypsMentioning inState (except := #[hS', hS])
          let mut g ← getMainGoal
          let mut goals := #[]
          let hSId := mkIdent (← hS.getUserName)
          let hS'Id := mkIdent (← hS'.getUserName)
          let mlirMem := mkIdent `mlir_mem
          for hyp in preserveHyps do
            let decl ← hyp.getDecl
            -- P S ↦ P S'
            let newTy :=
              (← kabstract (← instantiateMVars decl.type) inState).instantiate1 (.fvar S')
            let pg ← mkFreshExprSyntheticOpaqueMVar newTy (tag := decl.userName) -- New goal
            let (_, g') ← (← g.assert decl.userName newTy pg).intro1P
            g ← g'.clear hyp
            setGoals [pg.mvarId!]
            let hId := mkIdent decl.userName
            evalTactic
                (←
                  `(tactic|
                      first
                      | ( subst $hSId:ident
                          try simp at $hId:ident
                          simp [$mlirMem:ident, $hS'Id:ident, $hId:ident]
                          done)
                      | (subst $hSId:ident $hS'Id:ident; assumption)
                      | skip))
            unless ← pg.mvarId!.isAssigned do
              goals := goals.push pg.mvarId!
          let_expr Eq _ S _ :=
            ← instantiateMVars (← hS.getType) | throwError m!"{← hS.getType} is no Equation"
          g ← g.clear hS
          g ← g.clear S.fvarId!
          g ← g.rename S' `S
          g ← g.rename hS' `hS
          setGoals [g]
          return goals
    finishStep value hyp only simpArgs
    setGoals (goals.toList ++ (← getGoals))

/-- Step an effectful instruction, proving it with `tac`. -/
def runStep (args : StepArgs) (tac : Syntax) : TacticM Unit :=
  runStepImpure args.value args.hyp args.only args.simpArgs tac args.consumed

@[tactic stepImpure]
def evalStepImpure : Tactic := fun stx => runStep (StepArgs.parse stx[1] stx[2] stx[3]) stx[5]

section InstructionSpecific

@[tactic stepLoad]
def evalStepLoad : Tactic := fun stx => do
  runStep (StepArgs.parse stx[1] stx[2] stx[3])
      (← `(tacticSeq| exact run_load (by simp_all) (by dsimp; try simp; rfl)))

@[tactic stepStore]
def evalStepStore : Tactic := fun stx => do
  runStep (StepArgs.parse stx[1] mkNullNode stx[2])
      (← `(tacticSeq| exact run_store (by simp_all) (by dsimp; try simp; rfl)))

end InstructionSpecific

end

end MLIR
