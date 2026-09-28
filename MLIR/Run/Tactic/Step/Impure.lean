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
    (expand : Bool) (runTactics : Syntax) (consumed : Array Ident) : TacticM Unit :=
  focus <|
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
        simpValue only simpArgs operation (← getRunBodyFrom goal).env
            expand -- Let simp work on the newly written value
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
                        -- fast path: the old fact and one transport lemma
                        | ( subst $hS'Id:ident $hSId:ident
                            solve_by_elim (transparency := .reducible) only [$hId:ident]
                              using $(mkIdent `mlir_transport):ident)
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
      finishStep value hyp only simpArgs expand
      setGoals (goals.toList ++ (← getGoals))

/-- Step an effectful instruction, proving it with `tac`. -/
def runStep (args : StepArgs) (tac : Syntax) : TacticM Unit :=
  runStepImpure args.value args.hyp args.only args.simpArgs args.expand tac args.consumed

@[tactic stepImpure]
def evalStepImpure : Tactic := fun stx =>
  runStep (StepArgs.parse stx[1] stx[2] stx[3] mkNullNode) stx[5]

section InstructionSpecific

/-- Fail unless every `PoisonOr` operand of the instruction's operation is `.value _`: the
`run_load`/`run_store` lemmas need known values, and `simp_all` cannot find a missing one. -/
elab "expect_values" : tactic =>
  withMainContext do
    let_expr Eq _ lhs _ := ← instantiateMVars (← getMainTarget)
      | throwError "expected an equation, got{indentExpr (← getMainTarget)}"
    -- `op E S`: the operation, applied to the env and the state
    for a in lhs.appFn!.appFn!.getAppArgs do
      if (← whnf (← inferType a)).isAppOf ``PoisonOr && !a.isAppOfArity ``PoisonOr.value 2 then
        throwError "operand{indentExpr a}\nis not known to be `.value _`; it may be poison"

@[tactic stepLoad]
def evalStepLoad : Tactic := fun stx => do
  runStep (StepArgs.parse stx[1] stx[2] stx[3] mkNullNode)
      (← `(tacticSeq| expect_values; exact run_load (by simp_all) (by dsimp; try simp; rfl)))

@[tactic stepStore]
def evalStepStore : Tactic := fun stx => do
  runStep (StepArgs.parse stx[1] mkNullNode stx[2] mkNullNode)
      (← `(tacticSeq| expect_values; exact run_store (by simp_all) (by dsimp; try simp; rfl)))

end InstructionSpecific

end

end MLIR
