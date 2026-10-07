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

/-- `step_impure` for a `memcpy`, closing the instruction with `run_memcpy`. -/
syntax (name := stepMemcpy) "step_memcpy" stepSimpArgs (stepConsuming)? : tactic

/-- `step_impure` for a `memset`, closing the instruction with `run_memset`. -/
syntax (name := stepMemset) "step_memset" stepSimpArgs (stepConsuming)? : tactic

/-- `step_impure` for a `store`, closing the instruction with `run_store`. -/
syntax (name := stepStore) "step_store" stepSimpArgs (stepConsuming)? : tactic

/-- Seal the goal's new state as `S` with `hS`, carrying the facts about `inState` over (the
unproved ones are returned as goals). -/
def sealStep (inState : Expr) : TacticM (Array MVarId) := do
  -- the new state's memory facts, about it as a term over `inState`, then generalized with it
  let (mem, olds) ←
    withMainContext do
        let (g, goal) ← getGoalType
        let (hyps, olds, g) ← Tactic.memFactsOf g inState (← getRunBodyFrom goal).state
        replaceMainGoal [g]
        return (hyps, olds)
  let ⟨S', hS', hS⟩ ← sealState inState mem
  -- the old read facts: carried over by `memFactsOf`, used by `sealState`'s simplification
  withMainContext do
      replaceMainGoal [← (← getMainGoal).tryClearMany olds]
  -- Get facts to preserve
  let goals ←
    withMainContext do
        -- not the new state's own facts (its reads may mention `inState` in their values), nor
        -- facts about `inState` only as `inState.allocaPtr`: a fixed pointer, not the state
        let allocaPtr ← mkAppM ``GlobalState.allocaPtr #[inState]
        let preserveHyps ←
          (← hypsMentioning inState (except := #[hS', hS])).filterM fun h => do
              let ty ← instantiateMVars (← h.getType)
              -- a continuation stays about its own state
              if ← Tactic.isContinuation ty then
                return false
              let rest :=
                ty.replace fun t => if t == allocaPtr then some (mkConst ``Unit.unit) else none
              return !ty.containsFVar S' && inState.occurs rest
        let mut g ← getMainGoal
        let mut goals := #[]
        let facts ← contextFactMap
        let transport ← labelled `mlir_transport
        let locals ← Tactic.localImplications
        let new? := (← instantiateMVars (← hS'.getType)).eq?.map (·.2.2)
        for hyp in preserveHyps do
          let decl ← hyp.getDecl
          -- `P S` as `fun s => P s`, then `P S'`
          let key ← instantiateMVars decl.type
          let motive := .lam `s (← inferType inState) (← kabstract key inState) .default
          let newTy := motive.beta #[.fvar S']
          let pg ← mkFreshExprSyntheticOpaqueMVar newTy (tag := decl.userName) -- New goal
          let (_, g') ← (← g.assert decl.userName newTy pg).intro1P
          g ← g'.clear hyp
          -- `P (new state)` carried from `P S`, then `hS'` back; else left open
          let pf? ←
            observing? do
                let some new := new? | failure
                let some pf ←
                  Tactic.carryFact facts transport locals (.fvar hyp) key
                      (motive.beta #[new]) | failure
                mkEqNDRec motive pf (← mkEqSymm (.fvar hS'))
          match pf? with
          | some pf =>
            pg.mvarId!.assign pf
          | none =>
            goals := goals.push pg.mvarId!
        -- substitute, not clear: a written value may mention the old state (`alloca`).
        -- `substCore` reverts and reintroduces what follows `S`, so `S'`/`hS'` get new ids
        let (fs, g') ← substCore g hS (symm := false)
        g := g'
        g ← g.rename (fs.get S').fvarId! `S
        let hNew := (fs.get hS').fvarId!
        g ← g.rename hNew `hS
        -- the substituted old state's projections reduced
        g ← Tactic.dsimpStateEq g hNew
        setGoals [g]
        return goals
  return goals

/-- Step an effectful instruction, proving it with `runTactics`; with `resolveFirst`, the written
value's reads resolved before the state is sealed (a call's result, which reads the old state). -/
def runStep (args : StepArgs) (runTactics : Syntax) (resolveFirst := false) : TacticM Unit :=
  focus do
    Tactic.ensureStateEq
    withMainContext do
        let (g, goal) ← getGoalType
        let inState := (← getRunBodyFrom goal).state
        let ⟨runGoal, main⟩ ← rewriteStep g ``BasicBlock.runBodyFrom_step_of_run
        let some runGoal ← dsimpMlirInstr? runGoal | throwError "Could not `dsimp` runGoal"
        let_expr Eq _ op_run _ :=
          ←
            instantiateMVars
                (← runGoal.getType) | throwError m!"{← runGoal.getType} not an equality"
        unless op_run.getAppNumArgs >= 2 do
          throwError m!"Run goal lhs {op_run} not application with env and state"
        let operation := op_run.appFn!.appFn!
        setGoals [runGoal] -- Makes the following simp work
        let resultValue ←
          simpValue args.only args.simpArgs operation (← getRunBodyFrom goal).env args.expand
        let runGoal ← replaceBySimp runGoal operation resultValue
        -- Apply runTactics to runGoal
        setGoals [runGoal]
        evalTactic runTactics
        unless (← getUnsolvedGoals).isEmpty do
          throwError "`step_impure =>` left `insn` unsolved"
        setGoals [main]
        if resolveFirst then
          resolveWrittenValue args
        let goals ← sealStep inState
        finishStep args
        -- the consumed facts last: the value may read through them. Their ids first: once a
        -- `clear` assigns the main goal, its context is gone
        withMainContext do
            let hs ← args.consumed.mapM getFVarId
            let mut g ← getMainGoal
            for h in hs do
              g ← g.clear h
            replaceMainGoal [g]
        setGoals (goals.toList ++ (← getGoals))

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

/-- A load or store, closed with `lem`: the pointer's `Fits` by `mem_fact`, the value by
`dsimp`. -/
def runAccess (args : StepArgs) (lem : Ident) : TacticM Unit := do
  runStep args
      (←
        `(tacticSeq|
        expect_values
        exact $lem (by first | mem_fact | simp_all) (by dsimp; try simp; rfl)))

@[tactic stepLoad]
def evalStepLoad : Tactic := fun stx => do
  -- the pointer keeps the values named with `with`, as the facts about it do
  runAccess (StepArgs.parse stx[1] stx[2] stx[3] mkNullNode (named := true)) (mkCIdent ``run_load)

@[tactic stepStore]
def evalStepStore : Tactic := fun stx => do
  runAccess (StepArgs.parse stx[1] mkNullNode stx[2] mkNullNode) (mkCIdent ``run_store)

@[tactic stepMemcpy]
def evalStepMemcpy : Tactic := fun stx => do
  runStep (StepArgs.parse stx[1] mkNullNode stx[2] mkNullNode)
      (←
        `(tacticSeq|
        expect_values
        exact
            run_memcpy (by rfl) (by first | mem_fact | simp_all) (by first | mem_fact | simp_all)
              (by first | mem_fact | simp_all)))

@[tactic stepMemset]
def evalStepMemset : Tactic := fun stx => do
  runStep (StepArgs.parse stx[1] mkNullNode stx[2] mkNullNode)
      (←
        `(tacticSeq|
        expect_values
        exact run_memset (by rfl) (by first | mem_fact | simp_all)))

end InstructionSpecific

end

end MLIR
