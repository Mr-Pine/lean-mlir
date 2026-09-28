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
                -- fast path, without elaborating tactics: `P S₀chain` from `hS`, one or two
                -- transport lemmas to `P (new state)`, then `hS'` back
                let fast? ←
                  observing? do
                      let some (_, _, chain) := (← instantiateMVars (← hS.getType)).eq? | failure
                      let some (_, _, new) := (← instantiateMVars (← hS'.getType)).eq? | failure
                      let motive ←
                        withLocalDeclD `s (← inferType inState) fun x => do
                            mkLambdaFVars #[x]
                                ((← kabstract (← instantiateMVars decl.type) inState).instantiate1
                                  x)
                      let h₀ ← mkEqNDRec motive (.fvar hyp) (.fvar hS)
                      -- keyed as is, and `dsimp`ed like the new state
                      let key ← instantiateMVars (motive.beta #[chain])
                      let facts : Std.HashMap Expr Expr :=
                        (({} : Std.HashMap Expr Expr).insert key h₀).insert
                          (← Tactic.dsimpState key) h₀
                      let some pf ←
                        Tactic.transportWith facts (← labelled `mlir_transport) 2
                            (motive.beta #[new]) | failure
                      mkEqNDRec motive pf (← mkEqSymm (.fvar hS'))
                if let some pf := fast? then
                  pg.mvarId!.assign pf
                  continue
                setGoals [pg.mvarId!]
                let hId := mkIdent decl.userName
                evalTactic
                    (←
                      `(tactic|
                          first
                          -- fast path: the old fact and one transport lemma; the context
                          -- (`*`) only when a lemma needs a side fact
                          | ( subst $hS'Id:ident $hSId:ident
                              solve_by_elim (transparency := .reducible) only [$hId:ident] using
                                $(mkIdent `mlir_transport):ident)
                          | ( subst $hS'Id:ident $hSId:ident
                              solve_by_elim (transparency := .reducible) only [$hId:ident, *] using
                                $(mkIdent `mlir_transport):ident)
                          -- a chain of transports, still at reducible transparency
                          | ( subst $hS'Id:ident $hSId:ident
                              transport_fact)
                          | ( subst $hSId:ident
                              try simp at $hId:ident
                              simp [$mlirMem:ident, $hS'Id:ident, $hId:ident]
                              done)
                          | (subst $hSId:ident $hS'Id:ident; assumption)
                          | skip))
                unless ← pg.mvarId!.isAssigned do
                  goals := goals.push pg.mvarId!
              -- substitute, not clear: a written value may mention the old state (`alloca`).
              -- `substCore` reverts and reintroduces what follows `S`, so `S'`/`hS'` get new ids
              let (fs, g') ← substCore g hS (symm := false)
              g := g'
              g ← g.rename (fs.get S').fvarId! `S
              g ← g.rename (fs.get hS').fvarId! `hS
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

/-- Close `Fits m p w` by a fact, or a conjunct of one, with the same `m` and `p`. -/
elab "fits_fact" : tactic =>
  withMainContext do
    let g ← getMainGoal
    let_expr Fits m p w := ← instantiateMVars (← g.getType) | throwError "goal is not `Fits`"
    for (pf, ty) in ← Tactic.splitConjunctedFacts do
      let_expr Fits m' p' w' := ty | continue
      -- `isDefEq` for `w`: the goal's is `(Ty.bv 64).width`
      if m' == m && p' == p && (← withNewMCtxDepth (isDefEq w' w)) then
        g.assign pf
        replaceMainGoal []
        return
    throwError "no fact `{← g.getType}`"

@[tactic stepLoad]
def evalStepLoad : Tactic := fun stx => do
  runStep (StepArgs.parse stx[1] stx[2] stx[3] mkNullNode (named := true))
      (←
        `(tacticSeq|
        expect_values
        exact run_load (by first | fits_fact | simp_all) (by dsimp; try simp; rfl)))

@[tactic stepStore]
def evalStepStore : Tactic := fun stx => do
  runStep (StepArgs.parse stx[1] mkNullNode stx[2] mkNullNode)
      (←
        `(tacticSeq|
        expect_values
        exact run_store (by first | fits_fact | simp_all) (by dsimp; try simp; rfl)))

end InstructionSpecific

end

end MLIR
