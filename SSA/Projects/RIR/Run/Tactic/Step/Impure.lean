module

public import SSA.Projects.RIR.Semantics.Func
public import SSA.Projects.RIR.Run.Memory
public meta import SSA.Projects.RIR.Run.BasicBlock
public meta import SSA.Projects.RIR.Run.Tactic.Env
public meta import SSA.Projects.RIR.Run.Tactic.State
public meta import SSA.Projects.RIR.Run.Tactic.Seal
public meta import SSA.Projects.RIR.Run.Tactic.Step.Common
public meta import SSA.Projects.RIR.Run.Tactic.Step.Syntax
public meta import Lean.Elab.Tactic
public import SSA.Projects.RIR.Run.Tactic.Trace

namespace LeanMLIR.RIR

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
unproved ones are returned as goals) and dropping the `consumed` ones. -/
def sealStep (inState : Expr) (consumed : Array Ident) : TacticM (Array MVarId) := do
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
        -- not the new state's own facts (its reads may mention `inState` in their values)
        -- not the new state's own facts (its reads may mention `inState` in their values), nor
        -- facts about `inState` only as `inState.allocaPtr`: a fixed pointer, not the state
        let allocaPtr ← mkAppM ``GlobalState.allocaPtr #[inState]
        let preserveHyps ←
          (← hypsMentioning inState (except := #[hS', hS])).filterM fun h => do
              let ty ← instantiateMVars (← h.getType)
              let rest :=
                ty.replace fun t => if t == allocaPtr then some (mkConst ``Unit.unit) else none
              return !ty.containsFVar S' && inState.occurs rest
        let mut g ← getMainGoal
        let mut goals := #[]
        let hSId := mkIdent (← hS.getUserName)
        let hS'Id := mkIdent (← hS'.getUserName)
        let mlirMem := mkIdent `mlir_mem
        for hyp in preserveHyps do
          let decl ← hyp.getDecl
          -- P S ↦ P S'
          let newTy := (← kabstract (← instantiateMVars decl.type) inState).instantiate1 (.fvar S')
          let pg ← mkFreshExprSyntheticOpaqueMVar newTy (tag := decl.userName) -- New goal
          let (_, g') ← (← g.assert decl.userName newTy pg).intro1P
          g ← g'.clear hyp
          -- fast path, without elaborating tactics: `P S`, one or two transport lemmas to
          -- `P (new state)`, then `hS'` back
          let fast? ←
            observing? do
                let some (_, _, new) := (← instantiateMVars (← hS'.getType)).eq? | failure
                let motive ←
                  withLocalDeclD `s (← inferType inState) fun x => do
                      mkLambdaFVars #[x]
                          ((← kabstract (← instantiateMVars decl.type) inState).instantiate1 x)
                -- `P S`, keyed as is, and `dsimp`ed like the new state
                let key ← instantiateMVars decl.type
                let facts : Std.HashMap Expr Expr :=
                  (({} : Std.HashMap Expr Expr).insert key (.fvar hyp)).insert
                    (← Tactic.dsimpState key) (.fvar hyp)
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
        let hNew := (fs.get hS').fvarId!
        g ← g.rename hNew `hS
        -- the substituted old state's projections reduced
        g ←
          g.withContext do
              let some (_, l, r) := (← instantiateMVars (← hNew.getType)).eq? | return g
              g.replaceLocalDeclDefEq hNew (← mkEq l (← Tactic.dsimpState r))
        setGoals [g]
        return goals
  return goals

/-- Step a pure instruction, extending the env with the new value -/
def runStepImpure (value : EnvName) (hyp : EnvName) (only : Bool) (simpArgs : Syntax)
    (expand : Bool) (runTactics : Syntax) (consumed : Array Ident) (tag : Bool) : TacticM Unit :=
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
        let goals ← sealStep inState #[]
        finishStep value hyp only simpArgs expand tag
        -- the consumed facts last: the value may read through them
        withMainContext do
            let mut g ← getMainGoal
            for h in consumed do
              g ← g.clear (← getFVarId h)
            replaceMainGoal [g]
        setGoals (goals.toList ++ (← getGoals))

/-- Step an effectful instruction, proving it with `tac`. -/
def runStep (args : StepArgs) (tac : Syntax) : TacticM Unit :=
  runStepImpure args.value args.hyp args.only args.simpArgs args.expand tac args.consumed args.tag

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
    let some pf ←
      Tactic.fitsProof? (← Tactic.splitConjunctedFacts) m p w | throwError "no fact `{← g.getType}`"
    g.assign pf
    replaceMainGoal []

/-- Close `a ≠ b` (or `¬a = b`) from the facts: either way round, or by a `Nodup`. -/
elab "ne_fact" : tactic =>
  withMainContext do
    let g ← getMainGoal
    let ty := (← instantiateMVars (← g.getType)).cleanupAnnotations
    let some (a, b) :=
      ty.ne?.map (fun (_, a, b) => (a, b)) <|> (ty.not?.bind (·.eq?)).map fun (_, a, b) => (a, b)
      | throwError "goal is not `≠`"
    let some pf ← Tactic.neProof? (← Tactic.splitConjunctedFacts) a b | throwError "no `≠` fact"
    g.assign (mkExpectedPropHint pf ty)
    replaceMainGoal []

/-- Close `(Range.of p v).Disjoint (Range.of q w)` from the facts (distinct blocks, offsets). -/
elab "disjoint_fact" : tactic =>
  withMainContext do
    let g ← getMainGoal
    let_expr Range.Disjoint a b :=
      ← instantiateMVars (← g.getType) | throwError "goal is not `Disjoint`"
    let_expr Range.of p v := a | throwError "goal is not `Disjoint` of two ranges"
    let_expr Range.of q w := b | throwError "goal is not `Disjoint` of two ranges"
    let some pf ←
      Tactic.disjointProof? (← Tactic.splitConjunctedFacts) p v q
          w | throwError "no disjointness from the facts"
    g.assign pf
    replaceMainGoal []

@[tactic stepLoad]
def evalStepLoad : Tactic := fun stx => do
  let args := StepArgs.parse stx[1] stx[2] stx[3] mkNullNode (named := true)
  -- the pointer keeps the values named with `with`, as the facts about it do
  runStepImpure args.value args.hyp args.only args.simpArgs args.expand
      (←
        `(tacticSeq|
        expect_values
        exact run_load (by first | fits_fact | simp_all) (by dsimp; try simp; rfl)))
      args.consumed args.tag

@[tactic stepStore]
def evalStepStore : Tactic := fun stx => do
  let args := StepArgs.parse stx[1] mkNullNode stx[2] mkNullNode
  runStepImpure args.value args.hyp args.only args.simpArgs args.expand
      (←
        `(tacticSeq|
        expect_values
        exact run_store (by first | fits_fact | simp_all) (by dsimp; try simp; rfl)))
      args.consumed args.tag

@[tactic stepMemcpy]
def evalStepMemcpy : Tactic := fun stx => do
  let args := StepArgs.parse stx[1] mkNullNode stx[2] mkNullNode
  runStepImpure args.value args.hyp args.only args.simpArgs args.expand
      (←
        `(tacticSeq|
        expect_values
        exact
            run_memcpy (by rfl) (by first | disjoint_fact | simp_all)
              (by first | fits_fact | simp_all) (by first | fits_fact | simp_all)))
      args.consumed args.tag

@[tactic stepMemset]
def evalStepMemset : Tactic := fun stx => do
  let args := StepArgs.parse stx[1] mkNullNode stx[2] mkNullNode
  runStepImpure args.value args.hyp args.only args.simpArgs args.expand
      (←
        `(tacticSeq|
        expect_values
        exact
            run_memset (by rfl) (by first | fits_fact | simp_all)))
      args.consumed args.tag

end InstructionSpecific

end

end LeanMLIR.RIR
