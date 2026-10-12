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

/-- `step_impure` for a `load`, closing the instruction with `run_load`; of a pointer, with
`run_loadPtr`, its value the pointer stored there (`S.mem.loadPtr p`, by a read fact). -/
syntax (name := stepLoad) "step_load" stepSimpArgs (stepNames)? (stepConsuming)? : tactic

/-- `step_impure` for a `memcpy`, closing the instruction with `run_memcpy`, or with `run_memcpyDef`
for a source only partly known. -/
syntax (name := stepMemcpy) "step_memcpy" stepSimpArgs (stepConsuming)? : tactic

/-- `step_impure` for a `memmove`, closing the instruction with `run_memmove`, or `run_memmoveDef`
for a source only partly known. -/
syntax (name := stepMemmove) "step_memmove" stepSimpArgs (stepConsuming)? : tactic

/-- `step_impure` for a `memset`, closing the instruction with `run_memset`. -/
syntax (name := stepMemset) "step_memset" stepSimpArgs (stepConsuming)? : tactic

/-- `step_impure` for a `store`, closing the instruction with `run_store`; of a pointer, with
`run_storePtr`, which records it: `hread_p : S.mem.loadPtr p = .value q` after. -/
syntax (name := stepStore) "step_store" stepSimpArgs (stepConsuming)? : tactic

/-- `step_impure` for a `lifetime.start` or `lifetime.end`: the state's memory as
`S.mem.lifetimeStart p` or `S.mem.lifetimeEnd p`; the facts about `p`'s object it does not carry
are dropped. -/
syntax (name := stepLifetime) "step_lifetime" stepSimpArgs : tactic

/-- `step_impure` for an `assume`: its condition, resolved by the simp arguments, must be `1`. -/
syntax (name := stepAssume) "step_assume" stepSimpArgs : tactic

/-- Seal the goal's new state as `S` with `hS`, carrying the facts about `inState` over (the
unproved ones are returned as goals; `consumed` ones, and at a lifetime marker those mentioning its
pointer `about?`, two lemmas deep or not at all; at a marker, the rest not carried dropped). Also
returned: the names fresh facts took over from the facts they supersede. -/
def sealStep (inState : Expr) (consumed : Array FVarId := #[]) (about? : Option Expr := none) :
    TacticM (Array MVarId × Array Name) := do
  -- the new state's memory facts, about it as a term over `inState`, then generalized with it
  let (mem, olds, renamed) ←
    withMainContext do
        let (g, goal) ← getGoalType
        let (hyps, olds, g, renamed) ← Tactic.memFactsOf g inState (← getRunBodyFrom goal).state
        replaceMainGoal [g]
        return (hyps, olds, renamed)
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
        let fc ← Tactic.FactCtx.build
        let locals ← Tactic.localImplications
        let new? := (← instantiateMVars (← hS'.getType)).eq?.map (·.2.2)
        -- the marker's pointer and the named slot `x = q` it is, either way round
        let markerPtrs ←
          match about? with
          | none => pure #[]
          | some q =>
            do
              let eqs ← Tactic.localEqs
              let slots := eqs.filter fun e => e.lhs == q && e.rhs.isAppOf ``GlobalState.slot
              pure (#[q] ++ (eqs.filter (·.rhs == q)).map (·.lhs) ++ slots.map (·.rhs))
        for hyp in preserveHyps do
          let decl ← hyp.getDecl
          -- `P S` as `fun s => P s`, then `P S'`
          let key ← instantiateMVars decl.type
          let motive := .lam `s (← inferType inState) (← kabstract key inState) .default
          let newTy := motive.beta #[.fvar S']
          -- about the object a lifetime marker restarts or ends (by its pointer, or a slot named
          -- for it): rarely carried, so not searched deep
          let aboutMarker := markerPtrs.any fun q => (key.find? (· == q)).isSome
          -- `P (new state)` carried from `P S`, then `hS'` back; else left open
          let pf? ←
            observing? do
                let some new := new? | failure
                let some pf ←
                  Tactic.carryFact fc locals (.fvar hyp) key (motive.beta #[new]) (deep :=
                      !consumed.contains hyp && !aboutMarker) | failure
                mkEqNDRec motive pf (← mkEqSymm (.fvar hS'))
          -- a consumed fact not carried stays about the old state, to be cleared after the step;
          -- an equation (`S.mem.eraseFrom b = m`) stays about it, true there, rather than a goal
          if pf?.isNone && consumed.contains hyp then
            continue
          -- about the object a lifetime marker restarts or ends: gone with its old lifetime
          if pf?.isNone && aboutMarker then
            trace[rir] m!"fact {decl.userName} dropped at the lifetime marker"
            g ← g.tryClear hyp
            continue
          if pf?.isNone && key.isEq then
            trace[rir] m!"fact {decl.userName} kept about the state before the step"
            continue
          -- past a lifetime marker, a fact not carried is dropped rather than a goal
          if pf?.isNone && about?.isSome then
            trace[rir] m!"fact {decl.userName} not carried past the lifetime marker: dropped"
            g ← g.tryClear hyp
            continue
          let pg ← mkFreshExprSyntheticOpaqueMVar newTy (tag := decl.userName) -- New goal
          let (_, g') ← (← g.assert decl.userName newTy pg).intro1P
          g ← g'.clear hyp
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
        -- the substituted old state's projections reduced, its writes merged with the new ones
        g ← Tactic.dsimpStateEq g hNew
        g ← Tactic.mergeStateEq g hNew
        setGoals [g]
        return goals
  return (goals, renamed)

/-- Step an effectful instruction, proving it with `runTactics`; with `resolveFirst`, the written
value's reads resolved before the state is sealed (a call's result, which reads the old state). -/
def runStepAt (args : StepArgs) (runTactics : Syntax) (resolveFirst := false) : TacticM Unit :=
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
        -- a lifetime marker's pointer, whose object's facts it ends
        let op := resultValue.expr
        let marker := op.isAppOf ``Operation.lifetimeStart || op.isAppOf ``Operation.lifetimeEnd
        if marker then
          let arg := op.appArg!
          unless arg.isAppOf ``PoisonOr.value || arg.isAppOf ``PoisonOr.poison do
            throwError "lifetime marker: its pointer operand is not known to be a value or \
              poison{indentExpr arg}\na register the env does not hold?"
        let about? := do
          guard marker
          let_expr PoisonOr.value _ q := op.appArg! | none
          return q
        -- Apply runTactics to runGoal
        setGoals [runGoal]
        evalTactic runTactics
        unless (← getUnsolvedGoals).isEmpty do
          throwError "`step_impure =>` left `insn` unsolved"
        setGoals [main]
        if resolveFirst then
          resolveWrittenValue args
        -- the consumed facts there before the step: carried only if cheaply, never as a goal
        let before ←
          withMainContext do
              let lctx ← getLCtx
              return args.consumed.filterMap fun h => (lctx.findFromUserName? h.getId).map (h, ·)
        let (goals, renamed) ← sealStep inState (before.map (·.2.fvarId)) about?
        finishStep args
        -- the consumed facts last: the value may read through them. By name: the seal renews ids,
        -- and a fact may be the step's own (a read-back). One there before may be gone with its
        -- value. Their ids first: once a `clear` assigns the main goal, its context is gone
        withMainContext do
            let lctx ← getLCtx
            let mut hs := #[]
            -- not a fresh fact that took over a consumed one's name
            for h in args.consumed.filter (!renamed.contains ·.getId) do
              match lctx.findFromUserName? h.getId with
              | some d =>
                hs := hs.push d.fvarId
              | none =>
                unless before.any (·.1.getId == h.getId) do
                  discard <| getFVarId h
            let mut g ← getMainGoal
            for h in hs do
              g ← g.clear h
            replaceMainGoal [g]
        setGoals (goals.toList ++ (← getGoals))

/-- `runStepAt` from recursion depth `0` (`Tactic.atStepDepth`). -/
def runStep (args : StepArgs) (runTactics : Syntax) (resolveFirst := false) : TacticM Unit :=
  Tactic.atStepDepth (runStepAt args runTactics resolveFirst)

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

/-- Fail unless the instruction's operation (`load`, `store`) is at pointer type: the pointer run
lemmas are tried only there, a mismatched one unfolding the operation. -/
elab "expect_ptr" : tactic =>
  withMainContext do
    let_expr Eq _ lhs _ := ← instantiateMVars (← getMainTarget)
      | throwError "expected an equation, got{indentExpr (← getMainTarget)}"
    let op := lhs.appFn!.appFn!
    let some τ ← op.getAppArgs.findM? fun a => return (← inferType a).isConstOf ``Ty
      | throwError "no type argument in{indentExpr op}"
    unless (← whnfR τ).isConstOf ``Ty.ptr do
      throwError "not at pointer type:{indentExpr τ}"

@[tactic stepLoad]
def evalStepLoad : Tactic := fun stx => do
  -- the pointer keeps the values named with `with`, as the facts about it do; its `Fits` by
  -- `mem_fact`, the value by `dsimp`
  runStep (StepArgs.parse stx[1] stx[2] stx[3] mkNullNode (named := true))
      (←
        `(tacticSeq|
        expect_values
        first
        | expect_ptr; exact run_loadPtr (by mem_fact)
        | exact run_load (by first | mem_fact | simp_all) (by dsimp; try simp; rfl)))

@[tactic stepStore]
def evalStepStore : Tactic := fun stx => do
  -- the pointer's `Room` by `mem_fact`, the value's bits by `dsimp`, its type's padding by `decide`
  runStep (StepArgs.parse stx[1] mkNullNode stx[2] mkNullNode)
      (←
        `(tacticSeq|
        expect_values
        first
        | expect_ptr; exact run_storePtr (by mem_fact)
        | exact
            run_store (by first | mem_fact | simp_all) (by dsimp; try simp; rfl)
              (by first | decide | simp_all)))

/-- Close a lifetime marker's run goal by its own lemma: a mismatched one unfolds both markers into
the block map before failing. -/
elab "lifetime_run" : tactic =>
  withMainContext do
    let_expr Eq _ lhs _ := ← instantiateMVars (← getMainTarget)
      | throwError "expected an equation, got{indentExpr (← getMainTarget)}"
    let op := lhs.appFn!.appFn!
    let poison := op.appArg!.isAppOf ``PoisonOr.poison
    let lem :=
      if op.isAppOf ``Operation.lifetimeStart then
        if poison then ``run_lifetimeStart_poison else ``run_lifetimeStart
      else if poison then ``run_lifetimeEnd_poison else ``run_lifetimeEnd
    evalTactic (← `(tactic| exact $(mkIdent lem)))

/-- Step a `lifetime.start` or `lifetime.end`. -/
def runLifetimeStep (args : StepArgs) : TacticM Unit := do
  runStep args (← `(tacticSeq| lifetime_run))

/-- Step an `assume`. -/
def runAssumeStep (args : StepArgs) : TacticM Unit := do
  runStep args (← `(tacticSeq| exact run_assume))

@[tactic stepLifetime]
def evalStepLifetime : Tactic := fun stx =>
  runLifetimeStep (StepArgs.parse stx[1] mkNullNode mkNullNode mkNullNode)

@[tactic stepAssume]
def evalStepAssume : Tactic := fun stx =>
  runAssumeStep (StepArgs.parse stx[1] mkNullNode mkNullNode mkNullNode)

@[tactic stepMemcpy]
def evalStepMemcpy : Tactic := fun stx => do
  runStep (StepArgs.parse stx[1] mkNullNode stx[2] mkNullNode)
      (←
        `(tacticSeq|
        expect_values
        first
        | exact run_memcpy (by rfl) (by first | mem_fact | simp_all)
            (by first | mem_fact | simp_all) (by mem_fact)
        -- a source not known throughout: its definedness copied
        | exact run_memcpyDef (by rfl) (by first | mem_fact | simp_all)
            (by first | mem_fact | simp_all) (by first | mem_fact | simp_all)))

@[tactic stepMemmove]
def evalStepMemmove : Tactic := fun stx => do
  runStep (StepArgs.parse stx[1] mkNullNode stx[2] mkNullNode)
      (←
        `(tacticSeq|
        expect_values
        first
        | exact run_memmove (by rfl) (by first | mem_fact | simp_all) (by mem_fact)
        -- a source not known throughout: its definedness copied
        | exact run_memmoveDef (by rfl) (by first | mem_fact | simp_all)
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
