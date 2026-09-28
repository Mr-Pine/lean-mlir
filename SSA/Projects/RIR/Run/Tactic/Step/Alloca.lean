module

public meta import SSA.Projects.RIR.Run.Tactic.Step.Impure
public meta import SSA.Projects.RIR.Run.Tactic.Memory
public import SSA.Projects.RIR.Run.Memory

namespace LeanMLIR.RIR

open Lean Elab Tactic Meta

public meta section

/-- `step_impure` for an `alloca`, closing the instruction with `run_alloca`. Before the step, each
pointer `q` with a `Fits` fact about the state gets `hq_fresh : q.id ≠ S.allocaPtr.id` and its
symmetric form, with `S` written as its `hS` right-hand side, so the facts outlive the state. -/
syntax (name := stepAlloca) "step_alloca" (stepNames)? (stepConsuming)? : tactic

/-- Add the freshness facts for the next `alloca` of the main goal's state. -/
def addAllocaFreshness : TacticM Unit :=
  withMainContext do
    let (g, goal) ← Tactic.getGoalType
    let S := (← Tactic.getRunBodyFrom goal).state
    let hS ← Tactic.findEqWithLhs S m!"`{S} = _`"
    let some (_, _, rhs) := (← instantiateMVars (← hS.getType)).eq? | throwError "not an equation"
    let wfTy ← mkAppM ``GlobalState.WF #[S]
    let some hwf ←
      (← getLCtx).findDeclM? fun d => do
          if !d.isImplementationDetail && (← withReducible (isDefEq d.type wfTy)) then
            return some d.toExpr
          return none | throwError "`step_alloca`: no hypothesis `{wfTy}`"
    let memS ← mkAppM ``GlobalState.mem #[S]
    -- `fun x => q.id ≠ x.allocaPtr.id`, to move the fact from `S` to `rhs`
    let motive (q : Expr) : MetaM Expr :=
      withLocalDeclD `x (mkConst ``GlobalState) fun x => do
        mkLambdaFVars #[x]
            (←
              mkAppM ``Ne
                  #[← mkAppM ``Pointer.id #[q],
                    ← mkAppM ``Pointer.id #[← mkAppM ``GlobalState.allocaPtr #[x]]])
    let mut seen : Array Expr := #[]
    let mut hyps : Array Hypothesis := #[]
    for (pf, ty) in ← Tactic.splitConjunctedFacts do
      let_expr Fits m q _ := ty | continue
      unless q.isFVar && !seen.contains q do
        continue
      unless ← withReducible (isDefEq m memS) do
        continue
      seen := seen.push q
      let ne ← mkAppM ``GlobalState.ne_allocaPtr_of_fits #[hwf, pf]
      let fresh ← mkEqNDRec (← motive q) ne (mkFVar hS)
      let freshTy ← instantiateMVars (← inferType fresh)
      let name := s!"h{(← q.fvarId!.getUserName).toString}_fresh"
      hyps := hyps.push { userName := .mkSimple name, type := freshTy, value := fresh }
      hyps :=
        hyps.push
          { userName := .mkSimple (name ++ "'"),
            type :=
              ←
                mkAppM ``Ne
                    #[(← instantiateMVars freshTy).appArg!,
                      (← instantiateMVars freshTy).appFn!.appArg!],
            value := ← mkAppM ``Ne.symm #[fresh] }
    let (_, g) ← g.assertHypotheses hyps
    replaceMainGoal [g]

@[tactic stepAlloca]
def evalStepAlloca : Tactic := fun stx => do
  addAllocaFreshness
  runStep (StepArgs.parse mkNullNode stx[1] stx[2] mkNullNode) (← `(tacticSeq| exact run_alloca))

end

end LeanMLIR.RIR
