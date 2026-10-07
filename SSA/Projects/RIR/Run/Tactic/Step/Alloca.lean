module

public meta import SSA.Projects.RIR.Run.Tactic.Step.Impure
public meta import SSA.Projects.RIR.Run.Tactic.Memory
public import SSA.Projects.RIR.Run.Memory

namespace LeanMLIR.RIR

open Lean Elab Tactic Meta

public meta section

/-- `step_impure` for an `alloca`, closing the instruction with `run_alloca`. Each pointer `q` with
a `Fits` fact gets `hq_ne_x : q.id ≠ x.id` for the new slot `x`, and the slot `Fits` its bytes;
facts name the slot `x`, not the state's `allocaPtr`. -/
syntax (name := stepAlloca) "step_alloca" (stepNames)? (stepConsuming)? : tactic

/-- `q.id ≠ S.allocaPtr.id` for each pointer `q` with a `Fits` fact about the state `S`, before
the tactic `tac` allocates `S`'s next block; not for the named slots of the new slot's base, apart
from it by index (`neSlots?`). -/
def addAllocaFreshness (tac : String) : TacticM Unit := do
  Tactic.ensureStateEq
  withMainContext do
      let (g, goal) ← Tactic.getGoalType
      let S := (← Tactic.getRunBodyFrom goal).state
      let wfTy ← mkAppM ``GlobalState.WF #[S]
      let some hwf ←
        withReducible (findLocalDeclWithType? wfTy) | throwError "`{tac}`: no hypothesis `{wfTy}`"
      let hwf := mkFVar hwf
      let memS ← mkAppM ``GlobalState.mem #[S]
      -- the new slot's base, through `S`'s equation
      let base := Tactic.counterBase? ((← Tactic.findLocalEq? S).elim S (·.rhs)) |>.map (·.1)
      let slots ← Tactic.namedSlots (← Tactic.localEqs)
      let mut seen : Array Expr := #[]
      let mut hyps : Array Hypothesis := #[]
      for (pf, ty) in ← Tactic.splitConjunctedFacts do
        let_expr Fits m q _ := ty | continue
        unless q.isFVar && !seen.contains q && m == memS do
          continue
        seen := seen.push q
        if let some (s, _) := slots[q]? then
          if base == some s.appFn!.appArg! then
            continue
        let ne ← mkAppM ``GlobalState.ne_allocaPtr_of_fits #[hwf, pf]
        hyps :=
          hyps.push
            { userName := .mkSimple s!"h{(← q.fvarId!.getUserName).toString}_ne",
              type := ← inferType ne, value := ne }
      let (_, g') ← g.assertHypotheses hyps
      replaceMainGoal [g']

/-- After the `alloca`: the slot `hx : x = p` (`p` an `allocaPtr`) as `x = b.slot k` (`slotPtr?`),
and the facts about `p` stated about `x`, named after it. -/
def nameAllocaSlot : TacticM Unit :=
  withMainContext do
    let mut g ← getMainGoal
    -- the slot: the newest local `x` with `hx : x = _.allocaPtr`
    let some e :=
      (← Tactic.localEqs).findRev? fun e =>
        e.lhs.isFVar && e.rhs.isAppOf ``GlobalState.allocaPtr | return
    let (x, hx, p) := (e.lhs.fvarId!, e.decl.fvarId, e.rhs)
    let xName ← x.getUserName
    -- as a slot, equal by `rfl`; it stays folded where memory steps take it, as the facts name it
    g ← g.replaceLocalDeclDefEq hx (Tactic.tagNamed (← mkEq e.lhs ((Tactic.slotPtr? p).getD p)))
    let pf ← mkEqSymm (.fvar hx)
    for h in ← Tactic.hypsMentioning p (except := #[hx]) do
      let d ← h.getDecl
      let ty ← instantiateMVars d.type
      let motive ← Tactic.motiveOver ty p (mkConst ``Pointer)
      let ty' := motive.beta #[.fvar x]
      let name :=
        if ty.isAppOf ``Fits then (`h).appendAfter s!"{xName}_fits"
        else d.userName.appendAfter s!"_{xName}"
      let (_, g') ← (← g.assert name ty' (← mkEqNDRec motive d.toExpr pf)).intro1P
      g ← g'.clear d.fvarId
    -- its offset, `0`: offsets into the slot (`x.add 24`) stay in range
    g ←
      g.withContext do
          let off := mkApp (mkConst ``GlobalState.allocaPtr_offset) p.appArg!
          let some (_, _, zero) := (← inferType off).eq? | return g
          let pf ← mkEqTrans (← mkCongrArg (mkConst ``Pointer.offset) (.fvar hx)) off
          let ty ← mkEq (← mkAppM ``Pointer.offset #[.fvar x]) zero
          return (← (← g.assert ((`h).appendAfter s!"{xName}_off") ty pf).intro1P).2
    replaceMainGoal [g]

@[tactic stepAlloca]
def evalStepAlloca : Tactic := fun stx => do
  addAllocaFreshness "step_alloca"
  runStep (StepArgs.parse mkNullNode stx[1] stx[2] mkNullNode (named := true))
      (← `(tacticSeq| exact run_alloca))
  nameAllocaSlot

end

end LeanMLIR.RIR
