module

public meta import MLIR.Run.Tactic.Step.Impure
public meta import MLIR.Run.Tactic.Memory
public import MLIR.Run.Memory

namespace MLIR

open Lean Elab Tactic Meta

public meta section

/-- `step_impure` for an `alloca`, closing the instruction with `run_alloca`. Each pointer `q` with
a `Fits` fact gets `hq_ne_x : q.id ≠ x.id` for the new slot `x`, and the slot `Fits` its bytes;
facts name the slot `x`, not the state's `allocaPtr`. -/
syntax (name := stepAlloca) "step_alloca" (stepNames)? (stepConsuming)? : tactic

/-- `q.id ≠ S.allocaPtr.id` for each pointer `q` with a `Fits` fact about the state `S`, before
the `alloca` of `S`'s next slot. -/
def addAllocaFreshness : TacticM Unit := do
  Tactic.ensureStateEq
  withMainContext do
      let (g, goal) ← Tactic.getGoalType
      let S := (← Tactic.getRunBodyFrom goal).state
      let wfTy ← mkAppM ``GlobalState.WF #[S]
      let some hwf ←
        (← getLCtx).findDeclM? fun d => do
            if !d.isImplementationDetail && (← withReducible (isDefEq d.type wfTy)) then
              return some d.toExpr
            return none | throwError "`step_alloca`: no hypothesis `{wfTy}`"
      let memS ← mkAppM ``GlobalState.mem #[S]
      let a ← mkAppM ``Pointer.id #[← mkAppM ``GlobalState.allocaPtr #[S]]
      -- the earlier slots' ids, newest first, in `hslots : [...].Nodup`
      let slots? ←
        (← getLCtx).findDeclRevM? fun d => do
            if d.isImplementationDetail || d.userName != `hslots then
              return none
            let_expr List.Nodup _ l := ← instantiateMVars d.type | return none
            return some (d, l)
      let slotIds := (slots?.bind fun (_, l) => l.listLit?.map (·.2)).getD []
      let mut seen : Array Expr := #[]
      let mut hyps : Array Hypothesis := #[]
      let mut slotNe : Array (Expr × Expr) := #[]
      for (pf, ty) in ← Tactic.splitConjunctedFacts do
        let_expr Fits m q _ := ty | continue
        unless q.isFVar && !seen.contains q && m == memS do
          continue
        seen := seen.push q
        let ne ← mkAppM ``GlobalState.ne_allocaPtr_of_fits #[hwf, pf]
        let qid ← mkAppM ``Pointer.id #[q]
        if slotIds.contains qid then
          slotNe := slotNe.push (qid, ne)
          continue
        hyps :=
          hyps.push
            { userName := .mkSimple s!"h{(← q.fvarId!.getUserName).toString}_ne",
              type := ← inferType ne, value := ne }
      -- the new slot's id on the front: apart from each earlier slot's, by its `Fits` fact
      let mut g := g
      if slotIds.all fun i => slotNe.any (·.1 == i) then
        let ty := mkConst ``BlockId
        let mut notMem ← mkAppOptM ``List.not_mem_nil #[ty, a]
        let mut l ← mkAppOptM ``List.nil #[ty]
        for i in slotIds.reverse do
          let some (_, ne) := slotNe.find? (·.1 == i) | unreachable!
          notMem ← mkAppM ``List.not_mem_cons_of_ne_of_not_mem #[← mkAppM ``Ne.symm #[ne], notMem]
          l ← mkAppM ``List.cons #[i, l]
        let old ←
          match slots? with
          | some (d, _) =>
            pure d.toExpr
          | none =>
            mkAppOptM ``List.nodup_nil #[ty]
        let pf ←
          mkAppM ``Iff.mpr
              #[← mkAppOptM ``List.nodup_cons #[ty, a, l], ← mkAppM ``And.intro #[notMem, old]]
        let (_, g') ←
          (← g.assert `hslots (← mkAppM ``List.Nodup #[← mkAppM ``List.cons #[a, l]]) pf).intro1P
        g := g'
        if let some (d, _) := slots? then
          g ← g.clear d.fvarId
      else
        for (_, ne) in slotNe do
          hyps := hyps.push { userName := `hslot_ne, type := ← inferType ne, value := ne }
      let (_, g') ← g.assertHypotheses hyps
      replaceMainGoal [g']

/-- After the `alloca`: the facts about the slot `hx : x = p` (`p` an `allocaPtr`) stated about
`x`, named after it. -/
def nameAllocaSlot : TacticM Unit :=
  withMainContext do
    let mut g ← getMainGoal
    -- the slot: the newest local `x` with `hx : x = _.allocaPtr`
    let some (x, hx, p) ←
      (← getLCtx).foldlM (init := none) fun acc d => do
          let some (_, .fvar x, p) := (← instantiateMVars d.type).consumeMData.eq? | return acc
          return if p.isAppOf ``GlobalState.allocaPtr then some (x, d.fvarId, p) else acc | return
    let xName ← x.getUserName
    -- the slot stays folded where memory steps take it, as the facts name it
    g ←
      g.replaceLocalDeclDefEq hx (Tactic.tagNamed (← instantiateMVars (← hx.getType)).consumeMData)
    let pf ← mkEqSymm (.fvar hx)
    for d in ← getLCtx do
      if d.isImplementationDetail || d.fvarId == hx then
        continue
      let ty ← instantiateMVars d.type
      unless (ty.find? (· == p)).isSome do
        continue
      let motive ←
        withLocalDeclD `y (mkConst ``Pointer) fun y => do
            mkLambdaFVars #[y] (ty.replace fun t => if t == p then some y else none)
      let ty' := motive.beta #[.fvar x]
      let name :=
        if ty.isAppOf ``Fits then (`h).appendAfter s!"{xName}_fits"
        else if d.userName == `hslots then `hslots else d.userName.appendAfter s!"_{xName}"
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
  addAllocaFreshness
  runStep (StepArgs.parse mkNullNode stx[1] stx[2] mkNullNode (named := true))
      (← `(tacticSeq| exact run_alloca))
  nameAllocaSlot

end

end MLIR
