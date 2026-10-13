module

public meta import MLIR.Run.Tactic.Step.Impure
public meta import MLIR.Run.Tactic.Memory
public import MLIR.Run.Memory

namespace MLIR

open Lean Elab Tactic Meta

public meta section

/-- `step_impure` for an `alloca`, closing the instruction with `run_alloca`. Each pointer `q` with
an `InBounds`, `Room` or `Fits` fact gets `hq_ne_x : q.id ≠ x.id` for the new slot `x`; the slot has
`Room` for its bytes (`hx_room`), or, dead until a `lifetime.start`, `InBounds` (`hx_bounds`);
facts name the slot `x`, not the state's `allocaPtr`. -/
syntax (name := stepAlloca) "step_alloca" (stepNames)? (stepConsuming)? : tactic

/-- `q.id ≠ S.allocaPtr.id` for each pointer `q` with a memory fact about the state `S`, before
the tactic `tac` allocates `S`'s next block; not for the named slots of the new slot's base, apart
from it by index (`neSlots?`), unless `slots` (a global's block: reads past its masked store need
the fact). -/
def addAllocaFreshness (tac : String) (slots := false) : TacticM Unit := do
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
      let named ← Tactic.namedSlots (← Tactic.localEqs)
      let mut seen : Array Expr := #[]
      let mut hyps : Array Hypothesis := #[]
      for (pf, ty) in ← Tactic.splitConjunctedFacts do
        let some (k, m, q, _) := Tactic.memPred? ty | continue
        unless q.isFVar && !seen.contains q && m == memS do
          continue
        seen := seen.push q
        if let some (s, _) := named[q]? then
          if !slots && base == some s.appFn!.appArg! then
            continue
        let ne ← mkAppM ``GlobalState.ne_allocaPtr_of_inBounds #[hwf, ← Tactic.weakenMemPred pf k 0]
        hyps :=
          hyps.push
            { userName := .mkSimple s!"h{(← q.fvarId!.getUserName).toString}_ne",
              type := ← inferType ne, value := ne }
      let (_, g') ← g.assertHypotheses hyps
      replaceMainGoal [g']

/-- After the `alloca`: the slot `hx : x = p` (`p` an `allocaPtr`) as `x = b.slot k` (`slotPtr?`),
and the facts about `p` stated about `x`, named after it (`hx_fits_8` for `x.add 8`). -/
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
    -- the slot's pointer as the facts spell it: `p`, or another state term with its counter
    -- (`{ alloc := s.alloc, mem := … }.allocaPtr` after an earlier global's block)
    let slot := Tactic.slotPtr? p
    let spelled ← g.withContext do
        let ptrs ← IO.mkRef #[p]
        for d in ← getLCtx do
          if d.isImplementationDetail || d.fvarId == hx then
            continue
          (← instantiateMVars d.type).forEachWhere (·.isAppOfArity ``GlobalState.allocaPtr 1)
            fun q => do
              if slot.isSome && Tactic.slotPtr? q == slot then
                ptrs.modify fun a => if a.contains q then a else a.push q
        ptrs.get
    for q in spelled do
      let pfq ← g.withContext do mkExpectedPropHint pf <$> mkEq q (.fvar x)
      for h in ← g.withContext (Tactic.hypsMentioning q (except := #[hx])) do
        let some d := (← g.getDecl).lctx.find? h | continue
        let ty ← instantiateMVars d.type
        -- the state's equation keeps the slot as its state spells it
        if ty.isEq && ty.getArg! 0 == mkConst ``GlobalState then
          continue
        let motive ← g.withContext (Tactic.motiveOver ty q (mkConst ``Pointer))
        let ty' := motive.beta #[.fvar x]
        -- a range inside the block (a global's member) after its offset
        let name ←
          match Tactic.memPred? ty with
          | some (k, _, r, _) =>
            do
              let at_ ←
                match r.app2? ``Pointer.add with
                | some (_, off) => pure ((← getBitVecValue? off).map fun ⟨_, o⟩ => s!"_{o.toNat}")
                | none => pure none
              pure ((`h).appendAfter
                s!"{xName}_{#["bounds", "room", "fits", "live"][k]!}{at_.getD ""}")
          | none => pure (d.userName.appendAfter s!"_{xName}")
        let (_, g') ←
          (← g.assert name ty' (← g.withContext (mkEqNDRec motive d.toExpr pfq))).intro1P
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

end MLIR
