module

public import SSA.Projects.RIR.Semantics.Func
public meta import SSA.Projects.RIR.Run.BasicBlock
public meta import SSA.Projects.RIR.Run.Tactic.Parse
public meta import SSA.Projects.RIR.Run.Tactic.Util
public meta import SSA.Projects.RIR.Run.Tactic.Env
public meta import SSA.Projects.RIR.Run.Tactic.Seal
public meta import SSA.Projects.RIR.Run.Tactic.State
public meta import SSA.Projects.RIR.Run.Tactic.Step.Impure
public meta import SSA.Projects.RIR.Run.Tactic.Step.Common
public meta import SSA.Projects.RIR.Run.Tactic.Step.Syntax
public meta import Lean.Elab.Tactic

namespace LeanMLIR.RIR

open Lean Elab Tactic Meta

public meta section

/-- `step_pattern using h` runs a run of instructions by a pattern lemma `h`, proved once over
registers: `h` concludes `(blk.runBodyFrom E pos S >>= g) = K` and takes

- a body fact `blk.body.drop pos = pat … ++ rest`, closed by unfolding: this fixes the registers,
  and fails when the instructions at the position are not the pattern;
- reads `E.read r = v`, closed through the env's writes (locals' definitions unfolded);
- decidable side conditions (the registers' `≠`), closed by `decide`;
- a continuation `∀ …, (blk.runBodyFrom E' pos' S >>= g) = K`, entered: its last write is named
  like `step_pure`'s, and its other binders (the pattern's dead intermediates) are sealed away. -/
syntax (name := stepPattern) "step_pattern" " using " stepLemma (stepNames)? : tactic

/-- `pf : lhs = v` into `lhs = v'`, each local of `v` with a definition `x = t` in context replaced by
`t`. -/
def unfoldLocals (v pf : Expr) : MetaM (Expr × Expr) := do
  let mut v := v
  let mut pf := pf
  for x in (collectFVars {} v).fvarIds do
    let some h ← Tactic.findLocalEq? (.fvar x) | continue
    pf ← mkEqTrans pf (← mkCongrArg (← mkLambdaFVars #[.fvar x] v) h.decl.toExpr)
    v := v.replaceFVar (.fvar x) h.rhs
  return (v, pf)

/-- Close a pattern read `E.read r = v`: the value the env's writes give `r`, as is or with locals'
definitions unfolded (a named constant against the pattern's); an argument's, from the args fact. -/
def closePatternRead (g : MVarId) : TacticM Unit :=
  g.withContext do
    let some (_, lhs, rhs) := (← instantiateMVars (← g.getType)).eq? | throwError "not a read"
    -- the register as the body fixed it: `(Dst.mk 24 _).i` to `24`
    let reg ←
      Meta.transform (lhs.getArg! 3) (post := fun e => do
          match_expr e with
          | Dst.i _ _ d =>
            let_expr Dst.mk _ _ i _ := d | return .continue
            return .done i
          | Dst.h _ _ d =>
            let_expr Dst.mk _ _ _ h := d | return .continue
            return .done h
          | _ =>
            return .continue)
    let read ← mkAppM ``Env.read #[lhs.getArg! 2, reg]
    -- an argument, or a register of an outer pattern (not a literal): by the step's simp passes
    let bySimp : TacticM Unit := do
      let r ← Tactic.simpValue true mkNullNode read (lhs.getArg! 2) false
      if r.expr == read then
        throwError "step_pattern: no value for the read{indentExpr read}\nthrough the writes; add \
        a fact `h : E.read %k = _` about the block's entry env"
      unless ← withReducible (isDefEq r.expr rhs) <||> withDefault (isDefEq r.expr rhs) do
        throwError "step_pattern: {lhs} is{indentExpr r.expr}\nnot{indentExpr rhs}"
      g.assign (mkExpectedPropHint (← r.getProof) (← mkEq lhs rhs))
    if reg.isAppOf ``Reg.arg then
      bySimp
      return
    let some (v, pf) ← Tactic.walkRead (lhs.getArg! 2) reg | bySimp
    -- reducible first: a default-transparency mismatch unfolds every definition before failing
    if ← withReducible (isDefEq v rhs) then
      g.assign (mkExpectedPropHint pf (← mkEq lhs rhs))
      return
    let (v', pf') ← unfoldLocals v pf
    unless ← withReducible (isDefEq v' rhs) <||> withDefault (isDefEq v' rhs) do
      throwError "step_pattern: {lhs} is{indentExpr v}\nnot{indentExpr rhs}"
    g.assign (mkExpectedPropHint pf' (← mkEq lhs rhs))

/-- A continuation premise: `∀ …, (blk.runBodyFrom … >>= g) = K`, with or without binders. -/
def isContinuation (ty : Expr) : MetaM Bool :=
  forallTelescope ty fun _ b => do
    let some (_, l, _) := b.eq? | return false
    return (l.find? (·.isAppOf ``BasicBlock.runBodyFrom)).isSome

/-- Close a decidable side condition by `decide`, failing loudly when it is false. -/
def closeByDecide (g : MVarId) : MetaM Unit := do
  let ty ← instantiateMVars (← g.getType)
  let some pf ←
    Tactic.decideProof?
        ty | throwError "step_pattern: side condition false or undecidable{indentExpr ty}"
  g.assign pf

/-- Close a side condition from the facts (`memFact`: a fact about the pattern's inputs, like a flag
being `0` or `1`, a `≠` from a `Nodup`, one about an earlier state), else by `decide`. -/
def closeSide (g : MVarId) : TacticM Unit := do
  unless ← Tactic.memFact g do
    closeByDecide g

/-- A premise of a pattern lemma: a read (`closePatternRead`), a side condition (`closeSide`), or
a conjunction of them (`E ⊨ [r := v, …]`, also through an abbreviation), split. -/
partial def closePremise (g : MVarId) : TacticM Unit := do
  let ty ← instantiateMVars (← g.getType)
  -- reads through an abbreviation (`abbrev Holds E … := E ⊨ […]`), unfolded
  let ty' ← whnfR ty
  let (g, ty) ←
    if ty' != ty && (ty'.find? (·.isAppOfArity ``Env.read 4)).isSome then
      pure (← g.replaceTargetDefEq ty', ty')
    else
      pure (g, ty)
  if let some (ga, gb)← Tactic.splitAnd? g ty then
    closePremise ga
    closePremise gb
  else if Tactic.isEnvReadEq ty then
    closePatternRead g
  else
    closeSide g

def stepPatternAt (stx : Syntax) : TacticM Unit := do
  -- the state as `S` with `hS`, to seal what the pattern stores
  Tactic.ensureStateEq
  withMainContext do
      let args := StepArgs.parse mkNullNode stx[3] mkNullNode mkNullNode (named := true)
      let g ← getMainGoal
      let inState := (← getRunBodyFrom (← getGoalType).2).state
      -- a constant with all its arguments open, so its implicit registers are ours to split
      let thm := stepLemmaTerm stx[2]
      let lem ←
        if thm.raw.isIdent then
          mkConstWithFreshMVarLevels (← realizeGlobalConstNoOverloadWithInfo thm)
        else
          instantiateMVars (← Term.elabTerm thm none)
      let (ms, _, concl) ← forallMetaTelescopeReducing (← inferType lem)
      -- registers as `⟨?i, ?h⟩`, so the body's `.val k _` fixes them
      -- (assigned, not unified: structure eta would solve `?x =?= ⟨?i, ?h⟩` by `?i := ?x.i`);
      -- with explicit arguments, the elaborator's open implicits too
      let mut typeProofs := #[]
      for m in (← getMVars lem).map mkMVar ++ ms do
        let ty ← instantiateMVars (← inferType m)
        if ty.isAppOfArity ``Dst 2 && !(← m.mvarId!.isAssigned) then
          let dst := mkApp2 (mkConst ``Dst.mk) (ty.getArg! 0) (ty.getArg! 1)
          let .forallE _ iTy _ _ ← whnf (← inferType dst) | throwError "`Dst.mk`: no index"
          let i ← mkFreshExprMVar iTy
          let .forallE _ hTy _ _ ←
            whnf (← inferType (mkApp dst i)) | throwError "`Dst.mk`: no proof"
          let h ← mkFreshExprMVar hTy
          typeProofs := typeProofs.push h.mvarId!
          m.mvarId!.assign (mkApp2 dst i h)
      unless ← isDefEq concl (← instantiateMVars (← g.getType)) do
        throwError "step_pattern: the conclusion of{indentExpr lem}\ndoes not match the goal"
      -- the body first: it fixes the registers and arguments the other premises mention
      let mut bodyFact? := none
      for m in ms do
        let some (_, lhs, rhs) := (← instantiateMVars (← m.mvarId!.getType)).eq? | continue
        if lhs.isAppOf ``List.drop then
          if ← withDefault (isDefEq lhs rhs) then
            m.mvarId!.assign (← mkEqRefl lhs)
          else if let some h← bodyFactAs? lhs rhs then
            -- an abstract block (a pattern lemma's proof): through its body fact
            m.mvarId!.assign h
            bodyFact? := some h
          else
            throwError "step_pattern: the body at the position is not the pattern of{indentExpr lem}"
      let mut cont? := none
      for m in ms do
        let mv := m.mvarId!
        if ← mv.isAssigned then
          continue
        let ty ← instantiateMVars (← mv.getType)
        unless ← isProp ty do
          continue
        if ← isContinuation ty then
          cont? := some mv
          continue
        closePremise mv
      -- a register's type proof: unification skips proofs, so none got assigned
      for h in typeProofs do
        unless ← h.isAssigned do
          let some (_, l, r) := (← instantiateMVars (← h.getType)).eq? | continue
          unless ← withDefault (isDefEq l r) do
            throwError "step_pattern: register type mismatch{indentExpr (← h.getType)}"
          h.assign (← mkEqRefl l)
      let some cont := cont? | throwError "step_pattern: no continuation premise"
      g.assign (← instantiateMVars (mkAppN lem ms))
      -- the lemma's names: a kept fact is referred to by them
      let (dead, main) ← cont.introNP (getIntrosSize (← instantiateMVars (← cont.getType)))
      replaceMainGoal [← Tactic.reduceIndex main]
      -- an abstract block's body fact, carried past the pattern
      if let some h := bodyFact? then
        withMainContext do
            let h ← instantiateMVars h
            let h' ← mkAppM ``List.drop_add_of_drop_eq_append #[h]
            let some (_, l, rest) := (← inferType h').eq? | throwError "body fact: not an equation"
            let run ← getRunBodyFrom (← getMainTarget)
            let ty ← mkEq (← mkAppM ``List.drop #[run.idx, l.appArg!]) rest
            let (_, main) ← (← (← getMainGoal).assert `hbody ty (mkExpectedPropHint h' ty)).intro1P
            replaceMainGoal [main]
      finishStep args
      -- the pattern's intermediates: sealed away, so unused; its facts about them kept
      let mut main ← getMainGoal
      for x in dead.reverse do
        let some d := (← main.getDecl).lctx.find? x | continue
        unless ← main.withContext (isProp d.type) do
          main ← main.tryClear x
      replaceMainGoal [main]
      -- a pattern that stores: its new state sealed, as an impure step's (last: `substCore`
      -- reintroduces the locals after the state)
      let outState ←
        withMainContext do
            return (← getRunBodyFrom (← getGoalType).2).state
      if outState != inState then
        let goals ← sealStep inState
        replaceMainGoal ((← getMainGoal) :: goals.toList)

@[tactic stepPattern]
def evalStepPattern : Tactic := fun stx => Tactic.atStepDepth (stepPatternAt stx)

end

end LeanMLIR.RIR
