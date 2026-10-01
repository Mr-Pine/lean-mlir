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
syntax (name := stepPattern) "step_pattern" " using " term (stepNames)? : tactic

/-- `pf : lhs = v` into `lhs = v'`, each local of `v` with a definition `x = t` in context replaced by
`t`. -/
def unfoldLocals (v pf : Expr) : MetaM (Expr × Expr) := do
  let mut v := v
  let mut pf := pf
  for x in (collectFVars {} v).fvarIds do
    let some h ← Tactic.findEqWithLhs? (.fvar x) m!"" | continue
    let some (_, _, t) := (← instantiateMVars (← h.getType)).eq? | continue
    let motive ←
      withLocalDeclD `y (← x.getType) fun y => do
          mkLambdaFVars #[y] (v.replaceFVar (.fvar x) y)
    pf ← mkEqTrans pf (← mkCongrArg motive (.fvar h))
    v := v.replaceFVar (.fvar x) t
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
    if reg.isAppOf ``Reg.arg then
      let r ←
        Tactic.simpValue true mkNullNode (← mkAppM ``Env.read #[lhs.getArg! 2, reg]) (lhs.getArg! 2)
            false
      unless ← withDefault (isDefEq r.expr rhs) do
        throwError "step_pattern: {lhs} is{indentExpr r.expr}\nnot{indentExpr rhs}"
      g.assign (mkExpectedPropHint (← r.getProof) (← mkEq lhs rhs))
      return
    let some (v, pf) ← Tactic.walkRead (lhs.getArg! 2) reg |
      do
        let r ← mkAppM ``Env.read #[lhs.getArg! 2, reg]
        throwError "step_pattern: no value for the read{indentExpr r}\nthrough the writes; add a fact \
        `h : E.read %k = _` about the block's entry env"
    if ← isDefEq v rhs then
      g.assign (mkExpectedPropHint pf (← mkEq lhs rhs))
      return
    let (v', pf') ← unfoldLocals v pf
    unless ← withDefault (isDefEq v' rhs) do
      throwError "step_pattern: {lhs} is{indentExpr v}\nnot{indentExpr rhs}"
    g.assign (mkExpectedPropHint pf' (← mkEq lhs rhs))

/-- Close a decidable side condition by `decide`, failing loudly when it is false. -/
def closeByDecide (g : MVarId) : MetaM Unit := do
  let ty ← instantiateMVars (← g.getType)
  let inst ← synthInstance (← mkAppM ``Decidable #[ty])
  let value ← withDefault <| whnf (mkApp2 (mkConst ``Decidable.decide) ty inst)
  unless value.isConstOf ``Bool.true do
    throwError "step_pattern: side condition does not hold{indentExpr ty}"
  g.assign (← mkDecideProof ty)

/-- Close a side condition by a local hypothesis (a fact about the pattern's inputs, like a flag
being `0` or `1`), a `≠` from a `Nodup`, or one about an earlier state through `transport_fact`,
else by `decide`. -/
def closeSide (g : MVarId) : TacticM Unit := do
  if ← g.assumptionCore then
    return
  if let some (_, a, b) := (← instantiateMVars (← g.getType)).ne? then
    if let some pf← Tactic.neProof? (← Tactic.splitConjunctedFacts) a b then
      g.assign pf
      return
  if (← observing? (Tactic.run g (evalTactic (← `(tactic| transport_fact))))) matches some [] then
    return
  closeByDecide g

@[tactic stepPattern]
def evalStepPattern : Tactic := fun stx => do
  -- the state as `S` with `hS`, to seal what the pattern stores
  Tactic.ensureStateEq
  withMainContext do
      let args :=
        StepArgs.parse (mkNullNode #[mkNullNode, mkNullNode]) stx[3] mkNullNode mkNullNode (named :=
          true)
      let g ← getMainGoal
      let inState := (← getRunBodyFrom (← getGoalType).2).state
      -- a constant with all its arguments open, so its implicit registers are ours to split
      let lem ←
        if stx[2].isIdent then
          mkConstWithFreshMVarLevels (← realizeGlobalConstNoOverload stx[2])
        else
          instantiateMVars (← Term.elabTerm stx[2] none)
      let (ms, _, concl) ← forallMetaTelescopeReducing (← inferType lem)
      unless ← isDefEq concl (← instantiateMVars (← g.getType)) do
        throwError "step_pattern: the conclusion of{indentExpr lem}\ndoes not match the goal"
      -- registers as `⟨?i, ?h⟩`, so the body's `.val k _` fixes them
      -- (assigned, not unified: structure eta would solve `?x =?= ⟨?i, ?h⟩` by `?i := ?x.i`)
      let mut typeProofs := #[]
      for m in ms do
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
      -- the body first: it fixes the registers and arguments the other premises mention
      for m in ms do
        let some (_, lhs, rhs) := (← instantiateMVars (← m.mvarId!.getType)).eq? | continue
        if lhs.isAppOf ``List.drop then
          unless ← withDefault (isDefEq lhs rhs) do
            throwError "step_pattern: the body at the position is not the pattern of{indentExpr lem}"
          m.mvarId!.assign (← mkEqRefl lhs)
      let mut cont? := none
      for m in ms do
        let mv := m.mvarId!
        if ← mv.isAssigned then
          continue
        let ty ← instantiateMVars (← mv.getType)
        unless ← isProp ty do
          continue
        if ty.isForall then
          cont? := some mv
          continue
        match ty.eq? with
        | some (_, lhs, rhs) =>
          if lhs.isAppOfArity ``Env.read 4 then
            closePatternRead mv
          else
            closeSide mv
        | none =>
          closeSide mv
      -- a register's type proof: unification skips proofs, so none got assigned
      for h in typeProofs do
        unless ← h.isAssigned do
          let some (_, l, r) := (← instantiateMVars (← h.getType)).eq? | continue
          unless ← withDefault (isDefEq l r) do
            throwError "step_pattern: register type mismatch{indentExpr (← h.getType)}"
          h.assign (← mkEqRefl l)
      let some cont := cont? | throwError "step_pattern: no continuation premise"
      g.assign (← instantiateMVars (mkAppN lem ms))
      let (dead, main) ← cont.intros
      replaceMainGoal [← Tactic.reduceIndex main]
      finishStep args.value args.hyp false mkNullNode true
      -- the pattern's intermediates: sealed away, so unused
      let mut main ← getMainGoal
      for x in dead do
        main ← main.tryClear x
      replaceMainGoal [main]
      -- a pattern that stores: its new state sealed, as an impure step's (last: `substCore`
      -- reintroduces the locals after the state)
      let outState ←
        withMainContext do
            return (← getRunBodyFrom (← getGoalType).2).state
      if outState != inState then
        let goals ← sealStep inState #[]
        replaceMainGoal ((← getMainGoal) :: goals.toList)

end

end LeanMLIR.RIR
