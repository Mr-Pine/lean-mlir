module

public import MLIR.Semantics.Func
public meta import MLIR.Run.BasicBlock
public meta import MLIR.Run.Tactic.Parse
public meta import MLIR.Run.Tactic.Util
public meta import MLIR.Run.Tactic.Env
public meta import MLIR.Run.Tactic.Seal
public meta import MLIR.Run.Tactic.State
public meta import MLIR.Run.Tactic.Step.Impure
public meta import MLIR.Run.Tactic.Step.Common
public meta import MLIR.Run.Tactic.Step.Syntax
public meta import Lean.Elab.Tactic

namespace MLIR

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
syntax (name := stepPattern) "step_pattern" " using " stepLemma (stepPatternNames)? : tactic

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

/-- The registers' type proofs in `instrs`, as the lift proved them: index ↦ `Γ.ty i = t`. -/
def regTypeProofs (instrs : Array Expr) : MetaM (Std.HashMap Nat Expr) := do
  let out ← IO.mkRef ({} : Std.HashMap Nat Expr)
  for x in instrs do
    x.forEachWhere (fun e => e.isAppOfArity ``Dst.mk 4 || e.isAppOfArity ``Reg.val 4) fun e => do
        if let some k← Tactic.finNLit? (e.getArg! 2) then
          out.modify (·.insert k (e.getArg! 3))
  out.get

/-- A body fact `block.body.drop idx = pat ++ rest` for a block whose instructions are known: the
pattern's instructions read off the block, as a step reads one, and `rest` the body past them. The
kernel checks it, so a deep `idx` is not unfolded here. The fact and the instructions, or `none`
when the instructions are not the pattern's. -/
def concreteBodyFact? (lhs rhs : Expr) : MetaM (Option (Expr × Array Expr)) := do
  let some (idx, block) := Tactic.bodyDrop? lhs | return none
  let idx ← instantiateMVars idx
  let some i := idx.nat? <|> idx.rawNatLit? | return none
  let_expr HAppend.hAppend _ _ _ _ pat _ := rhs | return none
  -- the pattern's length, its list unfolded
  let mut k := 0
  let mut p ← whnfD pat
  while p.isAppOfArity ``List.cons 3 do
    k := k + 1
    p ← whnfD p.appArg!
  unless p.isAppOfArity ``List.nil 1 do
    return none
  let mut instrs := #[]
  for j in [i:i + k] do
    let some x ← blockInstr? block (mkNatLit j) | return none
    instrs := instrs.push x
  let_expr List.drop α _ body := lhs | return none
  let rest := mkApp3 (.const ``List.drop lhs.getAppFn.constLevels!) α (mkNatLit (i + k)) body
  let fact :=
    mkAppN rhs.getAppFn (rhs.getAppArgs.extract 0 4 ++ #[← mkListLit α instrs.toList, rest])
  unless ← isDefEq fact rhs do
    return none
  return some (mkExpectedPropHint (← mkEqRefl lhs) (← mkEq lhs (← instantiateMVars rhs)), instrs)

/-- A body fact `block.body.drop idx = pat ++ rest` from a concrete block's literal body fact
`block.body.drop idx = xs`: the pattern's instructions the first of `xs`, `rest` the others; the
kernel checks only the pattern's instructions. The fact and the instructions, or `none`. -/
def literalPatternFact? (lhs rhs : Expr) : MetaM (Option (Expr × Array Expr)) := do
  let some (idx, block) := Tactic.bodyDrop? lhs | return none
  let some f ← Tactic.bodyFact? block idx | return none
  unless f.hidden do
    return none
  let_expr HAppend.hAppend _ _ _ _ pat _ := rhs | return none
  let mut k := 0
  let mut p ← whnfD pat
  while p.isAppOfArity ``List.cons 3 do
    k := k + 1
    p ← whnfD p.appArg!
  unless p.isAppOfArity ``List.nil 1 do
    return none
  let mut instrs := #[f.instr]
  let mut rest := f.rest
  for _ in [1:k] do
    let_expr List.cons _ x xs := rest | return none
    instrs := instrs.push x
    rest := xs
  let_expr List.drop α _ _ := lhs | return none
  let fact :=
    mkAppN rhs.getAppFn (rhs.getAppArgs.extract 0 4 ++ #[← mkListLit α instrs.toList, rest])
  unless ← isDefEq fact rhs do
    return none
  return some (mkExpectedPropHint f.proof (← mkEq lhs (← instantiateMVars rhs)), instrs)

/-- Substitute a state the continuation bound (`bound`, the goal's state) by its equation among the
binders (`hS' : S' = t`); whether the state is bound without one (a fresh state). -/
def bindStateEq (bound : Array FVarId) : TacticM Bool :=
  withMainContext do
    let st := (← getRunBodyFrom (← getMainTarget)).state
    let some sv := st.fvarId? | return false
    unless bound.contains sv do
      return false
    for h in bound do
      let some d := (← getLCtx).find? h | continue
      let some (_, l, r) := (← instantiateMVars d.type).eq? | continue
      let symm? :=
        if l == st && !r.containsFVar sv then some false
        else if r == st && !l.containsFVar sv then some true
        else none
      let some symm := symm? | continue
      replaceMainGoal [(← substCore (← getMainGoal) h (symm := symm)).2]
      return false
    return true

/-- `g` without the facts about the state `S` before a pattern whose continuation binds a fresh
state: they do not hold of it. Equations and continuations stay; `S` and its equation go if
nothing else mentions them. -/
def dropStateFacts (g : MVarId) (S : Expr) : MetaM MVarId :=
  g.withContext do
    let some hS ← Tactic.findEqWithLhs? S | return g
    let hs ← (← hypsMentioning S (except := #[hS])).filterM fun h => do
        let ty ← instantiateMVars (← h.getType)
        return (← isProp ty) && !ty.isEq && !(← Tactic.isContinuation ty)
    let g ← g.tryClearMany hs
    let g ← g.tryClear hS
    match S.fvarId? with
    | some s => g.tryClear s
    | none => pure g

def stepPatternAt (stx : Syntax) : TacticM Unit := do
  -- a concrete block's body fact, as a step's: the pattern's instructions read off it
  withMainContext do
      let (g, goal) ← getGoalType
      replaceMainGoal [(← withBodyFact g (← getRunBodyFrom goal)).1]
  -- the state as `S` with `hS`, to seal what the pattern stores
  Tactic.ensureStateEq
  withMainContext do
      let (args, names) := StepArgs.parsePattern stx[3]
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
      let mut instrs := #[]
      for m in ms do
        let some (_, lhs, rhs) := (← instantiateMVars (← m.mvarId!.getType)).eq? | continue
        if lhs.isAppOf ``List.drop then
          if let some (h, xs)← literalPatternFact? lhs rhs then
            m.mvarId!.assign h
            instrs := xs
            bodyFact? := some (h, true)
          else if let some (h, xs)← concreteBodyFact? lhs rhs then
            m.mvarId!.assign h
            instrs := xs
          else if ← withDefault (isDefEq lhs rhs) then
            m.mvarId!.assign (← mkEqRefl lhs)
          else if let some h← bodyFactAs? lhs rhs then
            -- an abstract block (a pattern lemma's proof): through its body fact
            m.mvarId!.assign h
            bodyFact? := some (h, false)
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
      -- a register's type proof: unification skips proofs, so none got assigned; the body's own
      -- when known (deciding `Γ.ty i` unfolds `Γ` to register `i`, too deep for a long function)
      let proofs ← regTypeProofs instrs
      for h in typeProofs do
        unless ← h.isAssigned do
          let hTy ← instantiateMVars (← h.getType)
          let some (_, l, r) := hTy.eq? | continue
          if let some k← Tactic.finNLit? l.appArg! then
            if let some pf := proofs[k]? then
              if ← withReducible (isDefEq (← inferType pf) hTy) then
                h.assign pf
                continue
          unless ← withDefault (isDefEq l r) do
            throwError "step_pattern: register type mismatch{indentExpr (← h.getType)}"
          h.assign (← mkEqRefl l)
      let some cont := cont? | throwError "step_pattern: no continuation premise"
      g.assign (← instantiateMVars (mkAppN lem ms))
      -- the lemma's names: a kept fact is referred to by them
      let (bound, main) ← cont.introNP (getIntrosSize (← instantiateMVars (← cont.getType)))
      let main ← Tactic.reduceIndex main
      -- the values the continuation binds (`∀ A' E', …`): named by `with`, in order
      let (args, main) ← main.withContext do
          let results ← bound.filterM fun x => do
              let ty ← instantiateMVars (← x.getType)
              if ← isProp ty then
                return false
              let heads := [``Ty.denote, ``PoisonOr, ``GlobalState, ``Env, ``MemoryState]
              return !heads.any (ty.isAppOf ·)
          if names.isEmpty || results.isEmpty || stx[3][0][0][1].getNumArgs > 0 then
            return (args, main)
          unless names.size ≤ results.size do
            throwError "step_pattern: {names.size} names for the {results.size} values the \
              continuation binds ({← results.mapM (·.getUserName)})"
          let mut main := main
          for x in results, n in names do
            main ← main.rename x n.getId
          -- named, so folded: their equations among the binders (`a = …`) tagged as `with`'s
          for h in bound do
            let ty ← instantiateMVars (← h.getType)
            let some (_, .fvar y, _) := ty.eq? | continue
            if (results.extract 0 names.size).contains y then
              main ← main.replaceLocalDeclDefEq h (Tactic.tagNamed ty)
          return ({ args with value := .auto, hyp := .auto, tag := false }, main)
      -- its facts: an anonymous one named after the value it equates (`ha` for `a = …`), else
      -- after its predicate (`htablePhase`)
      let main ← main.withContext do
          let mut main := main
          for x in bound do
            let ty := (← instantiateMVars (← x.getType)).consumeMData
            unless (← x.getUserName).hasMacroScopes && (← isProp ty) do
              continue
            main ← main.rename x (← Tactic.factName ty)
          return main
      replaceMainGoal [main]
      -- an abstract block's body fact, carried past the pattern
      if let some (h, hidden) := bodyFact? then
        withMainContext do
            let h ← instantiateMVars h
            let h' ← mkAppM ``List.drop_add_of_drop_eq_append #[h]
            let some (_, l, rest) := (← inferType h').eq? | throwError "body fact: not an equation"
            let run ← getRunBodyFrom (← getMainTarget)
            let ty ← mkEq (← mkAppM ``List.drop #[run.idx, l.appArg!]) rest
            replaceMainGoal [← assertBodyFact (← getMainGoal) ty (mkExpectedPropHint h' ty) hidden]
      -- a state the continuation binds: by its equation among the binders (`S' = t`), substituted
      let bare ← bindStateEq bound
      finishStep args
      -- the pattern's intermediates: sealed away, so unused; its facts about them kept
      let mut main ← getMainGoal
      for x in bound.reverse do
        let some d := (← main.getDecl).lctx.find? x | continue
        unless ← main.withContext (isProp d.type) do
          main ← main.tryClear x
      replaceMainGoal [main]
      -- a pattern that stores: its new state sealed, as an impure step's (last: `substCore`
      -- reintroduces the locals after the state); a bound state without an equation is a fresh
      -- one: the old state's facts dropped, the continuation's about it kept
      let outState ←
        withMainContext do
            return (← getRunBodyFrom (← getGoalType).2).state
      if bare then
        withMainContext do
            replaceMainGoal [← dropStateFacts (← getMainGoal) inState]
        Tactic.ensureStateEq
      else if outState != inState then
        let (goals, _) ← sealStep inState
        replaceMainGoal ((← getMainGoal) :: goals.toList)
        -- the body fact, reintroduced by the sealing, hidden again
        clearStaleBodyFacts

@[tactic stepPattern]
def evalStepPattern : Tactic := fun stx => Tactic.atStepDepth (stepPatternAt stx)

end

end MLIR
