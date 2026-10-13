module

public meta import MLIR.Run.Tactic.Util
public meta import MLIR.Run.Tactic.Env
public meta import MLIR.Run.Tactic.Seal
public meta import Lean.Elab.Tactic

namespace MLIR

open Lean Elab Tactic Meta

public meta section

inductive EnvName
  | inline
  | auto
  | named (s : TSyntax `ident)

/-- The arguments shared by the stepping tactics. -/
structure StepArgs where
  value : EnvName := .auto
  hyp : EnvName := .auto
  only : Bool := false
  simpArgs : Syntax := mkNullNode
  consumed : Array Ident := #[]
  expand : Bool := true
  /-- Tag the value's equation, so later steps keep it folded. -/
  tag : Bool := false

structure RewriteStepResult where
  stepGoal : MVarId
  mainGoal : MVarId

/-- `g` with a body fact for the block and position of `run`: one in context (an abstract block's,
or a concrete one's carried from its last step), else a concrete block's made now (hidden): each
step reads its instruction off the fact, so the kernel's check of a step does not walk the body. -/
def withBodyFact (g : MVarId) (run : RunBodyFrom) : MetaM (MVarId × Option BodyFact) :=
  g.withContext do
    if let some f ← bodyFact? run.block run.idx then
      return (g, some f)
    let some (ty, pf) ← literalBodyFact? run.block run.idx | return (g, none)
    let g ← assertBodyFact g ty pf (hidden := true)
    return (g, ← g.withContext (bodyFact? run.block run.idx))

/-- The body fact `fact` at a position, carried to the goal `main`'s (one instruction on, its index
as `main` spells it), hidden as `fact` is. -/
def carryBodyFact (main : MVarId) (fact : BodyFact) : MetaM MVarId :=
  main.withContext do
    let h' ← mkAppM ``List.drop_succ_of_drop_eq_cons #[fact.proof]
    let some (_, l, xs) := (← inferType h').eq? | throwError "body fact: not an equation"
    -- `[…].append rest` from unfolding the pattern, back to `[…] ++ rest`
    let xs ←
      match_expr xs with
      | List.append _ ys zs =>
        mkAppM ``HAppend.hAppend #[ys, zs]
      | _ =>
        pure xs
    let run ← getRunBodyFrom (← instantiateMVars (← main.getType))
    let ty ← mkEq (← mkAppM ``List.drop #[run.idx, l.appArg!]) xs
    assertBodyFact main ty (mkExpectedPropHint h' ty) fact.hidden

/-- `rewriteStep` after `withBodyFact`, in `g`'s context. -/
def rewriteStepWith (g : MVarId) (lem : Expr) (run : RunBodyFrom) (fact? : Option BodyFact) :
    MetaM RewriteStepResult := do
  let r ← g.rewrite (← g.getType) lem -- Rewrite
  let mut stepGoal? := none
  for m in r.mvarIds do
    let ty := (← instantiateMVars (← m.getType)).consumeTypeAnnotations
    if ty.isAppOf ``LT.lt then -- hpos
      match fact? with
      | some f =>
        m.assign (← mkAppM ``List.lt_length_of_drop_eq_cons #[f.proof])
      | none =>
        m.assign (← mkDecideProof ty)
    else if ty.isEq then -- h
      stepGoal? := some m
  let some stepGoal := stepGoal? | throwError "no run goal (hyp `h`)"
  stepGoal.setTag `insn
  -- Resolve block.body[idx]
  let ty ← instantiateMVars (← stepGoal.getType)
  -- `block.body[pos]`, not a `getElem` in the env's written values (`H[7]`)
  let some instr :=
    ty.find? fun e => e.isAppOfArity ``GetElem.getElem 8 && (e.getArg! 5).isAppOf ``BasicBlock.body
    | throwError "no body[pos]"
  let stepGoal ←
    match fact? with
    | some f =>
      stepGoal.withContext do
          let eq ← mkAppM ``List.getElem_of_drop_eq_cons #[f.proof]
          let rw ← stepGoal.rewrite ty eq
          unless rw.mvarIds.isEmpty do
            throwError "body fact: unexpected side goals"
          stepGoal.replaceTargetEq rw.eNew rw.eqProof
    | none =>
      let instr' ← whnfD ((← blockInstr? run.block run.idx).getD instr)
      stepGoal.replaceTargetDefEq ((← kabstract ty instr).instantiate1 instr')
  let main ← reduceIndex (← g.replaceTargetEq (← instantiateMVars r.eNew) r.eqProof)
  -- carry the body fact on to the next instruction
  let main ←
    match fact? with
    | some f => carryBodyFact main f
    | none => pure main
  return ⟨stepGoal, main⟩

/-- Rewrite the goal `g` with `lem`, its `hpos` and instruction from a body fact (`withBodyFact`;
without one, by `decide` and unfolding), returning the remaining goals. -/
def rewriteStep (g : MVarId) (lem : Name) : MetaM RewriteStepResult := do
  let lem ← mkConstWithFreshMVarLevels lem
  let run ←
    g.withContext do
        getRunBodyFrom (← instantiateMVars (← g.getType))
  let (g, fact?) ← withBodyFact g run
  g.withContext (rewriteStepWith g lem run fact?)

/-- `folded h₁ …`: the equations `hᵢ : x = e` (premises, `have`s) stay folded as a `with x`'s do:
later steps keep `x`, never rewriting by `hᵢ`. -/
elab "folded" hs:(ppSpace colGt ident)+ : tactic =>
  withMainContext do
    let mut g ← getMainGoal
    for h in hs do
      let fv ← getFVarId h
      let ty := (← instantiateMVars (← fv.getType)).consumeMData
      unless ty.isEq do
        throwError "`folded`: {h} is not an equation"
      g ← g.replaceLocalDeclDefEq fv (Tactic.tagNamed ty)
    replaceMainGoal [g]

/-- `dsimp [mlir_instr]` -/
def dsimpMlirInstr? (m : MVarId) : MetaM (Option MVarId) := do
  let (m?, _) ← dsimpGoal m (← simpSetContext #[`mlir_instr]) (simprocs := #[← Simp.getSimprocs])
  return m?

/-- Clear the body facts `block.body.drop i = _` behind the goal's position; a concrete block's
hidden again where a step reintroduced it (`substCore`, `revert`). -/
def clearStaleBodyFacts : TacticM Unit :=
  withMainContext do
    let some run := getRunBodyFrom? (← getMainTarget) | return
    let mut g ← getMainGoal
    for e in ← bodyFactEqs do
      let some (n, b) := bodyDrop? e.lhs | continue
      if ← isDefEq b run.block <&&> notM (isDefEq n run.idx) then
        g ← g.tryClear e.decl.fvarId
      else if !e.decl.isImplementationDetail && !b.hasFVar && !b.hasMVar then
        g ← hideLocal g e.decl.fvarId
    replaceMainGoal [g]

/-- The value an effectful step writes, its reads resolved while the state they read is a local
with its facts: sealing the new state substitutes it away, and a read of the substituted term
resolves only by walking its writes. -/
def resolveWrittenValue (args : StepArgs) : TacticM Unit :=
  withMainContext do
    evalTactic
        (←
          `(tactic|
              try
                dsimp only [$(mkIdent ``Env.writeMany_nil):ident,
                  $(mkIdent ``Env.writeMany_cons):ident]))
    let (g, goal) ← getGoalType
    let_expr Env.write _ _ base _ value := (← getRunBodyFrom goal).env | return
    let r ← simpValue args.only args.simpArgs value base args.expand
    replaceMainGoal [← replaceBySimp g value r]

def finishStep (args : StepArgs) : TacticM Unit :=
  withMainContext do
    clearStaleBodyFacts
    -- a call writes its results with `writeMany`: unfold it into single writes (none for `void`)
    evalTactic
        (←
          `(tactic|
              try
                dsimp only [$(mkIdent ``Env.writeMany_nil):ident,
                  $(mkIdent ``Env.writeMany_cons):ident]))
    -- Resolve any env reads
    let (g, goal) ← getGoalType
    let runBodyFrom ← getRunBodyFrom goal
    if runBodyFrom.env.isFVar then
      do
        runSeal
        return -- Nothing to do; Env is not modified
    let_expr Env.write _ _ base dst value := runBodyFrom.env
      | throwError "env {runBodyFrom.env} is not an `Env.write`"
    -- the newly written value, its reads resolved
    let r ← simpValue args.only args.simpArgs value base args.expand
    let g ← replaceBySimp g value r
    replaceMainGoal [g]
    -- unless `inline`, the value as a local `v` with `hv : v = …`
    let name? ←
      match args.value with
      | .inline =>
        pure none
      | .named s =>
        pure (some s.getId)
      | .auto =>
        do
          if let some idx← dstIndex? dst then
            pure (some ((`v).appendAfter (toString idx)))
          else
            -- an abstract register (in a pattern lemma's proof): after its variable, `vy` for `y`
            let xs ←
              (collectFVars {} dst).fvarIds.filterM fun x => return (← x.getType).isAppOf ``Dst
            let some x := xs[0]? | pure (some `v)
            pure (some ((`v).appendAfter (← x.getUserName).toString))
    if let some x := name? then
      let hx :=
        match args.hyp with
        | .named s => s.getId
        | _ => x.appendBefore "h"
      -- only the inner `x` of `.value x` or `wrap x`, so the local is not a `PoisonOr`
      let target :=
        if r.expr.isAppOfArity ``PoisonOr.value 2 || r.expr.isAppOfArity ``Ty.wrap 2 then
          r.expr.appArg!
        else r.expr
      -- a value that already is a local stays: naming it would capture that local everywhere
      unless target.isFVar do
        -- a name given by `with`: its equation shadows only an earlier `x`'s, not another fact
        if let .named _ := args.value then
          if let some d := (← g.getDecl).lctx.findFromUserName? hx then
            let earlierX ← g.withContext do
                let some (_, .fvar y, _) := (← instantiateMVars d.type).consumeMData.eq?
                  | return false
                return (← y.getUserName) == x
            unless d.isImplementationDetail || earlierX do
              throwError "`with {x}`: `{hx}` names a hypothesis already; name the equation \
                (`with {x} h`) or clear `{hx}`"
        let (_, g) ←
          g.withContext do
              -- a tagged value stays folded where later steps and the state take it
              generalizeOpaque g target x
                  #[⟨hx, fun y => do
                      let ty ← mkEq y target
                      return if args.tag then Tactic.tagNamed ty else ty, ← mkEqRefl target⟩]
        replaceMainGoal [g]
    -- Extract new `E`
    sealEnv
    runSeal

end

end MLIR
