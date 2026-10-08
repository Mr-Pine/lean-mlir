module

public import SSA.Projects.RIR.Semantics.Func
public meta import SSA.Projects.RIR.Run.BasicBlock
public meta import SSA.Projects.RIR.Run.Scalar
public meta import SSA.Projects.RIR.Run.Tactic.Env
public meta import SSA.Projects.RIR.Run.Tactic.Step.Syntax
public meta import Lean.Elab.Tactic
public import SSA.Projects.RIR.Run.Tactic.Trace

namespace LeanMLIR.RIR

open Lean Elab Tactic Meta

public meta section

syntax (name := finishBlock) "finish_block" stepSimpArgs : tactic

simproc reduceFuncContinue (Func.continue _ _ _) := fun e => do
  let_expr Func.continue func E res s := e | return .continue
  -- an exit; a jump stays
  let_expr Sum.inl _ _ vals := res | return .continue
  let proof ← mkAppOptM ``Func.exit #[func, vals, s, E]
  let some (_, _, rhs) := (← inferType proof).eq? | return .continue
  return .visit { expr := rhs, proof? := proof }

/-- Reduce `b.exit` when the block is concrete. -/
dsimproc [simp, mlir_instr]reduceBlockExit (BasicBlock.exit _) := fun e => do
  let e' ← withTransparency .default (whnf e)
  return if e' == e then .continue else .visit e'

/-- The `if`s of a chain choosing between jumps, outermost first. -/
partial def jumpItes (e : Expr) : Array Expr :=
  if e.isAppOfArity ``ite 5 && (e.getArg! 3).isAppOf ``Jump.run then #[e] ++ jumpItes (e.getArg! 4)
  else #[]

/-- Rewrite `ite` (`@ite α c inst t e`) to `t` by `ite_eq_left h`, or to `e` by `ite_eq_right h`. -/
def rwIte (g : MVarId) (lem : Name) (ite : Expr) (h : FVarId) : MetaM MVarId :=
  g.withContext do
    let eq :=
      mkAppN (mkConst lem ite.getAppFn.constLevels!)
        #[ite.getArg! 1, ite.getArg! 2, mkFVar h, ite.getArg! 0, ite.getArg! 3, ite.getArg! 4]
    let r ← g.rewrite (← g.getType) eq
    g.replaceTargetEq r.eNew r.eqProof

/-- A local proving `c` (`true`) or its negation (`false`), up to reducible unfolding. -/
def decideByLocal? (c : Expr) : MetaM (Option (Bool × FVarId)) := do
  if let some h← withReducible (findLocalDeclWithType? c) then
    return some (true, h)
  if let some h← withReducible (findLocalDeclWithType? (mkNot c)) then
    return some (false, h)
  if let some (_, a, b) := c.eq? then
    if let some h← withReducible (findLocalDeclWithType? (← mkAppM ``Ne #[a, b])) then
      return some (false, h)
  return none

/-- Split an `if` chain choosing between jumps into one goal per jump. A condition a local decides
takes its branch; otherwise branch `i` gets only its condition, as `hbr`, and the last branch every
negation, as `hbr` for a single `if`, else as `hbr0`, `hbr1`, …. -/
def splitJumps : TacticM Unit :=
  withMainContext do
    let g ← getMainGoal
    let some c := (← instantiateMVars (← g.getType)).find? (fun e => (jumpItes e).size > 0) | return
    let mut g := g
    let mut negs := #[]
    let mut goals := #[]
    for ite in jumpItes c do
      match ← g.withContext (decideByLocal? (ite.getArg! 1)) with
      | some (true, h) =>
        setGoals (goals.push (← (← rwIte g ``ite_eq_left ite h).tryClearMany negs)).toList
        return
      | some (false, h) =>
        g ← rwIte g ``ite_eq_right ite h
        continue
      | none =>
        pure ()
      let (pos, neg) ← g.byCases (ite.getArg! 1) `hbr
      -- this branch: its condition only
      goals := goals.push (← (← rwIte pos.mvarId ``ite_eq_left ite pos.fvarId).tryClearMany negs)
      negs := negs.push neg.fvarId
      g ← rwIte neg.mvarId ``ite_eq_right ite neg.fvarId
    -- the last branch: every negation, under distinct names
    if negs.size > 1 then
      for h in negs, i in [0:negs.size] do
        g ← g.rename h (.mkSimple s!"hbr{i}")
    setGoals (goals.push g).toList

/-- Resolve the register reads in the env a jump writes: `Func.runFrom f E' k S`, with `E'` the
target's parameters written into the env before the jump, which every read reads. -/
def resolveJumpArgs (only : Bool) (simpArgs : Syntax) : TacticM Unit :=
  withMainContext do
    let (_, goal) ← getGoalType
    let env := (← getFuncRunFromGoal goal).env
    let reads ← IO.mkRef (#[] : Array Expr)
    env.forEachWhere (·.isAppOfArity ``Env.read 4) fun r => reads.modify (·.push r)
    for read in ← reads.get do
      let r ← simpValue only simpArgs read (read.getArg! 2) true
      replaceMainGoal [← replaceBySimp (← getMainGoal) read r]

def finishJumpingBlock (only : Bool) (simpArgs : Syntax) : TacticM Unit := do
  let (g, goal) ← getGoalType
  -- Reduce potential condition read for jump
  if let some read := goal.find? (·.isAppOfArity ``Env.read 4) then
    let r ← simpValue only simpArgs read (read.getArg! 2) true
    replaceMainGoal [← replaceBySimp g read r]
    -- `dsimp` to get rid of the `match`
    evalTactic (← `(tactic| dsimp only [Ty.unwrap_bv]))
  evalTactic
      (←
        `(tactic|
            try
              simp only [switchTarget, Jump.run_ite, beq_iff_eq, bne_iff_ne, ofBool_eq_one_iff,
                BitVec.reduceEq, ↓reduceIte]))
  splitJumps
  evalTactic
      (←
        `(tactic|
            all_goals
              try
                dsimp only [Jump.run, Fin.isValue, Regs.read_nil, EffectM.pure_eq,
                  PoisonOr.value_bind, Regs.read_cons, reduceWriteManyDsts, Env.writeMany_nil,
                  Env.writeMany_cons]))
  evalTactic (← `(tactic| all_goals rw [Func.continue_next]))
  let mut goals := []
  for g in ← getGoals do
    setGoals [g]
    resolveJumpArgs only simpArgs
    let (_, goal) ← getGoalType
    sealEnvAt (← getFuncRunFromGoal goal).env
    goals := goals ++ (← getGoals)
  setGoals goals

@[tactic finishBlock]
def evalFinishBlock : Tactic := fun stx =>
  withMainContext do
    -- at the block's end: `body.drop pos` reduces to `[]` here, so a wrong position fails at the
    -- tactic; `hpos` itself by `decide`, for the kernel only, as each step's
    let (g, goal) ← getGoalType
    let run ← getRunBodyFrom goal
    unless (← bodyFrom run.block run.idx).isAppOfArity ``List.nil 1 do
      throwError "`finish_block`: instructions left at position {run.idx}"
    let r ← g.rewrite goal (← mkConstWithFreshMVarLevels ``BasicBlock.runBodyFrom_done)
    for m in r.mvarIds do
      unless ← m.isAssigned do
        m.assign (← mkDecideProof (← instantiateMVars (← m.getType)).consumeTypeAnnotations)
    replaceMainGoal [← g.replaceTargetEq r.eNew r.eqProof]
    evalTactic
        (←
          `(tactic|
              simp only [EffectM.pure_eq, PoisonOr.value_bind, reduceBlockExit, reduceFuncContinue,
                Exit.run]))
    let (g, goal) ← getGoalType
    let some ret :=
      goal.find?
        (·.isAppOfArity ``Regs.read 4) -- If we don't exit, this will throw. Handle when relevant
      | finishJumpingBlock (!stx[1][0].isNone) stx[1][1]
    let env := ret.getArg! 2
    let r ← simpValue (only := !stx[1][0].isNone) (simpArgs := stx[1][1]) ret env true
    replaceMainGoal [← replaceBySimp g ret r]

/-- The pointers' equations in context (`hx : x = s.slot k`, a named slot's), as simp lemmas. -/
def pointerEqs : TacticM (Array (TSyntax `Lean.Parser.Tactic.simpLemma)) := do
  (← localEqs).filterMapM fun e => do
      unless e.lhs.isFVar && (← inferType e.lhs).isConstOf ``Pointer do
        return none
      let h ← Term.exprToSyntax (← mkExpectedTypeHint e.decl.toExpr e.type)
      return some (← `(Lean.Parser.Tactic.simpLemma| $h:term))

/-- A frame bound `n ≤ _` by `omega` over the counters, the pointers by `eqs` (`pointerEqs`). -/
def slotBound (eqs : Array (TSyntax `Lean.Parser.Tactic.simpLemma)) :
    TacticM (TSyntax ``Lean.Parser.Tactic.tacticSeq) :=
  `(tacticSeq|
    (try simp only [GlobalState.allocaPtr_id_id, GlobalState.alloca_alloc,
        GlobalState.slot_id_id, Pointer.add, $eqs,*]);
      omega)

/-- Close a frame bound `n ≤ _` by `omega` over the counters, the pointers by their equations in the
context (`hx : x = s.slot k`, a named slot's). -/
elab "slot_bound" : tactic =>
  withMainContext do
    evalTactic (← slotBound (← pointerEqs))

/-- Erase a frame from a result state with the `mlir_erase` lemmas: writes into the frame's blocks
and its `alloca`s and new blocks are dropped, their bounds `n ≤ _` by a fact or `slot_bound`; then
the erase itself, below a `WF` state's counter. -/
elab "erase_frame" : tactic =>
  withMainContext do
    let bound ← slotBound (← pointerEqs)
    evalTactic
        (←
          `(tactic|
              ( simp (disch :=
                  first
                  | assumption
                  | $bound) only [$(mkIdent `mlir_erase):ident]
                try simp (disch := assumption) only [GlobalState.WF.eraseFrom])))

end

end LeanMLIR.RIR
