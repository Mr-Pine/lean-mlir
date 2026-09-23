module

public import MLIR.Semantics.Func
public meta import MLIR.Run.BasicBlock
public meta import MLIR.Run.Tactic.Env
public meta import Lean.Elab.Tactic
public import MLIR.Run.Tactic.Trace

namespace MLIR

open Lean Elab Tactic Meta

public meta section

syntax (name :=
  finishBlock) "finish_block" (&" only")? (" [" withoutPosition(Lean.Parser.Tactic.simpArg,*,?) "]")? :
  tactic

simproc reduceFuncContinue (Func.continue _ _ _) := fun e => do
  let_expr Func.continue func E res s := e | return .continue
  let proof ←
    match_expr res with
    | Sum.inl _ _ vals =>
      mkAppOptM ``Func.exit #[func, vals, s, E]
    | Sum.inr _ _ n =>
      return .continue -- TODO
    | _ =>
      return .continue
  let some (_, _, rhs) := (← inferType proof).eq? | return .continue
  return .visit { expr := rhs, proof? := proof }

/-- Reduce `b.exit` when the block is concrete. -/
dsimproc [simp, mlir_instr]reduceBlockExit (BasicBlock.exit _) := fun e => do
  let e' ← withTransparency .default (whnf e)
  return if e' == e then .continue else .visit e'

@[tactic finishBlock]
def evalFinishBlock : Tactic := fun stx =>
  withMainContext do
    evalTactic
        (←
          `(tactic|
              ( rw [BasicBlock.runBodyFrom_done]
                simp only [EffectM.pure_eq, PoisonOr.value_bind, reduceBlockExit,
                  reduceFuncContinue, Exit.run])))
    let (g, goal) ← getGoalType
    let some ret :=
      goal.find?
        (·.isAppOfArity ``Regs.read 4) -- If we don't exit, this will throw. Handle when relevant
      | throwError "no {``Regs.read} in the goal{indentExpr goal}"
    let env := ret.getArg! 2
    let r ← simpValue (only := !stx[1].isNone) (simpArgs := stx[2]) ret env
    replaceMainGoal [← replaceBySimp g ret r]

end

end MLIR
