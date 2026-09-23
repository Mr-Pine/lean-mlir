module

public import SSA.Projects.RIR.Semantics.Func
public meta import SSA.Projects.RIR.Run.BasicBlock
public meta import SSA.Projects.RIR.Run.Tactic.Env
public meta import Lean.Elab.Tactic
public import SSA.Projects.RIR.Run.Tactic.Trace

namespace LeanMLIR.RIR

open Lean Elab Tactic Meta

public meta section

syntax (name := finishBlock) "finish_block" (&" only")? (" [" withoutPosition(Lean.Parser.Tactic.simpArg,*,?) "]")? :
  tactic

simproc reduceFuncContinue (Func.continue _ _ _) := fun e => do
  let_expr Func.continue func E res s := e | return .continue
  let proof ← match_expr res with
      | Sum.inl _ _ vals => mkAppOptM ``Func.exit #[func, vals, s, E]
      | Sum.inr _ _ n => return .continue -- TODO
      | _ => return .continue
  let some (_, _, rhs) := (← inferType proof).eq? | return .continue
  return .visit { expr := rhs, proof? := proof }

@[tactic finishBlock]
def evalFinishBlock : Tactic := fun stx => withMainContext do
  evalTactic (← `(tactic| (
    rw [BasicBlock.runBodyFrom_done]
    simp only [EffectM.pure_eq, PoisonOr.value_bind, reduceFuncContinue, Exit.run])))

  let (g, goal) ← getGoalType
  let some ret := goal.find? (·.isAppOfArity ``Regs.read 4) -- If we don't exit, this will throw. Handle when relevant
    | throwError "no {``Regs.read} in the goal{indentExpr goal}"
  let env := ret.getArg! 2
  let r ← simpValue (only := !stx[1].isNone) (simpArgs := stx[2]) ret env
  let body ← kabstract goal ret
  let motive := Expr.lam `ret (← inferType ret) body .default
  replaceMainGoal
      [← g.replaceTargetEq (body.instantiate1 r.expr) (← mkCongrArg motive (← r.getProof' ret))]

end

end LeanMLIR.RIR
