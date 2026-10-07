import SSA.Projects.Firedancer.Common.Proof.Scalar.Arithmetic.Registers

/-!
Read the operand names preserved in the constructive source evaluator and
expose one source expression per numbered register. The elaborator copies
expressions and composes congruence proofs only. Every result is checked by
the kernel against the original witness and the explicit LLVM register stage.
-/

namespace Firedancer.Common.ScalarArithmetic.SourceStages
open Lean Meta Elab Term

private structure SourceStage where
  expression : Expr
  operator : Option Expr
  operands : Array Nat

private partial def gather (idx : Nat) (raw digest : Expr)
    (stages : Std.HashMap Nat SourceStage) : MetaM (Std.HashMap Nat SourceStage) := do
  if stages.contains idx then return stages
  let mut e := raw
  -- The threaded witnesses introduce `fun x => ...` wrappers. Keep the
  -- operation's `fun k v... => ...` intact instead of evaluating LLVM binds.
  while e.getAppFn.isLambda && e.getAppFn.bindingName! != `k do
    e := e.getAppFn.beta e.getAppArgs
  let operator := e.getAppFn
  let mut binders := operator
  let mut names : Array Name := #[]
  while binders.isLambda do
    names := names.push binders.bindingName!
    binders := binders.bindingBody!
  let mut stages := stages
  let mut deps : Array Nat := #[]
  if names.size > 0 && names[0]! == `k then
    let args := e.getAppArgs
    unless args.size == names.size do throwError "stage {idx}: unexpected application"
    for j in [1:names.size] do
      let n := names[j]!.toString
      unless n.startsWith "v" do throwError "stage {idx}: unexpected operand name {n}"
      let some dep := (n.drop 1).toString.toNat? | throwError "stage {idx}: bad operand {n}"
      deps := deps.push dep
      stages ← gather dep args[j]! digest stages
    return stages.insert idx ⟨← mkLambdaFVars #[digest] raw, some operator, deps⟩
  else
    return stages.insert idx ⟨← mkLambdaFVars #[digest] raw, none, #[]⟩

private initialize stageCache : IO.Ref (Option (Std.HashMap Nat SourceStage)) ← IO.mkRef none

private def getStages : TermElabM (Std.HashMap Nat SourceStage) := do
  if let some stages ← stageCache.get then return stages
  let ci ← getConstInfo ``sourceReduce
  let some expr := ci.value? | throwError "source evaluator has no body"
  let stages ← lambdaTelescope expr fun args body => do
    unless args.size == 1 && body.isAppOf ``Firedancer.Common.wordsOf do
      throwError "unexpected source evaluator shape"
    let values := body.getAppArgs
    unless values.size == 4 do throwError "unexpected source output shape"
    let mut stages : Std.HashMap Nat SourceStage := {}
    for (idx, value) in #[454, 464, 475, 483].zip values do
      stages ← gather idx value args[0]! stages
    return stages
  stageCache.set (some stages)
  return stages

elab "source_stage_expr " i:num : term => do
  let stages ← getStages
  let some stage := stages[i.getNat]? | throwError "no source stage {i.getNat}"
  return stage.expression

elab "source_step_expr " i:num : term => do
  let stages ← getStages
  let some stage := stages[i.getNat]? | throwError "no source stage {i.getNat}"
  let some op := stage.operator | throwError "source stage {i.getNat} has no operation"
  return op

elab "source_stage_congruence " i:num ppSpace digest:term : term => do
  let stages ← getStages
  let some stage := stages[i.getNat]? | throwError "no source stage {i.getNat}"
  let digest ← elabTerm digest none
  let some op := stage.operator | return ← mkEqRefl (mkApp stage.expression digest)
  let mut proof ← mkEqRefl (mkApp op digest)
  for dep in stage.operands do
    let name := Name.str `Firedancer.Common.ScalarArithmetic.Registers ("align_" ++ toString dep)
    proof ← mkAppM ``congr #[proof, mkApp (mkConst name) digest]
  let opName := Name.str `Firedancer.Common.ScalarArithmetic.Registers ("op_" ++ toString i.getNat)
  if (← getEnv).contains opName then
    let operands := stage.operands.map fun dep =>
      mkApp (mkConst (Name.str `Firedancer.Common.ScalarArithmetic.Registers ("r" ++ toString dep))) digest
    let step := mkAppN (mkConst opName) (#[digest] ++ operands)
    proof ← mkAppM ``Eq.trans #[proof, step]
  return proof

elab "source_final_congruence " digest:term : term => do
  let digest ← elabTerm digest none
  let mut proof ← mkEqRefl (mkConst ``Firedancer.Common.wordsOf)
  for idx in #[454, 464, 475, 483] do
    let name := Name.str `Firedancer.Common.ScalarArithmetic.Registers ("align_" ++ toString idx)
    proof ← mkAppM ``congr #[proof, mkApp (mkConst name) digest]
  return proof

end Firedancer.Common.ScalarArithmetic.SourceStages
