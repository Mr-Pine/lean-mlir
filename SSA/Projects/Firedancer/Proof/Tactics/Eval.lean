import SSA.Projects.SLLVM.Dialect
import SSA.Projects.Firedancer.MLIR.DenoteStep
import SSA.Projects.Firedancer.Proof.Overflow

/-!
# Evaluating one stepped instruction

`denote_step_all` leaves `hv<i> : v<i> = <the instruction's semantics>` over the
opaque `v<k>` of its operands. `eval_llvm` reduces that to
`v<i> = PoisonOr.value e`, the form an operand must be in for the next
instruction's `PoisonOr` bind to reduce.
-/

namespace Firedancer
open LeanMLIR SLLVM
open InstCombine (LLVM)

/-- The optional clauses of `eval_llvm`. -/
syntax evalExtra := " [" term,* "]"
syntax evalName := " as " ident

open Lean Elab Tactic Meta in
/-- `eval_llvm i` reduces `hv<i>` to `v<i> = PoisonOr.value e`, each operand
replaced by the value an earlier `eval_llvm` named for it. `eval_llvm i [h₁, h₂]`
adds `h₁, h₂` to the simp set, for the `nsw`/`nuw` guards that need a bound.

`eval_llvm i as x` also names the value: `x` is opaque with `hx : e = x`, so
later instructions see an atom rather than the whole sub-expression, which is
what keeps a chain whose values fan out from growing multiplicatively. The
expression is read off `hv<i>`, never written out. -/
elab "eval_llvm " i:num extra:(evalExtra)? nm:(evalName)? : tactic => do
  let idx := i.getNat
  let hvName := Name.mkSimple s!"hv{idx}"
  let hvIdent := mkIdent hvName
  -- the `hv<k>` of the operands `%i` mentions, and no others
  let prev ← (← getMainGoal).withContext do
    let lctx ← getLCtx
    let some d := lctx.findFromUserName? hvName
      | throwError "eval_llvm: no {hvName} in context"
    let ty ← instantiateMVars d.type
    let mut acc : Array Term := #[]
    for k in [0:idx] do
      let some vd := lctx.findFromUserName? (Name.mkSimple s!"v{k}") | continue
      unless (lctx.findFromUserName? (Name.mkSimple s!"hv{k}")).isSome do continue
      if ty.hasAnyFVar (· == vd.fvarId) then acc := acc.push (mkIdent (Name.mkSimple s!"hv{k}"))
    return acc
  let extras : Array Term := match extra with
    | some e => e.raw[1].getSepArgs.map fun s => ⟨s⟩
    | none => #[]
  let fixed : Array Term := #[← `(simp_llvm), ← `(simp_llvm_option), ← `(LLVM.const?),
    ← `(umulOverflow_zeroExtend), ← `(PoisonOr.value_bind), ← `(false_and), ← `(if_false),
    ← `(true_and), ← `(BitVec.ofInt_ofNat)]
  let args := fixed ++ prev ++ extras
  evalTactic (← `(tactic| simp +decide only [$[$args:term],*] at $hvIdent:ident))
  let some nmStx := nm | return
  let xName := (⟨nmStx.raw[1]⟩ : Ident).getId
  let hName := Name.mkSimple ("h" ++ xName.toString)
  let goal ← getMainGoal
  let (e, fv) ← goal.withContext do
    let some d := (← getLCtx).findFromUserName? hvName
      | throwError "eval_llvm: no {hvName} in context"
    let some (_, _, rhs) := (← instantiateMVars d.type).eq?
      | throwError "eval_llvm: {hvName} is not an equation"
    unless rhs.isAppOfArity ``PoisonOr.value 2 do
      throwError "eval_llvm: %{idx} did not reduce to a value:{indentExpr rhs}"
    return (rhs.appArg!, d.fvarId)
  let (_, g₁) ← goal.revert #[fv]
  let (_, g₂) ← g₁.generalize #[{ expr := e, xName? := xName, hName? := hName }]
  let (_, g₃) ← g₂.introNP 1
  replaceMainGoal [g₃]

end Firedancer
