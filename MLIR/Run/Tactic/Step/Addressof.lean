module

public meta import MLIR.Run.Tactic.Step.Alloca
public meta import MLIR.Semantics.GlobalInitializer
public import MLIR.Run.Memory

namespace MLIR

open Lean Elab Tactic Meta

public meta section

/-- `step_impure` for an `addressof` of a global `g`, closing it with `run_addressof_wrap` and
`hv : ∀ s, g.value s = .value (Ty.wrap r, s)`, `g`'s type without padding. As with `step_alloca`,
the new block is named `x` and kept apart from the pointers with memory facts. -/
syntax (name := stepAddressof) "step_addressof" term:max (stepNames)? (stepConsuming)? : tactic

/-- Close the run goal of `addressof` of a global `g` with `run_addressof_wrap (hv _)`, for
`hv : ∀ s, g.value s = .value (Ty.wrap r, s)`; for a value with undefined members, with
`run_addressof_def`, its bits and their definedness as literals. -/
elab "addressof_value" hv:term:max : tactic =>
  withMainContext do
    -- `g`'s type, from `hv`'s statement
    let hv ← elabTerm hv none
    let ty ← inferType hv
    let some (v, x) ←
        forallTelescope ty fun _ body => do
          let some v := body.find? (·.isAppOfArity ``GlobalInitializer.value 1) | return none
          -- `.value (x, s)`
          let some (_, _, rhs) := body.eq? | return none
          unless rhs.isAppOfArity ``PoisonOr.value 2 do
            return none
          return some (v, rhs.appArg!.appFn!.appArg!)
      | throwError "`addressof_value`: {hv} is not about a global's `value`:{indentExpr ty}"
    -- the type spelled out, so the stored bits are about it rather than `g.t`
    let t ← reduce (← mkAppM ``GlobalInitializer.t #[v.appArg!])
    -- the width and byte count as literals, so the state's `storeAt` and the bits agree on them
    let w ← reduce (← mkAppM ``Ty.width #[t])
    let some w := w.nat? <|> w.rawNatLit? | throwError "`addressof_value`: width {w} is not a literal"
    let n := (w + 7) / 8
    unless x.isAppOf ``Ty.wrap do
      -- the bits and their definedness, evaluated
      let fd ← mkAppM ``Ty.flattenDef #[t, x]
      let lit (e : Expr) : MetaM Nat := do
        let r ← withTransparency .all (reduce (← mkAppM ``BitVec.toNat #[e]))
        let some k := r.nat? <|> r.rawNatLit?
          | throwError "`addressof_value`: the initializer's bits are no literal{indentExpr r}"
        return k
      let b ← lit (← mkAppM ``Prod.fst #[fd])
      let d ← lit (← mkAppM ``Prod.snd #[fd])
      return ←
        evalTactic
          (← `(tactic|
              exact run_addressof_def (t := $(← Term.exprToSyntax t)) (w := $(quote w))
                (b := BitVec.ofNat $(quote w) $(quote b)) (d := BitVec.ofNat $(quote w) $(quote d))
                (n := $(quote n)) ($(← Term.exprToSyntax hv) _) (by simp) rfl (by decide +kernel)
                rfl))
    evalTactic
        (← `(tactic|
            exact run_addressof_wrap (t := $(← Term.exprToSyntax t)) (w := $(quote w)) (n := $(quote n))
              ($(← Term.exprToSyntax hv) _) (by simp) (by decide) rfl rfl))

@[tactic stepAddressof]
def evalStepAddressof : Tactic := fun stx => do
  addAllocaFreshness "step_addressof"
  runStep (StepArgs.parse mkNullNode stx[2] stx[3] mkNullNode (named := true))
      (← `(tacticSeq| addressof_value $(⟨stx[1]⟩)))
  nameAllocaSlot

end

end MLIR
