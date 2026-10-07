module

public meta import SSA.Projects.RIR.Run.Tactic.Step.Alloca
public meta import SSA.Projects.RIR.Semantics.GlobalInitializer
public import SSA.Projects.RIR.Run.Memory

namespace LeanMLIR.RIR

open Lean Elab Tactic Meta

public meta section

/-- `step_impure` for an `addressof` of a global `g`, closing it with `run_addressof_wrap` and
`hv : ∀ s, g.value s = .value (Ty.wrap r, s)`. As with `step_alloca`, the new block is named `x` and
kept apart from the pointers with `Fits` facts. -/
syntax (name := stepAddressof) "step_addressof" term:max (stepNames)? (stepConsuming)? : tactic

/-- Close the run goal of `addressof` of a global `g` with `run_addressof_wrap (hv _)`, for
`hv : ∀ s, g.value s = .value (Ty.wrap r, s)`. -/
elab "addressof_value" hv:term:max : tactic =>
  withMainContext do
    -- `g`'s type, from `hv`'s statement
    let hv ← elabTerm hv none
    let ty ← inferType hv
    let some v ←
        forallTelescope ty fun _ body =>
          return body.find? (·.isAppOfArity ``GlobalInitializer.value 1)
      | throwError "`addressof_value`: {hv} is not about a global's `value`:{indentExpr ty}"
    -- the type spelled out, so the stored bits are about it rather than `g.t`
    let t ← reduce (← mkAppM ``GlobalInitializer.t #[v.appArg!])
    -- the width and byte count as literals, so the state's `storeAt` and the bits agree on them
    let w ← reduce (← mkAppM ``Ty.width #[t])
    let some w := w.nat? <|> w.rawNatLit? | throwError "`addressof_value`: width {w} is not a literal"
    let n := (w + 7) / 8
    evalTactic
        (← `(tactic|
            exact run_addressof_wrap (t := $(← Term.exprToSyntax t)) (w := $(quote w)) (n := $(quote n))
              ($(← Term.exprToSyntax hv) _) (by simp) rfl rfl))

@[tactic stepAddressof]
def evalStepAddressof : Tactic := fun stx => do
  addAllocaFreshness "step_addressof"
  runStep (StepArgs.parse mkNullNode stx[2] stx[3] mkNullNode (named := true))
      (← `(tacticSeq| addressof_value $(⟨stx[1]⟩)))
  nameAllocaSlot

end

end LeanMLIR.RIR
