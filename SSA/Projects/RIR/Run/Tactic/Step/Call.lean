module

public meta import SSA.Projects.RIR.Run.Tactic.Step.Impure
public import SSA.Projects.RIR.Run.Call

namespace LeanMLIR.RIR

open Lean Elab Tactic Meta

public meta section

syntax (name :=
  stepCall) "step_call" " using " term:max stepSimpArgs (stepNames)? (stepConsuming)? : tactic

@[tactic stepCall]
def evalStepCall : Tactic := fun stx => do
  let thm : Term := ⟨stx[2]⟩
  let args := StepArgs.parse stx[3] stx[4] stx[5] mkNullNode
  let innerDischarge ←
    `(tacticSeq| exact run_call (by
        apply $thm <;> first
          | with_reducible assumption | ne_fact | fits_fact | transport_fact
          | simp [$(mkIdent `mlir_mem):ident, *]))
  runStep args innerDischarge

end

end LeanMLIR.RIR
