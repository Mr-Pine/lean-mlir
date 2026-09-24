module

public meta import SSA.Projects.RIR.Run.Tactic.Step.Common
public meta import Lean.Elab.Tactic

/-! The argument syntax shared by the stepping tactics. -/

namespace LeanMLIR.RIR

open Lean

public meta section

/-- `only` and `[simp args]`, as for `simp`: used to resolve the instruction's reads. -/
syntax stepSimpArgs := (&" only")? (" [" withoutPosition(Lean.Parser.Tactic.simpArg,*,?) "]")?

/-- How to bind a written value: `with v hv` names it and its equation, `inline` keeps it in the
env. -/
syntax stepNames := (" with " ident (colGt ident)?) <|> &" inline"

/-- Facts about the old state that are not carried over to the new one. -/
syntax stepConsuming := &" consuming" (ppSpace colGt ident)+

/-- The arguments shared by the stepping tactics. -/
structure StepArgs where
  value : EnvName := .auto
  hyp : EnvName := .auto
  only : Bool := false
  simpArgs : Syntax := mkNullNode
  consumed : Array Ident := #[]

/-- Read a `stepSimpArgs` node, and the optional `stepNames` and `stepConsuming` groups. -/
def StepArgs.parse (simp names consuming : Syntax) : StepArgs :=
  let (value, hyp) : EnvName × EnvName :=
    if names.isNone then (.auto, .auto)
    else
      -- `with v hv` parses as a `group`; `inline` is a (non-atom) token node
      let alt := names[0][0]
      if alt.isOfKind groupKind then
        (.named ⟨alt[1]⟩, if alt[2].isNone then .auto else .named ⟨alt[2][0]⟩)
      else (.inline, .inline)
  { value, hyp, only := !simp[0].isNone, simpArgs := simp[1],
    consumed := if consuming.isNone then #[] else consuming[0][1].getArgs.map (⟨·⟩) }

end

end LeanMLIR.RIR
