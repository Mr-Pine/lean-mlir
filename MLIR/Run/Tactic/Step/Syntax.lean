module

public meta import MLIR.Run.Tactic.Step.Common
public meta import Lean.Elab.Tactic

/-! The argument syntax shared by the stepping tactics. -/

namespace MLIR

open Lean

public meta section

/-- `only` and `[simp args]`, as for `simp`: used to resolve the instruction's reads. -/
syntax stepSimpArgs := (&" only")? (" [" withoutPosition(Lean.Parser.Tactic.simpArg,*,?) "]")?

/-- How to bind a written value: `with v hv` names it and its equation, `named` names it `vN`,
`inline` keeps it in the env. -/
syntax stepNames := (" with " ident (colGt ident)?) <|> &" inline" <|> &" named"

/-- Facts about the old state that are not carried over to the new one. -/
syntax stepConsuming := &" consuming" (ppSpace colGt ident)+

/-- `opaque`: do not unfold the values the instruction reads into their definitions. -/
syntax stepOpaque := colGt &" opaque"

/-- The arguments shared by the stepping tactics. -/
structure StepArgs where
  value : EnvName := .auto
  hyp : EnvName := .auto
  only : Bool := false
  simpArgs : Syntax := mkNullNode
  consumed : Array Ident := #[]
  expand : Bool := true

/-- Read a `stepSimpArgs` node, and the optional `stepNames` and `stepConsuming` groups. Without
names, the value is inlined, or named `vN` if `named` (loads, `alloca`). -/
def StepArgs.parse (simp names consuming sopaque : Syntax) (named := false) : StepArgs :=
  let (value, hyp) : EnvName × EnvName :=
    if names.isNone then if named then (.auto, .auto) else (.inline, .inline)
    else
      -- `with v hv` parses as a `group`; `inline`/`named` are (non-atom) token nodes
      let alt := names[0][0]
      if alt.isOfKind groupKind then
        (.named ⟨alt[1]⟩, if alt[2].isNone then .auto else .named ⟨alt[2][0]⟩)
      else
        if alt.getAtomVal.endsWith "named" || alt[0].getAtomVal.endsWith "named" then (.auto, .auto)
        else (.inline, .inline)
  {
    value,
    hyp,
    only := !simp[0].isNone,
    simpArgs := simp[1],
    consumed := if consuming.isNone then #[] else consuming[0][1].getArgs.map (⟨·⟩),
    expand := sopaque.isNone,
  }

end

end MLIR
