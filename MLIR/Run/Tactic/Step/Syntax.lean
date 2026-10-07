module

public meta import MLIR.Run.Tactic.Step.Common
public meta import Lean.Elab.Tactic

/-! The argument syntax shared by the stepping tactics. -/

namespace MLIR

open Lean

public meta section

/-- `only` and `[simp args]`, as for `simp`: used to resolve the instruction's reads. -/
syntax stepSimpArgs := (&" only")? (" [" withoutPosition(Lean.Parser.Tactic.simpArg,*,?) "]")?

/-- `transparent`: a named value that later steps still unfold, as an unnamed one. -/
syntax stepTransparent := &" transparent"

/-- How to bind a written value: `with v hv` names it and its equation, `named` names it `vN`,
`inline` keeps it in the env. A named value stays folded in later steps unless `transparent`.
`hv` is never `consuming`, which starts `stepConsuming`. -/
syntax stepNames :=
  (" with" (stepTransparent)? ppSpace ident (colGt !&"consuming" ident)?) <|>
    &" inline" <|> (&" named" (stepTransparent)?)

/-- Facts about the old state that are not carried over to the new one. -/
syntax stepConsuming := &" consuming" (ppSpace colGt ident)+

/-- `opaque`: do not unfold the unnamed values the instruction reads into their definitions; named
ones never unfold. -/
syntax stepOpaque := colGt &" opaque"

/-- The first atom in `s`, trimmed. -/
private partial def firstAtom (s : Syntax) : String :=
  match s with
  | .atom _ v => v.trimAscii.toString
  | .node _ _ args => args[0]?.map firstAtom |>.getD ""
  | _ => ""

/-- Read a `stepSimpArgs` node, and the optional `stepNames` and `stepConsuming` groups. Without
names, the value is inlined, or named `vN` if `named` (loads, `alloca`), untagged. -/
def StepArgs.parse (simp names consuming sopaque : Syntax) (named := false) : StepArgs :=
  let (value, hyp, tag) : EnvName × EnvName × Bool :=
    if names.isNone then if named then (.auto, .auto, false) else (.inline, .inline, false)
    else
      let alt := names[0][0]
      match firstAtom alt with
      | "with" =>
        -- `with (transparent)? v (hv)?`
        (.named ⟨alt[2]⟩, if alt[3].isNone then .auto else .named ⟨alt[3][0]⟩, alt[1].isNone)
      | "named" => (.auto, .auto, alt[1].isNone)
      | _ => (.inline, .inline, false)
  {
    value,
    hyp,
    tag,
    only := !simp[0].isNone,
    simpArgs := simp[1],
    consumed := if consuming.isNone then #[] else consuming[0][1].getArgs.map (⟨·⟩),
    expand := sopaque.isNone,
  }

end

end MLIR
