module

public import MLIR.Run.Tactic.Init
public import MLIR.Run.Tactic.Finish
public import MLIR.Run.Tactic.Step.Pure
public import MLIR.Run.Tactic.Step.Impure
public import MLIR.Run.Tactic.Step.Call
public import MLIR.Run.Tactic.Widget
public import MLIR.Run.Tactic.Step.Alloca
public import MLIR.Run.Tactic.Step.Addressof
public import MLIR.Run.Tactic.Loop
public import MLIR.Run.Tactic.Step.Pattern

/-- A literal index's bound (`x[3]` of a `Vector _ 8`) by `decide`, before core's rules: those try
`assumption` and rewrite every hypothesis, about a second per `x[i]` in a step proof's context. -/
macro_rules
  | `(tactic| get_elem_tactic) => `(tactic| decide)
