module

public import SSA.Projects.RIR.Run.Tactic.Init
public import SSA.Projects.RIR.Run.Tactic.Finish
public import SSA.Projects.RIR.Run.Tactic.Step.Pure
public import SSA.Projects.RIR.Run.Tactic.Step.Impure
public import SSA.Projects.RIR.Run.Tactic.Step.Call
public import SSA.Projects.RIR.Run.Tactic.Widget
public import SSA.Projects.RIR.Run.Tactic.Step.Alloca
public import SSA.Projects.RIR.Run.Tactic.Step.Addressof
public import SSA.Projects.RIR.Run.Tactic.Loop
public import SSA.Projects.RIR.Run.Tactic.Step.Pattern

/-- A literal index's bound (`x[3]` of a `Vector _ 8`) by `decide`, before core's rules: those try
`assumption` and rewrite every hypothesis, about a second per `x[i]` in a step proof's context. -/
macro_rules
  | `(tactic| get_elem_tactic) => `(tactic| decide)
