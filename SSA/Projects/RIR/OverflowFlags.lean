module

public import SSA.Projects.RIR.Context
public import SSA.Projects.RIR.IntPred

namespace LeanMLIR.RIR

@[expose] public section

structure OverflowFlags where
  nsw : Bool := false
  nuw : Bool := false
  deriving Repr, DecidableEq, Lean.ToExpr

end

end LeanMLIR.RIR
