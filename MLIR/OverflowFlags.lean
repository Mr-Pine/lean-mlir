module

public import MLIR.Context
public import MLIR.IntPred

namespace MLIR

@[expose] public section

structure OverflowFlags where
  nsw : Bool := false
  nuw : Bool := false
  deriving Repr, DecidableEq, Lean.ToExpr

end

end MLIR
