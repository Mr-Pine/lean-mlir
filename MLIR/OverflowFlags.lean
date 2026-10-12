module

public import MLIR.Context
public import MLIR.IntPred

namespace MLIR

@[expose] public section

structure OverflowFlags where
  nsw : Bool := false
  nuw : Bool := false
  deriving Repr, DecidableEq, Lean.ToExpr

/-- A `getelementptr`'s no-wrap flags: `nusw` (also set by `inbounds`, whose bounds are not
checked), `nuw`. -/
structure GepFlags where
  nusw : Bool := false
  nuw : Bool := false
  deriving Repr, DecidableEq, Lean.ToExpr

end

end MLIR
