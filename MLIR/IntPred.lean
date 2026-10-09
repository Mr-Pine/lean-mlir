module

namespace MLIR

@[expose] public section

/-- `llvm.icmp`'s predicates, in MLIR's numbering: `eq` is 0, …, `uge` is 9. -/
inductive IntPred
  | eq
  | ne
  | slt
  | sle
  | sgt
  | sge
  | ult
  | ule
  | ugt
  | uge

end

end MLIR
