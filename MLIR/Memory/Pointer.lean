module

namespace MLIR

@[expose] public section

structure BlockId where
  id : Nat
  deriving DecidableEq, Hashable, Inhabited

structure Pointer where
  id : BlockId
  /-- Offset in bytes -/
  offset : BitVec 64
  deriving Inhabited, DecidableEq

end

end MLIR
