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

def Pointer.offsetInBits (p : Pointer) : Nat :=
  8 * p.offset.toNat

def Pointer.add (p : Pointer) (off : BitVec 64) :=
  { p with offset := p.offset + off }

/-- `add` moves within the block. -/
@[simp]
theorem Pointer.add_id (p : Pointer) (off : BitVec 64) : (p.add off).id = p.id :=
  rfl

end

end MLIR
