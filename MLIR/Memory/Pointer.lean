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

/-- The null pointer: block `0`, which a `WF` state never allocates. -/
def Pointer.null : Pointer :=
  ⟨⟨0⟩, 0⟩

def Pointer.offsetInBits (p : Pointer) : Nat :=
  8 * p.offset.toNat

def Pointer.add (p : Pointer) (off : BitVec 64) :=
  { p with offset := p.offset + off }

/-- The bits a pointer is stored as: its block's address plus its offset, as `ptrtoaddr` reads it
(`addr`, a state's choice of addresses). -/
def Pointer.addrBits (addr : BlockId → BitVec 64) (q : Pointer) : BitVec 64 :=
  addr q.id + q.offset

@[simp]
theorem Pointer.add_zero (p : Pointer) : (p.add 0#64) = p := by simp [Pointer.add]

/-- `add` moves within the block. -/
@[simp]
theorem Pointer.add_id (p : Pointer) (off : BitVec 64) : (p.add off).id = p.id :=
  rfl

/-- `add` moves within the block. -/
@[simp]
theorem Pointer.add_add (p : Pointer) (off off' : BitVec 64) :
    (p.add off).add off' = p.add (off + off') := by simp [Pointer.add, BitVec.add_assoc]

end

end MLIR
