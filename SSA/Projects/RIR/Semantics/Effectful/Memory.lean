module

-- public import LeanMLIR.Framework

-- import SSA.Projects.SLLVM.Tactic.SimpSet
public import Std.Data.HashMap.Basic
public import SSA.Projects.RIR.Memory.Pointer

namespace LeanMLIR.RIR

/-!
**SIMPLIFICATION**
We don't support storing poison, only fully-defined values!
-/

@[expose] public section

structure LiveBlock where
  (length : Nat)
  (bytes : BitVec (8 * length))

inductive Block where
  /-- A block of memory which was allocated and then freed. -/
  | dead
  /-- A live piece of memory (i.e., has been allocated and not yet freed). -/
  | live (b : LiveBlock)

/--
`AllocState` keeps a counter of available blockIds
-/
structure AllocState where
  nextFreeBlock : Nat
  deriving Inhabited

/--
`MemoryState` tracks the *content* of memory blocks
-/
structure MemoryState where
  mem : Std.HashMap BlockId Block
  deriving Inhabited

structure GlobalState where
  alloc : AllocState
  mem : MemoryState

/-! ## Basic Definitions -/

instance : GetElem? MemoryState BlockId Block (fun m i => i ∈ m.mem) where
  getElem mem id h := mem.mem[id]
  getElem? mem id := mem.mem[id]?

@[implicit_reducible]
def LiveBlock.lengthInBits (b : LiveBlock) : Nat :=
  8 * b.length

def Pointer.offsetInBits (p : Pointer) : Nat :=
  8 * p.offset.toNat

end
