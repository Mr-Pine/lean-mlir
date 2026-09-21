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

/-- `length` counts the length of the block in `bytes`  -/
structure MemoryBlock where
  (length : Nat)
  (bytes : BitVec (8 * length))

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
  mem : Std.HashMap BlockId MemoryBlock
  deriving Inhabited

structure GlobalState where
  alloc : AllocState
  mem : MemoryState

/-! ## Basic Definitions -/

instance : GetElem? MemoryState BlockId MemoryBlock (fun m i => i ∈ m.mem) where
  getElem mem id h := mem.mem[id]
  getElem? mem id := mem.mem[id]?

@[implicit_reducible]
def MemoryBlock.lengthInBits (b : MemoryBlock) : Nat :=
  8 * b.length

theorem MemoryState.getElem?_eq (m : MemoryState) (q : BlockId) : m[q]? = m.mem[q]? :=
  rfl

end
