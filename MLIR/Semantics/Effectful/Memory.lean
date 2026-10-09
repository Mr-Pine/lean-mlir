module

-- public import LeanMLIR.Framework

-- import SSA.Projects.SLLVM.Tactic.SimpSet
public import Std.Data.ExtHashMap.Basic
public import MLIR.Memory.Pointer

namespace MLIR

@[expose] public section

/-- A block of `length` bytes: its bits, which of them are `defined` (bit `i` set: bit `i` was
written), and whether the object is `live` (inside its lifetime). -/
structure MemoryBlock where
  (length : Nat)
  (bytes : BitVec (8 * length))
  (defined : BitVec (8 * length))
  (live : Bool)

/--
`AllocState` keeps a counter of available blockIds
-/
structure AllocState where
  nextFreeBlock : Nat
  deriving Inhabited

/--
`MemoryState` tracks the *content* of memory blocks
-/
@[ext]
structure MemoryState where
  mem : Std.ExtHashMap BlockId MemoryBlock
  deriving Inhabited

@[ext]
structure GlobalState where
  alloc : AllocState
  mem : MemoryState

/-! ## Basic Definitions -/

instance : GetElem? MemoryState BlockId MemoryBlock (fun m i => i ∈ m.mem) where
  getElem mem id h := mem.mem[id]
  getElem? mem id := mem.mem[id]?

/-- A live block holding `bytes`, all defined. -/
def MemoryBlock.ofBytes (length : Nat) (bytes : BitVec (8 * length)) : MemoryBlock :=
  ⟨length, bytes, BitVec.allOnes _, true⟩

@[implicit_reducible]
def MemoryBlock.lengthInBits (b : MemoryBlock) : Nat :=
  8 * b.length

theorem MemoryState.getElem?_eq (m : MemoryState) (q : BlockId) : m[q]? = m.mem[q]? :=
  rfl

/-- A state the allocator can extend: every block below the counter, and block `0`, the null
pointer's, never allocated. -/
structure GlobalState.WF (s : GlobalState) : Prop where
  bound : ∀ k ∈ s.mem.mem, k.id < s.alloc.nextFreeBlock
  pos : 0 < s.alloc.nextFreeBlock
  null : (⟨0⟩ : BlockId) ∉ s.mem.mem

end
