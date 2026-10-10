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

/-- What LLVM leaves unspecified and the model fixes per run, constrained by nothing: a proof about
a run holds for every choice. -/
class Unspecified where
  /-- Each block's address, as `ptrtoaddr` reads it; blocks may overlap, so a proof holds for
  every disjoint placement too. -/
  addr : BlockId → BitVec 64
  /-- `memcmp`'s result for `n` unequal bytes, before it is given the order's sign. -/
  memcmp : (n : Nat) → BitVec (8 * n) → BitVec (8 * n) → BitVec 32
  /-- `bcmp`'s result for `n` unequal bytes, before it is made nonzero. -/
  bcmp : (n : Nat) → BitVec (8 * n) → BitVec (8 * n) → BitVec 32

/-- The choice `⟨m⟩` makes when it builds a state from scratch: all zero. -/
instance : Unspecified :=
  ⟨fun _ => 0, fun _ _ _ => 0, fun _ _ _ => 0⟩

/--
`MemoryState` tracks the *content* of memory blocks, and the choices LLVM leaves unspecified
(instance-implicit: `⟨m⟩` takes the default; every operation keeps them)
-/
@[ext]
structure MemoryState where
  mem : Std.ExtHashMap BlockId MemoryBlock
  [unspec : Unspecified]
  deriving Inhabited

@[ext]
structure GlobalState where
  alloc : AllocState
  mem : MemoryState

/-! ## Basic Definitions -/

/-- Each block's address: the state's unspecified choice. -/
def MemoryState.addr (m : MemoryState) : BlockId → BitVec 64 :=
  m.unspec.addr

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
