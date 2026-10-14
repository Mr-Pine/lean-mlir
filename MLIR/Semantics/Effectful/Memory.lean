module

-- public import LeanMLIR.Framework

-- import SSA.Projects.SLLVM.Tactic.SimpSet
public import Std.Data.ExtHashMap.Basic
public import MLIR.Memory.Pointer
public import MLIR.Semantics.Effectful.Memory.Bits

namespace MLIR

@[expose] public section

/-- A block of `length` bytes: its bits, which of them are `defined` (bit `i` set: bit `i` was
written by an integer write), whether the object is `live` (inside its lifetime), the pointers
stored in it by their first bit, each loaded back while no integer write has defined its 64 bits
and they hold its address, and whether it is `writable` (not a `constant` global's). -/
structure MemoryBlock where
  (length : Nat)
  (bytes : BitVec (8 * length))
  (defined : BitVec (8 * length))
  (live : Bool)
  (ptrs : Nat → Option Pointer)
  (writable : Bool)

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

/-- A global's initial contents: `bytes` bytes of `bits`, defined where `defined` is set, and its
pointer members `ptrs`, each by its bit offset, the symbol of the global it points into and the
byte offset into it (`bits` undefined there); read-only if `constant`, its address insignificant if
`unnamedAddr` (an equal constant may share it). -/
structure GlobalImage where
  bytes : Nat
  bits : BitVec (8 * bytes)
  defined : BitVec (8 * bytes)
  constant : Bool
  unnamedAddr : Bool
  ptrs : List (Nat × String × BitVec 64) := []
  deriving DecidableEq

/-- An image's pointer member `(o, sym, off)`, its symbol's block by `r`: that block at `off`. -/
def GlobalImage.memberPtr (r : String → Option BlockId) : Nat × String × BitVec 64 → Option Pointer
  | (_, sym, off) => (r sym).map (⟨·, off⟩)

/-- An image's bits, each pointer member whose symbol has a block by `r` its address there. -/
def GlobalImage.linkedBits (g : GlobalImage) (r : String → Option BlockId)
    (addr : BlockId → BitVec 64) : BitVec (8 * g.bytes) :=
  g.ptrs.foldl
    (fun bs e =>
      match GlobalImage.memberPtr r e with
      | some q => Memory.spliceBits bs e.1 (q.addrBits addr)
      | none => bs)
    g.bits

/-- An image's pointer members whose symbols have blocks by `r`, by their bit offsets. -/
def GlobalImage.linkedPtrs (g : GlobalImage) (r : String → Option BlockId) :
    Nat → Option Pointer :=
  fun o => (g.ptrs.find? (·.1 == o)).bind (GlobalImage.memberPtr r)

/-- The live block a global's image is, `r` giving each symbol's block: writable unless `constant`,
each pointer member whose symbol has a block stored as a store of it leaves it (its address, not
defined by an integer write), the others undefined. -/
def GlobalImage.block (g : GlobalImage) (r : String → Option BlockId)
    (addr : BlockId → BitVec 64) : MemoryBlock :=
  ⟨g.bytes, g.linkedBits r addr, g.defined, true, g.linkedPtrs r, !g.constant⟩

/-- The program's globals: each symbol's block and image. Fixed for a run (instance-implicit in
`MemoryState`: `⟨m⟩` takes the empty one; every operation keeps it). -/
class GlobalTable where
  globals : String → Option (BlockId × GlobalImage)

/-- No globals. -/
instance : GlobalTable :=
  ⟨fun _ => none⟩

/--
`MemoryState` tracks the *content* of memory blocks, the choices LLVM leaves unspecified, and the
program's globals (both instance-implicit: `⟨m⟩` takes the defaults; every operation keeps them)
-/
@[ext]
structure MemoryState where
  mem : Std.ExtHashMap BlockId MemoryBlock
  [unspec : Unspecified]
  [table : GlobalTable]
  deriving Inhabited

@[ext]
structure GlobalState where
  alloc : AllocState
  mem : MemoryState

/-! ## Basic Definitions -/

/-- Each block's address: the state's unspecified choice. -/
def MemoryState.addr (m : MemoryState) : BlockId → BitVec 64 :=
  m.unspec.addr

/-- Each global's block and image, by symbol. -/
def MemoryState.globals (m : MemoryState) : String → Option (BlockId × GlobalImage) :=
  m.table.globals

/-- Each global's block, by symbol: what a global's pointer members resolve by. -/
def MemoryState.globalBlocks (m : MemoryState) : String → Option BlockId :=
  fun sym => (m.globals sym).map Prod.fst

/-- The block a global's image is in `m`: its pointer members resolved by `m`'s globals and
addresses. -/
def MemoryState.imageBlock (m : MemoryState) (g : GlobalImage) : MemoryBlock :=
  g.block m.globalBlocks m.addr

instance : GetElem? MemoryState BlockId MemoryBlock (fun m i => i ∈ m.mem) where
  getElem mem id h := mem.mem[id]
  getElem? mem id := mem.mem[id]?

/-- A live writable block holding `bytes`, all defined. -/
def MemoryBlock.ofBytes (length : Nat) (bytes : BitVec (8 * length)) : MemoryBlock :=
  ⟨length, bytes, BitVec.allOnes _, true, fun _ => none, true⟩

@[implicit_reducible]
def MemoryBlock.lengthInBits (b : MemoryBlock) : Nat :=
  8 * b.length

theorem MemoryState.getElem?_eq (m : MemoryState) (q : BlockId) : m[q]? = m.mem[q]? :=
  rfl

/-- A state the allocator can extend: every block below the counter, and block `0`, the null
pointer's, never allocated; each global's block there, a constant's holding its image (its pointer
members resolved, `imageBlock`), a mutable one's writable, and no two globals in one block unless
constants an `unnamedAddr` one may merge. -/
structure GlobalState.WF (s : GlobalState) : Prop where
  bound : ∀ k ∈ s.mem.mem, k.id < s.alloc.nextFreeBlock
  pos : 0 < s.alloc.nextFreeBlock
  null : (⟨0⟩ : BlockId) ∉ s.mem.mem
  global : ∀ sym b g, s.mem.globals sym = some (b, g) →
    if g.constant then s.mem[b]? = some (s.mem.imageBlock g)
    else ∃ blk, s.mem[b]? = some blk ∧ blk.writable = true ∧ blk.length = g.bytes
  merged : ∀ sym sym' b g g', s.mem.globals sym = some (b, g) → s.mem.globals sym' = some (b, g') →
    sym ≠ sym' → g.constant = true ∧ g'.constant = true ∧ (g.unnamedAddr || g'.unnamedAddr) = true

end
