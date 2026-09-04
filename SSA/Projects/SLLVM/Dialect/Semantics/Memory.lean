import LeanMLIR.Framework

import SSA.Projects.SLLVM.Tactic.SimpSet

namespace LeanMLIR

structure BlockId where
  id : Nat
  deriving DecidableEq, Hashable, Inhabited

/-!
**SIMPLIFICATION**
We don't support storing poison, only fully-defined values!
-/

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

structure Pointer where
  id : BlockId
  /-- Offset in bytes -/
  offset : BitVec 64
  deriving DecidableEq, Inhabited

/--
`GlobalState` is the whole machine state: the allocator, the contents of
memory, and the module's global symbols.

`globals` is *write-once*: `GlobalState.ofGlobals` installs it when a module is
loaded and no operation may add, remove or repoint an entry -- `addressof` only
reads it. That is what makes every `addressof` of a symbol, at any call depth,
name the same block. The invariant is not structural; `GlobalState.Equiv`
carries it, so a region that touched the table could not satisfy its spec.

The value is a `Pointer` rather than a `BlockId` because an `@alias` points
*into* an existing global at an offset.
-/
structure GlobalState where
  alloc : AllocState
  mem : MemoryState
  globals : Std.HashMap String Pointer

/-! ## Basic Definitions -/

instance : GetElem? MemoryState BlockId Block (fun m i => i ∈ m.mem) where
  getElem mem id h := mem.mem[id]
  getElem? mem id  := mem.mem[id]?

def LiveBlock.lengthInBits (b : LiveBlock) : Nat :=
  8 * b.length

def Pointer.offsetInBits (p : Pointer) : Nat :=
  8 * p.offset.toNat

def Pointer.withOffset (p: Pointer) (n: BitVec 64) := Pointer.mk p.id (p.offset + n)

/-! ## Refinement -/
section Refinement

instance : Refinement AllocState where
  IsRefinedBy s t := s = t

instance : Refinement MemoryState where
  IsRefinedBy s t := ∀ (id : BlockId),
    s[id]? = t[id]?

instance : Refinement GlobalState where
  IsRefinedBy s t :=
    s.alloc ⊑ t.alloc ∧ s.mem ⊑ t.mem ∧ s.globals = t.globals



section Lemmas

@[simp_sllvm]
theorem GlobalState.isRefinedBy_iff (s t : GlobalState) :
    s ⊑ t ↔ s.alloc ⊑ t.alloc ∧ s.mem ⊑ t.mem ∧ s.globals = t.globals := by
  rfl

@[simp_sllvm]
theorem AllocState.isRefinedBy_rfl (s : AllocState) :
    s ⊑ s := by
  rfl

@[simp_sllvm]
theorem MemoryState.isRefinedBy_rfl (s : MemoryState) :
    s ⊑ s := by
  intro id; rfl

end Lemmas
end Refinement
