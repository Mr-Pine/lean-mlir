module

public import SSA.Projects.RIR.Semantics.Effectful.Memory.Operations
import Std.Data.ExtHashMap.Lemmas

/-!
# Explicit byte-global contracts

RIR pointers retain allocation provenance, not machine addresses. An immutable LLVM byte global
can therefore be bound to the start of a distinct pre-existing block. `ByteGlobal.Present` is the
exact initializer contract; it does not allocate on each `addressof`. The preservation lemmas
require writes to have a different block id. They do not silently assume writes to a constant
are impossible, or turn mutable memory into immutable memory.

Alignment is retained as source information. RIR currently has no machine-address alignment
semantics, so `Present` deliberately makes no claim about physical addresses. A machine-memory
refinement must supply a base address divisible by `alignment`.
-/

namespace LeanMLIR.RIR

@[expose] public section

/-- A relocation-free LLVM constant with an explicit alignment in bytes. -/
structure ByteGlobal where
  symbol : String
  length : Nat
  bytes : BitVec (8 * length)
  alignment : Nat
  alignment_pos : 0 < alignment

/-- The symbol's address has a stable allocation identity, at offset zero. -/
def ByteGlobal.address (_ : ByteGlobal) (id : BlockId) : Pointer := ⟨id, 0⟩

/-- Exact contents of the whole global allocation, not merely a prefix. -/
def ByteGlobal.Present (g : ByteGlobal) (id : BlockId) (m : MemoryState) : Prop :=
  m[id]? = some ⟨g.length, g.bytes⟩

/-- An explicit symbol binding. Distinct definitions occupy distinct allocation blocks. -/
structure GlobalBinding where
  definition : ByteGlobal
  id : BlockId

/-- Initial-state contract for all bound byte globals. In addition to exact bytes, require
fresh allocation state and distinct provenance. This contract must be preserved by the caller's
writes; binding a name alone does not assert it. -/
def GlobalsWF (bindings : List GlobalBinding) (s : GlobalState) : Prop :=
  s.WF ∧ (bindings.map (·.id)).Nodup ∧
    ∀ b ∈ bindings, b.definition.Present b.id s.mem

/-- Install a global before executing a function. The caller chooses a fresh id; no instruction
uses this operation, so repeated `addressof` does not overwrite memory or allocate fresh copies. -/
def ByteGlobal.install (g : ByteGlobal) (s : GlobalState) : GlobalState :=
  { alloc := ⟨s.alloc.nextFreeBlock + 1⟩,
    mem := ⟨s.mem.mem.insert ⟨s.alloc.nextFreeBlock⟩ ⟨g.length, g.bytes⟩⟩ }

@[simp] theorem ByteGlobal.present_install (g : ByteGlobal) (s : GlobalState) :
    g.Present ⟨s.alloc.nextFreeBlock⟩ (g.install s).mem := by
  simp [ByteGlobal.Present, ByteGlobal.install, MemoryState.getElem?_eq]

/-- Installing a global preserves the freshness invariant used by stack allocation. -/
theorem ByteGlobal.wf_install (g : ByteGlobal) {s : GlobalState} (h : s.WF) :
    (g.install s).WF := by
  intro k hk
  simp only [ByteGlobal.install, Std.ExtHashMap.mem_insert] at hk ⊢
  rcases hk with hk | hk
  · have : (⟨s.alloc.nextFreeBlock⟩ : BlockId) = k := by simpa using hk
    subst this
    simp
  · have := h k hk
    omega

theorem ByteGlobal.Present.fits {g : ByteGlobal} {id : BlockId} {m : MemoryState}
    (h : g.Present id m) : Fits m (g.address id) (8 * g.length) := by
  exact ⟨⟨g.length, g.bytes⟩, h, by simp [ByteGlobal.address, Pointer.offsetInBits,
    MemoryBlock.lengthInBits]⟩

@[simp] theorem ByteGlobal.Present.readAt {g : ByteGlobal} {id : BlockId} {m : MemoryState}
    (h : g.Present id m) : m.readAt (g.address id) (8 * g.length) = g.bytes := by
  simp [MemoryState.readAt, ByteGlobal.address, ByteGlobal.Present] at h ⊢
  rw [h]
  simp [Pointer.offsetInBits]

/-- Writes through a pointer with another allocation provenance preserve the initializer. -/
theorem ByteGlobal.Present.storeAt {g : ByteGlobal} {id : BlockId} {m : MemoryState}
    {p : Pointer} {w : Nat} {v : BitVec w} (h : g.Present id m) (hne : id ≠ p.id) :
    g.Present id (m.storeAt p v) := by
  unfold ByteGlobal.Present at *
  exact (MemoryState.getElem?_storeAt_ne (q := g.address id) hne).trans h

/-- Stack allocation cannot alias a global already present in a well-formed initial state. -/
theorem ByteGlobal.Present.alloca {g : ByteGlobal} {id : BlockId} {s : GlobalState}
    (h : g.Present id s.mem) (hwf : s.WF) : g.Present id (s.alloca n).mem := by
  have hf := h.fits
  unfold ByteGlobal.Present at *
  have hne : id ≠ s.allocaPtr.id := GlobalState.ne_allocaPtr_of_fits hwf hf
  rw [GlobalState.getElem?_alloca hne]
  exact h

end
end LeanMLIR.RIR
