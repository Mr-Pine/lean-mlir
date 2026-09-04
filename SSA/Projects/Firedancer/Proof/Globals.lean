/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.Firedancer.Proof.Memory

/-!
# Globals

`llvm.mlir.addressof` reads a symbol's address out of `GlobalState.globals`, so
the address is a property of the state, not of the program: every `addressof`
of a symbol names the same block at any call depth, which is what makes a
mutable global sound. The operation itself reads nothing and checks nothing, so
what a global *holds* is stated here and enters a conformance theorem as a
hypothesis.

Two predicates, because they behave differently under a write:

* `GlobalPtr s name p` -- `s` records `p` as `name`'s address. Survives every
  store, since nothing an operation can do reaches the table.
* `HoldsGlobal s name p v` -- ... and `v` is still there. A store through `p`
  invalidates this half, as it would for any other pointer.

Disjointness is *not* here. Two globals can overlap in LLVM (`unnamed_addr`
licenses constant merging, an `@alias` points into its aliasee), and so can a
global and a caller's buffer, so a spec that needs either says so. What the
loader below does give, for a module loaded from scratch, is the artifacts'
case: one block per symbol, pairwise distinct by `chainPtr_id`.
-/

namespace Firedancer
open LeanMLIR SLLVM
open InstCombine (LLVM)

/-- `s` records `p` as the address of `name`. -/
def GlobalPtr (s : GlobalState) (name : String) (p : Pointer) : Prop :=
  s.globals[name]? = some p

/-- ... and the `w`-bit value `v` is what lives there. -/
def HoldsGlobal (s : GlobalState) (name : String) (p : Pointer) {w : Nat} (v : BitVec w) :
    Prop :=
  GlobalPtr s name p ∧ ∃ h : Fits s.mem p w, readWord h = v

namespace GlobalPtr

/-- The table is write-once, so `≈` carries the address unchanged -- which is
what lets a global survive a callee. -/
theorem of_equiv {s s' : GlobalState} {name : String} {p : Pointer}
    (h : GlobalPtr s name p) (he : s ≈ s') : GlobalPtr s' name p := by
  simp only [GlobalPtr, ← he.globals]; exact h

/-- A `GlobalState` differing only in memory keeps the address: the shape every
store leaves behind. -/
@[simp] theorem splice {s : GlobalState} {name : String} {p : Pointer} {m : MemoryState} :
    GlobalPtr { s with mem := m } name p ↔ GlobalPtr s name p := Iff.rfl

end GlobalPtr

namespace HoldsGlobal

/-- The global's address, forgetting what it holds. A mutable global keeps
exactly this much across a write. -/
theorem ptr {s : GlobalState} {name : String} {p : Pointer} {w : Nat} {v : BitVec w}
    (h : HoldsGlobal s name p v) : GlobalPtr s name p := h.1

/-- The global's block predates every `alloca` the region will do, exactly as a
caller's out-parameter does -- so `chainPtr_id` separates it from the locals
with no further hypothesis. -/
theorem lt_nextFreeBlock {s : GlobalState} {name : String} {p : Pointer} {w : Nat}
    {v : BitVec w} (hs : s.WF) (h : HoldsGlobal s name p v) :
    p.id.id < s.alloc.nextFreeBlock :=
  lt_nextFreeBlock_of_fits hs h.2.1

/-- A store to another block leaves the global alone. This is where a spec's
`p.id ≠ o.id` is spent: nothing else establishes that a region's writes miss
its globals. -/
theorem splice_ne {s : GlobalState} {name : String} {p q : Pointer} {w w' : Nat}
    {v : BitVec w} {x : BitVec w'} (h : HoldsGlobal s name p v) (hq : q.id ≠ p.id) :
    HoldsGlobal { s with mem := s.mem.splice q x } name p v := by
  obtain ⟨hp, hfit, hval⟩ := h
  exact ⟨hp, (readWord_splice_ne hq hfit).imp fun _ hv => hv.trans hval⟩

/-- Transport across a state that agrees on the global's block: the shape a
callee's `≈` hands back. -/
theorem of_equiv {s s' : GlobalState} {name : String} {p : Pointer} {w : Nat}
    {v : BitVec w} (h : HoldsGlobal s name p v) (he : s ≈ s') :
    HoldsGlobal s' name p v := by
  obtain ⟨hp, hfit, hval⟩ := h
  exact ⟨hp.of_equiv he, (readWord_of_live?_eq (he.live p.id).symm hfit).imp
    fun _ hv => hv.trans hval⟩

end HoldsGlobal

/-! ## Loading a module

`ofGlobals` is the constructor: it says a state *can* satisfy every
`HoldsGlobal` at once, and is what a `#guard` or a top-level caller starts
from. No region's proof mentions it -- a global whose address came from
somewhere else is equally admissible. -/

/-- Install one global: a fresh block holding `v`, recorded under `name`. -/
def _root_.LeanMLIR.GlobalState.withGlobal (s : GlobalState) (name : String) {w : Nat} (v : BitVec w) :
    GlobalState :=
  let p : Pointer := ⟨⟨s.alloc.nextFreeBlock⟩, 0⟩
  let s' := s.afterAlloca w
  { s' with mem := s'.mem.splice p v, globals := s'.globals.insert name p }

/-- The address `withGlobal` chose: the block at the counter, as `alloca`'s. -/
@[simp] theorem _root_.LeanMLIR.GlobalState.withGlobal_ptr (s : GlobalState) (name : String) {w : Nat}
    (v : BitVec w) : (s.withGlobal name v).globals[name]? = some ⟨⟨s.alloc.nextFreeBlock⟩, 0⟩ := by
  simp [GlobalState.withGlobal]

@[simp] theorem _root_.LeanMLIR.GlobalState.withGlobal_nextFreeBlock (s : GlobalState) (name : String)
    {w : Nat} (v : BitVec w) :
    (s.withGlobal name v).alloc.nextFreeBlock = s.alloc.nextFreeBlock + 1 := rfl

/-- An earlier global keeps its entry: distinct names, distinct blocks, and the
new block is above every old one. -/
@[simp] theorem _root_.LeanMLIR.GlobalState.withGlobal_ptr_ne (s : GlobalState) {name name' : String}
    {w : Nat} (v : BitVec w) (h : name' ≠ name) :
    (s.withGlobal name v).globals[name']? = s.globals[name']? := by
  simp [GlobalState.withGlobal, Std.HashMap.getElem?_insert, Ne.symm h]

theorem _root_.LeanMLIR.GlobalState.WF.withGlobal {s : GlobalState} (hs : s.WF) (name : String) {w : Nat}
    (v : BitVec w) : (s.withGlobal name v).WF := by
  intro q hq
  -- the global's own block is the one at the entry counter, strictly below `q`
  have hne : (⟨⟨s.alloc.nextFreeBlock⟩, 0⟩ : Pointer).id ≠ q := by
    rintro rfl; simp only [GlobalState.withGlobal_nextFreeBlock] at hq; omega
  show ((s.afterAlloca w).mem.splice _ v).live? q = none
  rw [live?_splice_ne hne]
  exact (hs.afterAlloca w) q hq

/-- What `withGlobal` establishes: the global is there, and it holds `v`. -/
theorem holdsGlobal_withGlobal (s : GlobalState) (name : String) {w : Nat} (v : BitVec w) :
    HoldsGlobal (s.withGlobal name v) name ⟨⟨s.alloc.nextFreeBlock⟩, 0⟩ v := by
  refine ⟨GlobalState.withGlobal_ptr s name v, ?_⟩
  have hfit : Fits (s.afterAlloca w).mem (⟨⟨s.alloc.nextFreeBlock⟩, 0⟩ : Pointer) w :=
    fits_afterAlloca s w
  exact (readWord_splice_self v hfit).imp fun _ hv => hv

end Firedancer
