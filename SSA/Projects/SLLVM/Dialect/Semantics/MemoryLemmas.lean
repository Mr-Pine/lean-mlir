/-
Released under Apache 2.0 license as described in the file LICENSE.
-/

import SSA.Projects.SLLVM.Dialect.Semantics.MemorySemantics

/-!
# Reasoning about SLLVM memory

The memory operations denote into `MemorySSAM`/`EffectM`, whose `do`-blocks
`simp_denote` cannot see through: normalising a program that touches memory
leaves a raw `StateT` term with `Std.HashMap` operations exposed.

The lemmas here close that gap for straight-line code. They are all in
*success* form -- "given that the pointer addresses a live block with room, the
run equals this state" -- rather than case-splitting on UB, because that is the
shape a proof about a kernel with known-good pointers actually needs.
-/

namespace LeanMLIR
namespace SLLVM
open InstCombine (LLVM)

/-! ## Well-addressed pointers -/

/-- `MemoryState`'s `GetElem?` is the underlying map's, definitionally; naming
that lets `Std.HashMap` lemmas apply after a `rw`. -/
theorem MemoryState.getElem?_eq (m : MemoryState) (q : BlockId) : m[q]? = m.mem[q]? := rfl

/--
`Fits m p n` says `p` addresses a live block of `m` with at least `n` bits
available from `p`'s offset -- exactly the condition under which a load or
store of `n` bits at `p` does not raise UB.
-/
def Fits (m : MemoryState) (p : Pointer) (n : Nat) : Prop :=
  ∃ block : LiveBlock, m[p.id]? = some (.live block) ∧ p.offsetInBits + n ≤ block.lengthInBits

/-- The memory state after a successful store of the bits `x` at `p`. -/
def _root_.LeanMLIR.MemoryState.splice (m : MemoryState) (p : Pointer) {w : Nat}
    (x : BitVec w) : MemoryState :=
  match m[p.id]? with
  | some (.live block) =>
      let block' : LiveBlock :=
        { block with bytes := spliceBits block.bytes p.offsetInBits x }
      { m with mem := m.mem.insert p.id (.live block') }
  | _ => m

/-- The spliced block, when the pointer addresses a live one. -/
theorem getElem?_splice_self {m : MemoryState} {p : Pointer} {w : Nat} {x : BitVec w}
    {block : LiveBlock} (hblk : m[p.id]? = some (.live block)) :
    (m.splice p x)[p.id]?
      = some (.live { block with bytes := spliceBits block.bytes p.offsetInBits x }) := by
  unfold MemoryState.splice
  rw [hblk, MemoryState.getElem?_eq]
  exact Std.HashMap.getElem?_insert_self

/-- A store leaves every other block alone. -/
@[simp_sllvm]
theorem getElem?_splice_ne {m : MemoryState} {p : Pointer} {w : Nat} {x : BitVec w}
    {q : BlockId} (h : p.id ≠ q) : (m.splice p x)[q]? = m[q]? := by
  unfold MemoryState.splice
  split
  · rw [MemoryState.getElem?_eq, MemoryState.getElem?_eq, Std.HashMap.getElem?_insert]
    simp [h]
  · rfl

/-- A store does not change which blocks are live, nor their size, so anything
that fitted before still fits. -/
@[simp_sllvm]
theorem fits_splice {m : MemoryState} {p q : Pointer} {w n : Nat} {x : BitVec w}
    (h : Fits m q n) : Fits (m.splice p x) q n := by
  obtain ⟨block, hblk, hlen⟩ := h
  by_cases hpq : p.id = q.id
  · refine ⟨{ block with bytes := spliceBits block.bytes p.offsetInBits x }, ?_, hlen⟩
    rw [← hpq] at hblk ⊢
    exact getElem?_splice_self hblk
  · exact ⟨block, by rw [getElem?_splice_ne hpq, hblk], hlen⟩

/-! ## Frame deallocation

An impure call ends by `MemoryState.killFrom n₀`, the deallocation of its
frame. These two say what that does per block: nothing below `n₀` -- the
lemma a load after a call needs, since caller blocks predate the call's
counter snapshot -- and death at or above it. -/

/-- Killing a frame leaves every block allocated before it alone. -/
theorem getElem?_killFrom_of_lt {m : MemoryState} {n₀ : Nat} {q : BlockId}
    (h : q.id < n₀) : (m.killFrom n₀)[q]? = m[q]? := by
  have hn : ¬ n₀ ≤ q.id := by omega
  simp only [MemoryState.getElem?_eq, MemoryState.killFrom, Std.HashMap.getElem?_map]
  simp [hn]

/-- Every block of the frame is dead afterwards. -/
theorem getElem?_killFrom_of_le {m : MemoryState} {n₀ : Nat} {q : BlockId}
    (h : n₀ ≤ q.id) : (m.killFrom n₀)[q]? = m[q]?.map fun _ => .dead := by
  simp only [MemoryState.getElem?_eq, MemoryState.killFrom, Std.HashMap.getElem?_map]
  simp [h]

/-- The live block at `q`, if any. A dead block and no block at all are the
same to every access, so this is all of a memory that a program can observe. -/
def _root_.LeanMLIR.MemoryState.live? (m : MemoryState) (q : BlockId) : Option LiveBlock :=
  match m[q]? with
  | some (.live b) => some b
  | _ => none

theorem live?_killFrom_of_lt {m : MemoryState} {n₀ : Nat} {q : BlockId}
    (h : q.id < n₀) : (m.killFrom n₀).live? q = m.live? q := by
  simp only [MemoryState.live?, getElem?_killFrom_of_lt h]

theorem live?_killFrom_of_le {m : MemoryState} {n₀ : Nat} {q : BlockId}
    (h : n₀ ≤ q.id) : (m.killFrom n₀).live? q = none := by
  simp only [MemoryState.live?, getElem?_killFrom_of_le h]
  cases m[q]? <;> rfl

/-- Two states no program can tell apart: the same counter, the same symbol
table and the same live blocks. This is what a function that "does not touch
the stack" preserves -- its frame is dead on return, not absent.

The `globals` conjunct is what holds a region to the write-once symbol table:
every conformance spec ends in `output_state ≈ s'`, so a region that repointed
a global could not satisfy its spec. -/
structure _root_.LeanMLIR.GlobalState.Equiv (s s' : GlobalState) : Prop where
  /-- The same allocation counter. -/
  alloc : s.alloc = s'.alloc
  /-- The same symbol table -- the write-once invariant, stated where every
  conformance spec already has to discharge it. -/
  globals : s.globals = s'.globals
  /-- The same live blocks. Dead and absent are the same to every access, so
  this is all of memory a program can observe. -/
  live : ∀ q, s.mem.live? q = s'.mem.live? q

instance : HasEquiv GlobalState := ⟨GlobalState.Equiv⟩

theorem _root_.LeanMLIR.GlobalState.equiv_def {s s' : GlobalState} :
    s ≈ s' ↔ s.alloc = s'.alloc ∧ s.globals = s'.globals
      ∧ ∀ q, s.mem.live? q = s'.mem.live? q :=
  ⟨fun h => ⟨h.alloc, h.globals, h.live⟩, fun ⟨a, g, l⟩ => ⟨a, g, l⟩⟩

@[refl] theorem _root_.LeanMLIR.GlobalState.Equiv.refl (s : GlobalState) : s ≈ s := ⟨rfl, rfl, fun _ => rfl⟩

@[symm] theorem _root_.LeanMLIR.GlobalState.Equiv.symm {s s' : GlobalState} (h : s ≈ s') : s' ≈ s :=
  ⟨h.alloc.symm, h.globals.symm, fun q => (h.live q).symm⟩

@[trans] theorem _root_.LeanMLIR.GlobalState.Equiv.trans {s s' s'' : GlobalState} (h : s ≈ s') (h' : s' ≈ s'') :
    s ≈ s'' :=
  ⟨h.alloc.trans h'.alloc, h.globals.trans h'.globals, fun q => (h.live q).trans (h'.live q)⟩

/-! ### The write-once symbol table

Every rebuild of a `GlobalState` in the model carries `globals` through
unchanged; these are the `rfl`s that let a walk forget about it. -/

@[simp, simp_sllvm]
theorem globals_afterAlloca (s : GlobalState) (w : Nat) :
    (s.afterAlloca w).globals = s.globals := rfl

@[simp, simp_sllvm]
theorem globals_popFrame (s : GlobalState) (m : MemoryState) :
    (s.popFrame m).globals = s.globals := rfl

/-- `s` is *well-formed* when no block at or above its counter is live, the
invariant `alloca` and `killFrom` keep. -/
def _root_.LeanMLIR.GlobalState.WF (s : GlobalState) : Prop :=
  ∀ q : BlockId, s.alloc.nextFreeBlock ≤ q.id → s.mem.live? q = none

/-- `WF` speaks only of the counter and of `live?`, and `≈` equates both, so it
transports along an equivalence. -/
theorem _root_.LeanMLIR.GlobalState.WF.of_equiv {s s' : GlobalState}
    (hs : s.WF) (h : s ≈ s') : s'.WF := by
  intro q hq
  rw [← h.live q]
  exact hs q (by rw [h.alloc]; exact hq)

theorem _root_.LeanMLIR.GlobalState.WF.afterAlloca {s : GlobalState} (hs : s.WF) (w : Nat) :
    (s.afterAlloca w).WF := by
  intro q hq
  simp only [GlobalState.afterAlloca] at hq ⊢
  have hne : (⟨s.alloc.nextFreeBlock⟩ : BlockId) ≠ q := by
    rintro rfl; change s.alloc.nextFreeBlock + 1 ≤ s.alloc.nextFreeBlock at hq; omega
  simpa [MemoryState.live?, MemoryState.getElem?_eq, Std.HashMap.getElem?_insert, hne]
    using hs q (by omega)

theorem fits_afterAlloca (s : GlobalState) (w : Nat) :
    Fits (s.afterAlloca w).mem ⟨⟨s.alloc.nextFreeBlock⟩, 0⟩ w :=
  ⟨{ length := (w + 7) / 8, bytes := 0#_ },
    by simp [GlobalState.afterAlloca, MemoryState.getElem?_eq],
    by simp [Pointer.offsetInBits, LiveBlock.lengthInBits]; omega⟩

/-! ## `alloca` and `store` against well-formedness

`WF` says every block at or above the counter is dead. Both writers preserve
it, and both leave the blocks below the counter as they found them -- the
frame facts every call-spanning proof rests on. -/

/-- A store leaves the blocks it does not address alone. -/
@[simp]
theorem live?_splice_ne {m : MemoryState} {p : Pointer} {w : Nat} {x : BitVec w}
    {q : BlockId} (h : p.id ≠ q) : (m.splice p x).live? q = m.live? q := by
  simp only [MemoryState.live?, getElem?_splice_ne h]

/-- A store through a pointer that addresses no live block does nothing. -/
theorem splicedDead {m : MemoryState} {p : Pointer} {w : Nat} {x : BitVec w}
    (h : m.live? p.id = none) : (m.splice p x).live? p.id = none := by
  unfold MemoryState.splice
  cases hb : m[p.id]? with
  | none => exact h
  | some blk =>
    cases blk with
    | dead => exact h
    | live b => simp [MemoryState.live?, hb] at h

theorem live?_splice_eq_none {m : MemoryState} {p : Pointer} {w : Nat} {x : BitVec w}
    {q : BlockId} (h : m.live? q = none) : (m.splice p x).live? q = none := by
  by_cases hq : p.id = q
  · subst hq; exact splicedDead h
  · rw [live?_splice_ne hq]; exact h

/-- A store keeps the blocks above the counter dead. -/
theorem _root_.LeanMLIR.GlobalState.WF.splice {s : GlobalState} {p : Pointer} {w : Nat}
    {x : BitVec w} (hs : s.WF) : ({ s with mem := s.mem.splice p x } : GlobalState).WF :=
  fun q hq => live?_splice_eq_none (hs q hq)

/-- An `alloca` leaves the blocks below the counter alone. -/
theorem live?_afterAlloca_of_lt {s : GlobalState} {w : Nat} {b : BlockId}
    (h : b.id < s.alloc.nextFreeBlock) : (s.afterAlloca w).mem.live? b = s.mem.live? b := by
  have hne : (⟨s.alloc.nextFreeBlock⟩ : BlockId) ≠ b := by
    rintro rfl; change s.alloc.nextFreeBlock < s.alloc.nextFreeBlock at h; omega
  simp [GlobalState.afterAlloca, MemoryState.live?, MemoryState.getElem?_eq,
    Std.HashMap.getElem?_insert, hne]

/-- The block an `alloca w` hands back: `(w + 7) / 8` zero bytes at the fresh
id. `fits_afterAlloca` gives its size; this gives its contents, which a proof
that reads the slot before storing to it needs. -/
theorem live?_afterAlloca_self (s : GlobalState) (w : Nat) :
    (s.afterAlloca w).mem.live? ⟨s.alloc.nextFreeBlock⟩
      = some { length := (w + 7) / 8, bytes := 0#_ } := by
  simp [GlobalState.afterAlloca, MemoryState.live?, MemoryState.getElem?_eq]

/-- The pointer and the state an `alloca w` produces, packaged for `obtain`,
with the facts a frame-carrying proof consumes: the fresh block's `Fits`, id
and offset, the advanced counter, well-formedness, and the one-block `live?`
frame. The two defining equations come first, ordered as the binders are, and
are what `peel_alloca` consumes. -/
theorem _root_.LeanMLIR.GlobalState.exists_afterAlloca_facts (s : GlobalState) (hs : s.WF)
    (w : Nat) :
    ∃ (t : Pointer) (s' : GlobalState),
      t = ⟨⟨s.alloc.nextFreeBlock⟩, 0⟩
      ∧ s' = s.afterAlloca w
      ∧ s'.WF
      ∧ Fits s'.mem t w
      ∧ t.id.id = s.alloc.nextFreeBlock
      ∧ t.offset = 0
      ∧ s'.alloc.nextFreeBlock = s.alloc.nextFreeBlock + 1
      ∧ ∀ b : BlockId, b ≠ t.id → s'.mem.live? b = s.mem.live? b :=
  ⟨⟨⟨s.alloc.nextFreeBlock⟩, 0⟩, s.afterAlloca w, rfl, rfl, hs.afterAlloca w,
    fits_afterAlloca s w, rfl, rfl, rfl,
    fun b hb => by
      have hne : (⟨s.alloc.nextFreeBlock⟩ : BlockId) ≠ b := fun h => hb h.symm
      simp [GlobalState.afterAlloca, MemoryState.live?, MemoryState.getElem?_eq,
        Std.HashMap.getElem?_insert, hne]⟩

/-- Popping a frame that allocated nothing is invisible: everything the kill
could touch is dead already. -/
theorem _root_.LeanMLIR.GlobalState.WF.popFrame_equiv {s : GlobalState} (hs : s.WF) :
    s ≈ s.popFrame s.mem := by
  refine ⟨rfl, rfl, fun q => ?_⟩
  show s.mem.live? q = (s.mem.killFrom s.alloc.nextFreeBlock).live? q
  by_cases hq : q.id < s.alloc.nextFreeBlock
  · exact (live?_killFrom_of_lt hq).symm
  · rw [live?_killFrom_of_le (not_lt.mp hq)]; exact hs q (not_lt.mp hq)

/-- The state a function returns to (`run_runFunction`) is equivalent to the one
it was entered in, provided its body left the blocks below the entry counter
live-for-live as it found them. -/
theorem GlobalState.killFrom_equiv {s : GlobalState} (m : MemoryState) (hs : s.WF)
    (hframe : ∀ q : BlockId, q.id < s.alloc.nextFreeBlock → m.live? q = s.mem.live? q) :
    s.popFrame m ≈ s := by
  refine ⟨rfl, rfl, fun q => ?_⟩
  by_cases hq : q.id < s.alloc.nextFreeBlock
  · exact (live?_killFrom_of_lt hq).trans (hframe q hq)
  · exact (live?_killFrom_of_le (not_lt.mp hq)).trans (hs q (not_lt.mp hq)).symm

/-! ## `store` -/

theorem run_store {t : LLVM.Ty} {x : TyDenote.toType t} {b : BitVec (LLVM.Ty.width t)}
    {m : MemoryState} {p : Pointer}
    (hx : LLVM.Ty.flatten t x = .value b) (hfit : Fits m p (LLVM.Ty.width t)) :
    (store (.value p) t x).run m = .value ((), m.splice p b) := by
  obtain ⟨block, hblk, hlen⟩ := hfit
  simp [store, getLiveBlockOrUB, hblk, hx, throwUBIf, Nat.not_lt.mpr hlen,
    MemoryState.splice, PoisonOr.getOrUB]

/-! ## `memset` -/

/-- A memset of `len` bytes at a pointer with room for them splices `len`
copies of the fill byte in. The `store` lemma's shape, with the written width
depending on the (run-time) length. -/
theorem run_memset {m : MemoryState} {p : Pointer} {b : BitVec 8} {len : BitVec 64}
    (hfit : Fits m p (8 * len.toNat)) :
    (memset (.value p) (.value b) (.value len)).run m
      = .value ((), m.splice p (BitVec.replicate len.toNat b)) := by
  obtain ⟨block, hblk, hlen⟩ := hfit
  simp [memset, getLiveBlockOrUB, hblk, throwUBIf, Nat.not_lt.mpr hlen,
    MemoryState.splice, PoisonOr.getOrUB]

/-! ## `load` -/

theorem run_load {t : LLVM.Ty} {m : MemoryState} {p : Pointer} {block : LiveBlock}
    (hblk : m[p.id]? = some (.live block))
    (hlen : p.offsetInBits + LLVM.Ty.width t ≤ block.lengthInBits) :
    (load (.value p) t).run m
      = .value (LLVM.Ty.unflatten t
          (block.bytes.extractLsb' p.offsetInBits (LLVM.Ty.width t)), m) := by
  simp [load, getLiveBlockOrUB, hblk, throwUBIf, Nat.not_lt.mpr hlen, PoisonOr.getOrUB]

/-- **Readback.** A load at `p` sees the value stored there, in *any* state
whose block at `p.id` is the spliced one -- in particular after any number of
intervening stores to other blocks. -/
theorem run_load_of_splice {t : LLVM.Ty} {x : TyDenote.toType t}
    {b : BitVec (LLVM.Ty.width t)} {m' : MemoryState} {p : Pointer} {block : LiveBlock}
    (hx : LLVM.Ty.flatten t x = .value b)
    (hlen : p.offsetInBits + LLVM.Ty.width t ≤ block.lengthInBits)
    (hm' : m'[p.id]?
      = some (.live { block with bytes := spliceBits block.bytes p.offsetInBits b })) :
    (load (.value p) t).run m' = .value (x, m') := by
  rw [run_load hm' hlen,
    show (({ block with bytes := spliceBits block.bytes p.offsetInBits b } : LiveBlock).bytes)
      = spliceBits block.bytes p.offsetInBits b from rfl,
    extractLsb'_spliceBits _ _ _ hlen, LLVM.Ty.unflatten_flatten t x b hx]

/-- **Load after store, same pointer**: what was written reads back. -/
theorem run_load_splice_self {t : LLVM.Ty} {x : TyDenote.toType t}
    {b : BitVec (LLVM.Ty.width t)} {m : MemoryState} {p : Pointer}
    (hx : LLVM.Ty.flatten t x = .value b) (hfit : Fits m p (LLVM.Ty.width t)) :
    (load (.value p) t).run (m.splice p b) = .value (x, m.splice p b) := by
  obtain ⟨block, hblk, hlen⟩ := hfit
  exact run_load_of_splice hx hlen (getElem?_splice_self hblk)

/-- **Load after store, different block**: an unrelated store is invisible. -/
theorem run_load_splice_ne {t : LLVM.Ty} {m : MemoryState} {p q : Pointer} {w : Nat}
    {x : BitVec w} {block : LiveBlock} (h : q.id ≠ p.id)
    (hblk : m[p.id]? = some (.live block))
    (hlen : p.offsetInBits + LLVM.Ty.width t ≤ block.lengthInBits) :
    (load (.value p) t).run (m.splice q x)
      = .value (LLVM.Ty.unflatten t
          (block.bytes.extractLsb' p.offsetInBits (LLVM.Ty.width t)), m.splice q x) :=
  run_load (by rw [getElem?_splice_ne h, hblk]) hlen

/-! ## Lifting into `EffectM` -/

/-- The `MemorySSAM → EffectM` lift, in success form. -/
theorem run_liftM {α : Type} {x : MemorySSAM α} {s : GlobalState} {y : α} {m : MemoryState}
    (h : x.run s.mem = .value (y, m)) :
    (liftM x : EffectM α).run s = .value (y, { s with mem := m }) := by
  cases s
  simp only [liftM, monadLift, MonadLift.monadLift, StateT.run] at *
  rw [h]

end SLLVM
end LeanMLIR
