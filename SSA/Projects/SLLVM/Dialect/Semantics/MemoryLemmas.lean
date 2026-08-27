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

/-- Two states no program can tell apart: the same counter and the same live
blocks. This is what a function that "does not touch the stack" preserves --
its frame is dead on return, not absent. -/
def _root_.LeanMLIR.GlobalState.Equiv (s s' : GlobalState) : Prop :=
  s.alloc = s'.alloc ∧ ∀ q, s.mem.live? q = s'.mem.live? q

instance : HasEquiv GlobalState := ⟨GlobalState.Equiv⟩

theorem GlobalState.equiv_def {s s' : GlobalState} :
    s ≈ s' ↔ s.alloc = s'.alloc ∧ ∀ q, s.mem.live? q = s'.mem.live? q := Iff.rfl

@[refl] theorem GlobalState.Equiv.refl (s : GlobalState) : s ≈ s := ⟨rfl, fun _ => rfl⟩

@[symm] theorem GlobalState.Equiv.symm {s s' : GlobalState} (h : s ≈ s') : s' ≈ s :=
  ⟨h.1.symm, fun q => (h.2 q).symm⟩

@[trans] theorem GlobalState.Equiv.trans {s s' s'' : GlobalState} (h : s ≈ s') (h' : s' ≈ s'') :
    s ≈ s'' :=
  ⟨h.1.trans h'.1, fun q => (h.2 q).trans (h'.2 q)⟩

/-- `s` is *well-formed* when no block at or above its counter is live, the
invariant `alloca` and `killFrom` keep. -/
def _root_.LeanMLIR.GlobalState.WF (s : GlobalState) : Prop :=
  ∀ q : BlockId, s.alloc.nextFreeBlock ≤ q.id → s.mem.live? q = none

/-- `WF` speaks only of the counter and of `live?`, and `≈` equates both, so it
transports along an equivalence. -/
theorem _root_.LeanMLIR.GlobalState.WF.of_equiv {s s' : GlobalState}
    (hs : s.WF) (h : s ≈ s') : s'.WF := by
  intro q hq
  rw [← h.2 q]
  exact hs q (by rw [h.1]; exact hq)

/-- The state a function returns to (`run_runFunction`) is equivalent to the one
it was entered in, provided its body left the blocks below the entry counter
live-for-live as it found them. -/
theorem GlobalState.killFrom_equiv {s : GlobalState} (m : MemoryState) (hs : s.WF)
    (hframe : ∀ q : BlockId, q.id < s.alloc.nextFreeBlock → m.live? q = s.mem.live? q) :
    s.popFrame m ≈ s := by
  refine ⟨rfl, fun q => ?_⟩
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
