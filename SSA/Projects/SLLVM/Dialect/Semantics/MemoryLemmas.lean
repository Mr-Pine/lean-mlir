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
    {b : BitVec (LLVM.Ty.width t)} {m m' : MemoryState} {p : Pointer} {block : LiveBlock}
    (hx : LLVM.Ty.flatten t x = .value b)
    (hblk : m[p.id]? = some (.live block))
    (hlen : p.offsetInBits + LLVM.Ty.width t ≤ block.lengthInBits)
    (hm' : m'[p.id]?
      = some (.live { block with bytes := spliceBits block.bytes p.offsetInBits b })) :
    (load (.value p) t).run m' = .value (x, m') := by
  clear hblk
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
  exact run_load_of_splice hx hblk hlen (getElem?_splice_self hblk)

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
