import SSA.Projects.SLLVM.Dialect
import SSA.Projects.Firedancer.MLIR.DenoteStep

namespace Firedancer
open LeanMLIR SLLVM
open InstCombine (LLVM)

lemma splicedLive (m: MemoryState) (p: Pointer) (b : LiveBlock) (hb: m.live? p.id = .some b) {w : Nat} (d: BitVec w) : (m.splice p d).live? p.id = .some { length := b.length, bytes := spliceBits b.bytes p.offsetInBits d } := by
  rw [MemoryState.splice]

  simp [MemoryState.live?] at hb
  replace hb : m[p.id]? = some (Block.live b) := by split at hb <;> simp_all
  simp [hb, MemoryState.live?, MemoryState.getElem?_eq]

/-- A store leaves the blocks it does not address alone. -/
@[simp]
theorem live?_splice_ne {m : MemoryState} {p : Pointer} {w : Nat} {x : BitVec w}
    {q : BlockId} (h : p.id ≠ q) : (m.splice p x).live? q = m.live? q := by
  simp only [MemoryState.live?, getElem?_splice_ne h]

/-- The `getElem?` form of a live block. -/
theorem getElem?_of_live? {m : MemoryState} {q : BlockId} {b : LiveBlock}
    (h : m.live? q = some b) : m[q]? = some (.live b) := by
  unfold MemoryState.live? at h
  split at h <;> simp_all

/-- A store leaves the blocks below the one it addresses alone. -/
theorem live?_splice_of_lt {m : MemoryState} {p : Pointer} {w : Nat} {x : BitVec w}
    {b : BlockId} (h : b.id < p.id.id) : (m.splice p x).live? b = m.live? b :=
  live?_splice_ne (by rintro rfl; omega)

/-- An `alloca` leaves the blocks below the counter alone. -/
theorem live?_afterAlloca_of_lt {s : GlobalState} {w : Nat} {b : BlockId}
    (h : b.id < s.alloc.nextFreeBlock) : (s.afterAlloca w).mem.live? b = s.mem.live? b := by
  have hne : (⟨s.alloc.nextFreeBlock⟩ : BlockId) ≠ b := by
    rintro rfl; change s.alloc.nextFreeBlock < s.alloc.nextFreeBlock at h; omega
  simp [GlobalState.afterAlloca, MemoryState.live?, MemoryState.getElem?_eq,
    Std.HashMap.getElem?_insert, hne]

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

/-- Two stores at *adjacent* ranges through the same base pointer are one
store of the concatenation -- the `MemoryState` counterpart of
`spliceBits_append`. `ho` is the no-wraparound side condition: the gep'd
pointer really is `w` bits further in, not wrapped around. -/
theorem splice_splice_append_equiv {s : GlobalState} {p : Pointer} {o : BitVec 64}
    {w w' : Nat} (x : BitVec w) (y : BitVec w')
    (ho : (p.withOffset o).offsetInBits = p.offsetInBits + w) :
    ({ s with mem := (s.mem.splice p x).splice (p.withOffset o) y } : GlobalState)
      ≈ { s with mem := s.mem.splice p (y ++ x) } := by
  refine ⟨rfl, fun q => ?_⟩
  by_cases hq : p.id = q
  · subst hq
    -- `(p.withOffset o).id` is `p.id`, but only up to projection-of-constructor,
    -- which `rw`'s syntactic matching will not do for it.
    show ((s.mem.splice p x).splice (p.withOffset o) y).live? (p.withOffset o).id
      = (s.mem.splice p (y ++ x)).live? p.id
    cases hb : s.mem.live? p.id with
    | none =>
        rw [splicedDead (m := s.mem.splice p x) (p := p.withOffset o) (splicedDead hb),
          splicedDead hb]
    | some b =>
        rw [splicedLive _ (p.withOffset o) _ (splicedLive s.mem p b hb x) y,
          splicedLive s.mem p b hb (y ++ x), ho, spliceBits_append]
  · show ((s.mem.splice p x).splice (p.withOffset o) y).live? q
      = (s.mem.splice p (y ++ x)).live? q
    rw [live?_splice_ne (p := p.withOffset o) hq, live?_splice_ne (p := p) hq,
      live?_splice_ne (p := p) hq]

/-- Splicing the same bits at the same pointer preserves equivalence: the block
written is fixed by the (equal) live block there, and no other block moves. -/
theorem splice_equiv {s s' : GlobalState} {p : Pointer} {w : Nat} {x : BitVec w}
    (h : s ≈ s') :
    ({ s with mem := s.mem.splice p x } : GlobalState)
      ≈ { s' with mem := s'.mem.splice p x } := by
  refine ⟨h.1, fun q => ?_⟩
  by_cases hq : p.id = q
  · subst hq
    cases hb : s.mem.live? p.id with
    | none => rw [splicedDead hb, splicedDead ((h.2 p.id).symm.trans hb)]
    | some b => rw [splicedLive _ _ _ hb, splicedLive _ _ _ ((h.2 p.id).symm.trans hb)]
  · rw [live?_splice_ne hq, live?_splice_ne hq]; exact h.2 q

/-- A store neither resurrects a block nor kills one. -/
theorem live?_splice_eq_none {m : MemoryState} {p : Pointer} {w : Nat} {x : BitVec w}
    {q : BlockId} (h : m.live? q = none) : (m.splice p x).live? q = none := by
  by_cases hq : p.id = q
  · subst hq; exact splicedDead h
  · rw [live?_splice_ne hq]; exact h

/-- A store keeps the blocks above the counter dead. -/
theorem _root_.LeanMLIR.GlobalState.WF.splice {s : GlobalState} {p : Pointer} {w : Nat}
    {x : BitVec w} (hs : s.WF) : ({ s with mem := s.mem.splice p x } : GlobalState).WF :=
  fun q hq => live?_splice_eq_none (hs q hq)

/-- The frame kill at the end of a call that allocated nothing is invisible:
every block it could kill is dead already. -/
theorem killFrom_equiv_of_none {s : GlobalState} {m : MemoryState}
    (hnone : ∀ q : BlockId, s.alloc.nextFreeBlock ≤ q.id → m.live? q = none) :
    ({ s with mem := m.killFrom s.alloc.nextFreeBlock } : GlobalState)
      ≈ { s with mem := m } := by
  refine ⟨rfl, fun q => ?_⟩
  by_cases hq : q.id < s.alloc.nextFreeBlock
  · exact live?_killFrom_of_lt hq
  · rw [live?_killFrom_of_le (by omega), hnone q (by omega)]

/-- `Fits` is antitone in the size demanded. -/
theorem Fits.mono {m : MemoryState} {p : Pointer} {n n' : Nat} (h : Fits m p n)
    (hle : n' ≤ n) : Fits m p n' :=
  let ⟨blk, hblk, hlen⟩ := h; ⟨blk, hblk, by omega⟩

/-- Stepping `o` bytes into a block leaves the same block, with `o * 8` fewer
bits available. -/
theorem remainingFits (m: MemoryState) (p: Pointer) (hp: Fits m p n) (o: BitVec 64)
    (ho : o.toNat * 8 ≤ n) : Fits m (p.withOffset o) (n - (o.toNat * 8)) := by
  obtain ⟨blk, hblk, hlen⟩ := hp
  refine ⟨blk, hblk, ?_⟩
  have h1 : p.offset.toNat < 2 ^ 64 := p.offset.isLt
  have h2 : o.toNat < 2 ^ 64 := o.isLt
  simp only [Pointer.withOffset, Pointer.offsetInBits, LiveBlock.lengthInBits,
    BitVec.toNat_add] at hlen ⊢
  omega

/-- Two states that agree on the block `p` addresses fit the same object there:
`Fits` looks at nothing else. -/
theorem fits_of_live?_eq {m m' : MemoryState} {p : Pointer} {n : Nat}
    (h : m'.live? p.id = m.live? p.id) (hp : Fits m p n) : Fits m' p n := by
  obtain ⟨blk, hblk, hlen⟩ := hp
  exact ⟨blk, getElem?_of_live? (h.trans (by simp only [MemoryState.live?, hblk])), hlen⟩

/-- A live block predates the counter: `alloca` hands out ids only at or above
it, and `WF` says those are dead. -/
theorem lt_nextFreeBlock_of_live {s : GlobalState} (hs : s.WF) {q : BlockId} {b : LiveBlock}
    (h : s.mem.live? q = some b) : q.id < s.alloc.nextFreeBlock := by
  by_contra hcon
  rw [hs q (by omega)] at h
  exact Option.noConfusion h

/-- `lt_nextFreeBlock_of_live` in `Fits` form: anything the caller can address
predates the frame, so no frame kill or fresh `alloca` touches it. -/
theorem lt_nextFreeBlock_of_fits {s : GlobalState} (hs : s.WF) {p : Pointer} {n : Nat}
    (h : Fits s.mem p n) : p.id.id < s.alloc.nextFreeBlock := by
  obtain ⟨blk, hblk, -⟩ := h
  exact lt_nextFreeBlock_of_live hs (show s.mem.live? p.id = some blk by
    simp only [MemoryState.live?, hblk])

/-- The block an `alloca w` hands back: `w` bits at offset 0. -/
theorem fits_afterAlloca_self (s : GlobalState) (w : Nat) :
    Fits (s.afterAlloca w).mem ⟨⟨s.alloc.nextFreeBlock⟩, 0⟩ w := by
  refine ⟨{ length := (w + 7) / 8, bytes := 0#_ }, ?_, ?_⟩
  · simp [GlobalState.afterAlloca, MemoryState.getElem?_eq]
  · have h0 : (0 : BitVec 64).toNat = 0 := rfl
    simp only [Pointer.offsetInBits, LiveBlock.lengthInBits]
    omega

/-- An `alloca` leaves alone every block the caller could already address. -/
theorem live?_afterAlloca_of_fits {s : GlobalState} (hs : s.WF) (w : Nat) {p : Pointer}
    {n : Nat} (h : Fits s.mem p n) :
    (s.afterAlloca w).mem.live? p.id = s.mem.live? p.id :=
  live?_afterAlloca_of_lt (lt_nextFreeBlock_of_fits hs h)

end Firedancer
