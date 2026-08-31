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

/-- The `getElem?` form of a live block. -/
theorem getElem?_of_live? {m : MemoryState} {q : BlockId} {b : LiveBlock}
    (h : m.live? q = some b) : m[q]? = some (.live b) := by
  unfold MemoryState.live? at h
  split at h <;> simp_all

/-- A store leaves the blocks below the one it addresses alone. -/
theorem live?_splice_of_lt {m : MemoryState} {p : Pointer} {w : Nat} {x : BitVec w}
    {b : BlockId} (h : b.id < p.id.id) : (m.splice p x).live? b = m.live? b :=
  live?_splice_ne (by rintro rfl; omega)

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

/-! ## Locals frames

A region that allocates locals -- `fd_f25519_t t1[1], t2[1], …` -- steps
through states whose only lasting difference from the entry state `s` sits in
blocks at or above `s`'s counter. `FrameBelow` names that invariant once, so a
proof carries a single fact through its `alloca`s, its callee equivalences,
and its stores to locals, instead of re-deriving a `live?` chain at every
step. It is stated to plug directly into `GlobalState.killFrom_equiv`, which
is how such a region's `popFrame` ending discharges. -/

/-- Every block below `n₀` reads in `s'` as it did in `s`. With
`n₀ = s.alloc.nextFreeBlock` this is the frame condition of a region entered
at `s`: everything the caller could address is untouched. -/
def FrameBelow (n₀ : Nat) (s s' : GlobalState) : Prop :=
  ∀ b : BlockId, b.id < n₀ → s'.mem.live? b = s.mem.live? b

namespace FrameBelow

variable {n₀ : Nat} {s s' s'' : GlobalState}

protected theorem refl (n₀ : Nat) (s : GlobalState) : FrameBelow n₀ s s := fun _ _ => rfl

protected theorem trans (h : FrameBelow n₀ s s') (h' : FrameBelow n₀ s' s'') :
    FrameBelow n₀ s s'' :=
  fun b hb => (h' b hb).trans (h b hb)

/-- An `alloca` in a state whose counter is at or above `n₀` allocates outside
the frame. -/
theorem afterAlloca {w : Nat} (h : n₀ ≤ s'.alloc.nextFreeBlock) (hf : FrameBelow n₀ s s') :
    FrameBelow n₀ s (s'.afterAlloca w) :=
  fun b hb => (live?_afterAlloca_of_lt (by omega)).trans (hf b hb)

/-- A store to a local -- a pointer whose block id is at or above `n₀` --
stays outside the frame. -/
theorem splice {t : Pointer} {w : Nat} {x : BitVec w} (ht : n₀ ≤ t.id.id)
    (hf : FrameBelow n₀ s s') :
    FrameBelow n₀ s { s' with mem := s'.mem.splice t x } :=
  fun b hb => (live?_splice_ne fun h => absurd (h ▸ hb) (by omega)).trans (hf b hb)

/-- A callee's result state is equivalent to a splice state; the frame
transports along the equivalence. -/
theorem of_equiv (he : s' ≈ s'') (hf : FrameBelow n₀ s s') : FrameBelow n₀ s s'' :=
  fun b hb => (he.2 b).symm.trans (hf b hb)

/-- The `popFrame` ending: a region entered at `s` whose final state kept the
frame restores `s` up to equivalence. -/
theorem popFrame_equiv (hs : s.WF) (hf : FrameBelow s.alloc.nextFreeBlock s s') :
    s.popFrame s'.mem ≈ s :=
  GlobalState.killFrom_equiv s'.mem hs hf

end FrameBelow

/-- Equal blocks splice to equal blocks: `splice` looks only at the block the
pointer addresses. -/
theorem live?_splice_congr {m₁ m₂ : MemoryState} {p : Pointer} {w : Nat} {x : BitVec w}
    (h : m₁.live? p.id = m₂.live? p.id) :
    (m₁.splice p x).live? p.id = (m₂.splice p x).live? p.id := by
  cases hb : m₂.live? p.id with
  | none => rw [splicedDead (h.trans hb), splicedDead hb]
  | some blk => rw [splicedLive _ _ _ (h.trans hb), splicedLive _ _ _ hb]

/-- The `popFrame` ending of a region that wrote exactly one caller block `o`
(through an out-parameter) and otherwise kept its frame: the result is the
entry state with one splice. `hoval` says `m` holds at `o` what the splice
puts there -- typically via `live?_splice_congr` and the frame up to the final
write. -/
theorem popFrame_equiv_splice {s : GlobalState} {m : MemoryState} {o : Pointer} {w : Nat}
    {x : BitVec w} (hs : s.WF) (ho : o.id.id < s.alloc.nextFreeBlock)
    (hf : ∀ b : BlockId, b.id < s.alloc.nextFreeBlock → b ≠ o.id →
      m.live? b = s.mem.live? b)
    (hoval : m.live? o.id = (s.mem.splice o x).live? o.id) :
    ({ s with mem := s.mem.splice o x } : GlobalState) ≈ s.popFrame m := by
  refine ⟨rfl, fun b => ?_⟩
  show (s.mem.splice o x).live? b = (m.killFrom s.alloc.nextFreeBlock).live? b
  by_cases hb : b.id < s.alloc.nextFreeBlock
  · rw [live?_killFrom_of_lt hb]
    by_cases hbo : b = o.id
    · rw [hbo, ← hoval]
    · rw [hf b hb hbo, live?_splice_ne (fun h => hbo h.symm)]
  · rw [live?_killFrom_of_le (by omega),
      live?_splice_ne (fun h => by rw [← h] at hb; omega), hs b (by omega)]

end Firedancer
