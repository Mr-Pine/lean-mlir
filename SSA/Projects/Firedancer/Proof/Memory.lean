module

public import SSA.Projects.SLLVM.Dialect
public import SSA.Projects.Firedancer.MLIR.DenoteStep

@[expose] public section

namespace Firedancer

open LeanMLIR SLLVM
open InstCombine (LLVM)

lemma splicedLive (m : MemoryState) (p : Pointer) (b : LiveBlock) (hb : m.live? p.id = .some b)
    {w : Nat} (d : BitVec w) :
    (m.splice p d).live? p.id =
      .some { length := b.length, bytes := spliceBits b.bytes p.offsetInBits d } := by
  rw [MemoryState.splice]
  simp [MemoryState.live?] at hb
  replace hb : m[p.id]? = some (Block.live b) := by split at hb <;> simp_all
  simp [hb, MemoryState.live?, MemoryState.getElem?_eq]

/-- The `getElem?` form of a live block. -/
theorem getElem?_of_live? {m : MemoryState} {q : BlockId} {b : LiveBlock} (h : m.live? q = some b) :
    m[q]? = some (.live b) := by
  unfold MemoryState.live? at h
  split at h <;> simp_all

/-- A store leaves the blocks below the one it addresses alone. -/
theorem live?_splice_of_lt {m : MemoryState} {p : Pointer} {w : Nat} {x : BitVec w} {b : BlockId}
    (h : b.id < p.id.id) : (m.splice p x).live? b = m.live? b :=
  live?_splice_ne
    (by
      rintro rfl; omega)

/-- Two stores at *adjacent* ranges through the same base pointer are one
store of the concatenation -- the `MemoryState` counterpart of
`spliceBits_append`. `ho` is the no-wraparound side condition: the gep'd
pointer really is `w` bits further in, not wrapped around. -/
theorem splice_splice_append_equiv {s : GlobalState} {p : Pointer} {o : BitVec 64} {w w' : Nat}
    (x : BitVec w) (y : BitVec w') (ho : (p.withOffset o).offsetInBits = p.offsetInBits + w) :
    ({ s with mem := (s.mem.splice p x).splice (p.withOffset o) y } : GlobalState) ≈
      { s with mem := s.mem.splice p (y ++ x) } := by
  refine ⟨rfl, rfl, fun q => ?_⟩
  by_cases hq : p.id = q
  · subst hq
    -- `(p.withOffset o).id` is `p.id`, but only up to projection-of-constructor,
    -- which `rw`'s syntactic matching will not do for it.
    show
      ((s.mem.splice p x).splice (p.withOffset o) y).live? (p.withOffset o).id =
        (s.mem.splice p (y ++ x)).live? p.id
    cases hb : s.mem.live? p.id with
    | none =>
      rw [splicedDead (m := s.mem.splice p x) (p := p.withOffset o) (splicedDead hb),
        splicedDead hb]
    | some b =>
      rw [splicedLive _ (p.withOffset o) _ (splicedLive s.mem p b hb x) y,
        splicedLive s.mem p b hb (y ++ x), ho, spliceBits_append]
  · show ((s.mem.splice p x).splice (p.withOffset o) y).live? q = (s.mem.splice p (y ++ x)).live? q
    rw [live?_splice_ne (p := p.withOffset o) hq, live?_splice_ne (p := p) hq,
      live?_splice_ne (p := p) hq]

/-- Splicing the same bits at the same pointer preserves equivalence: the block
written is fixed by the (equal) live block there, and no other block moves. -/
theorem splice_equiv {s s' : GlobalState} {p : Pointer} {w : Nat} {x : BitVec w} (h : s ≈ s') :
    ({ s with mem := s.mem.splice p x } : GlobalState) ≈ { s' with mem := s'.mem.splice p x } := by
  refine ⟨h.1, h.globals, fun q => ?_⟩
  by_cases hq : p.id = q
  · subst hq
    cases hb : s.mem.live? p.id with
    | none => rw [splicedDead hb, splicedDead ((h.live p.id).symm.trans hb)]
    | some b => rw [splicedLive _ _ _ hb, splicedLive _ _ _ ((h.live p.id).symm.trans hb)]
  · rw [live?_splice_ne hq, live?_splice_ne hq]; exact h.live q

/-- The frame kill at the end of a call that allocated nothing is invisible:
every block it could kill is dead already. -/
theorem killFrom_equiv_of_none {s : GlobalState} {m : MemoryState}
    (hnone : ∀ q : BlockId, s.alloc.nextFreeBlock ≤ q.id → m.live? q = none) :
    ({ s with mem := m.killFrom s.alloc.nextFreeBlock } : GlobalState) ≈ { s with mem := m } := by
  refine ⟨rfl, rfl, fun q => ?_⟩
  by_cases hq : q.id < s.alloc.nextFreeBlock
  · exact live?_killFrom_of_lt hq
  · rw [live?_killFrom_of_le (by omega), hnone q (by omega)]

/-- `Fits` is antitone in the size demanded. -/
theorem Fits.mono {m : MemoryState} {p : Pointer} {n n' : Nat} (h : Fits m p n) (hle : n' ≤ n) :
    Fits m p n' :=
  let ⟨blk, hblk, hlen⟩ := h;
  ⟨blk, hblk, by omega⟩

/-- Stepping `o` bytes into a block leaves the same block, with `o * 8` fewer
bits available. -/
theorem remainingFits (m : MemoryState) (p : Pointer) (hp : Fits m p n) (o : BitVec 64)
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
  -- v4.34: `noConfusion` no longer picks a motive here
  simp at h

/-- `lt_nextFreeBlock_of_live` in `Fits` form: anything the caller can address
predates the frame, so no frame kill or fresh `alloca` touches it. -/
theorem lt_nextFreeBlock_of_fits {s : GlobalState} (hs : s.WF) {p : Pointer} {n : Nat}
    (h : Fits s.mem p n) : p.id.id < s.alloc.nextFreeBlock := by
  obtain ⟨blk, hblk, -⟩ := h
  exact
    lt_nextFreeBlock_of_live hs
      (show s.mem.live? p.id = some blk by simp only [MemoryState.live?, hblk])

/-- The block an `alloca w` hands back: `w` bits at offset 0. -/
theorem fits_afterAlloca_self (s : GlobalState) (w : Nat) :
    Fits (s.afterAlloca w).mem ⟨⟨s.alloc.nextFreeBlock⟩, 0⟩ w := by
  refine ⟨{ length := (w + 7) / 8, bytes := 0#_ }, ?_, ?_⟩
  · simp [GlobalState.afterAlloca, MemoryState.getElem?_eq]
  · have h0 : (0 : BitVec 64).toNat = 0 := rfl
    simp only [Pointer.offsetInBits, LiveBlock.lengthInBits]
    omega

/-- An `alloca` leaves alone every block the caller could already address. -/
theorem live?_afterAlloca_of_fits {s : GlobalState} (hs : s.WF) (w : Nat) {p : Pointer} {n : Nat}
    (h : Fits s.mem p n) : (s.afterAlloca w).mem.live? p.id = s.mem.live? p.id :=
  live?_afterAlloca_of_lt (lt_nextFreeBlock_of_fits hs h)

/-! ## Locals frames

A region that allocates locals -- `fd_f25519_t t1[1], t2[1], …` -- steps
through states whose only lasting difference from the entry state `s` sits in
blocks at or above `s`'s counter. `FrameBelow` names that invariant once, so a
proof carries a single fact through its `alloca`s, its callee equivalences,
and its stores to locals, instead of re-deriving a `live?` chain at every
step. It is stated to plug directly into `GlobalState.killFrom_equiv`, which
is how such a region's `popFrame` ending discharges. -/

/-! ### Scalar cells

A fiat out-parameter kernel writes a single machine word through a pointer:
`subborrowx` a 64-bit limb and an 8-bit borrow, `cmovznz` a 64-bit select.
`readWord?` is the read that matches, and the three lemmas below are what a
caller threading several such cells needs -- read back your own write, ignore
a write elsewhere, and transport across a state that agrees on the block.
`readLimb?`/`readBuf?` are the 5-limb and 32-byte instances of the same
pattern; this is the scalar one. -/

/-- The `w`-bit scalar at `p`, or `none` if the block is dead. -/
def readWord? (p : Pointer) (w : Nat) (m : MemoryState) : Option (BitVec w) := do
  let blk ← m.live? p.id
  return blk.bytes.extractLsb' p.offsetInBits w

theorem readWord?_isSome {m : MemoryState} {p : Pointer} {w : Nat} (h : Fits m p w) :
    (readWord? p w m).isSome := by
  obtain ⟨blk, hblk, -⟩ := h
  have hlive : m.live? p.id = some blk := by simp only [MemoryState.live?, hblk]
  simp [readWord?, hlive]

/-- The `w`-bit scalar at `p`, given that it fits: the total read the callers
state their facts over. -/
def readWord {p : Pointer} {w : Nat} {m : MemoryState} (h : Fits m p w) : BitVec w :=
  (readWord? p w m).get (readWord?_isSome h)

theorem readWord_eq_of {m : MemoryState} {p : Pointer} {w : Nat} {h : Fits m p w} {x : BitVec w}
    (hv : readWord? p w m = some x) : readWord h = x := by simp only [readWord, hv, Option.get_some]

/-- `readWord` back into the proof-free `readWord?` form. -/
theorem readWord?_eq_some {m : MemoryState} {p : Pointer} {w : Nat} (h : Fits m p w) {x : BitVec w}
    (hv : readWord h = x) : readWord? p w m = some x := by
  rw [← hv]; exact (Option.some_get _).symm

/-- A cell reads back what was just written to it. -/
theorem readWord?_splice_self {m : MemoryState} {p : Pointer} {w : Nat} (x : BitVec w)
    (hp : Fits m p w) : readWord? p w (m.splice p x) = some x := by
  obtain ⟨blk, hblk, hlen⟩ := hp
  have hlive : m.live? p.id = some blk := by simp only [MemoryState.live?, hblk]
  simp only [readWord?, splicedLive m p blk hlive x]
  exact congrArg some (extractLsb'_spliceBits blk.bytes p.offsetInBits x hlen)

/-- A write to another block leaves a cell alone. -/
theorem readWord?_splice_ne {m : MemoryState} {p q : Pointer} {w w' : Nat} {x : BitVec w'}
    (h : q.id ≠ p.id) : readWord? p w (m.splice q x) = readWord? p w m := by
  simp only [readWord?, live?_splice_ne h]

/-- Two states that agree on the block `p` addresses read the same cell. -/
theorem readWord?_of_live?_eq {m m' : MemoryState} {p : Pointer} {w : Nat}
    (h : m'.live? p.id = m.live? p.id) : readWord? p w m' = readWord? p w m := by
  simp only [readWord?, h]

/-! The three lemmas above in total form: the `Fits` witness travels with the
value, so a caller threading cells never re-derives it. -/

theorem readWord_splice_self {m : MemoryState} {p : Pointer} {w : Nat} (x : BitVec w)
    (hp : Fits m p w) : ∃ h : Fits (m.splice p x) p w, readWord h = x :=
  ⟨fits_splice hp, readWord_eq_of (readWord?_splice_self x hp)⟩

theorem readWord_splice_ne {m : MemoryState} {p q : Pointer} {w w' : Nat} {x : BitVec w'}
    (hq : q.id ≠ p.id) (hp : Fits m p w) :
    ∃ h : Fits (m.splice q x) p w, readWord h = readWord hp :=
  ⟨fits_splice hp, readWord_eq_of ((readWord?_splice_ne hq).trans (readWord?_eq_some hp rfl))⟩

/-- Transport a cell across a state that agrees on its block. -/
theorem readWord_of_live?_eq {m m' : MemoryState} {p : Pointer} {w : Nat}
    (hl : m'.live? p.id = m.live? p.id) (hp : Fits m p w) :
    ∃ h : Fits m' p w, readWord h = readWord hp :=
  ⟨fits_of_live?_eq hl hp,
    readWord_eq_of ((readWord?_of_live?_eq hl).trans (readWord?_eq_some hp rfl))⟩

/-! ### Alloca chains

A region that opens with several `alloca`s -- 3 for `pow22523`, 21 for
`to_bytes` -- wants the whole prologue as one object rather than a chain of
`obtain`s. `allocaChain` is that state, and the step equation is `rfl`, which
is what `peel_alloca` wants for its defining hypothesis. -/

/-- The state after `k` successive `alloca`s of widths `w 0, …, w (k-1)`. -/
def _root_.LeanMLIR.GlobalState.allocaChain (s : GlobalState) (w : Nat → Nat) : Nat → GlobalState
  | 0 => s
  | k + 1 => (s.allocaChain w k).afterAlloca (w k)

/-- The pointer the `k`-th `alloca` of the chain returns. -/
def _root_.LeanMLIR.GlobalState.chainPtr (s : GlobalState) (w : Nat → Nat) (k : Nat) : Pointer :=
  ⟨⟨(s.allocaChain w k).alloc.nextFreeBlock⟩, 0⟩

namespace GlobalState

variable {s : GlobalState} {w : Nat → Nat}

@[simp]
theorem nextFreeBlock_allocaChain :
    ∀ k, (s.allocaChain w k).alloc.nextFreeBlock = s.alloc.nextFreeBlock + k
  | 0 => rfl
  | k + 1 => by
    show (s.allocaChain w k).alloc.nextFreeBlock + 1 = _
    rw [nextFreeBlock_allocaChain k]; omega

/-- Consecutive ids from the entry counter: the whole separation story. -/
@[simp]
theorem chainPtr_id (k : Nat) : (s.chainPtr w k).id.id = s.alloc.nextFreeBlock + k := by
  simp only [GlobalState.chainPtr, nextFreeBlock_allocaChain]

@[simp]
theorem chainPtr_offset (k : Nat) : (s.chainPtr w k).offset = 0 :=
  rfl

theorem WF.allocaChain (hs : s.WF) : ∀ k, (s.allocaChain w k).WF
  | 0 => hs
  | k + 1 => (WF.allocaChain hs k).afterAlloca (w k)

/-- A later `alloca` leaves an earlier cell alone: its id is strictly smaller. -/
theorem live?_allocaChain_of_lt {j : Nat} :
    ∀ k,
      j < k →
        (s.allocaChain w k).mem.live? (s.chainPtr w j).id =
          (s.allocaChain w (j + 1)).mem.live? (s.chainPtr w j).id := by
  intro k hk
  induction k with
  | zero => omega
  | succ n ih =>
    rcases Nat.lt_or_ge j n with h | h
    · rw [show (s.allocaChain w (n + 1)) = (s.allocaChain w n).afterAlloca (w n) from rfl,
        live?_afterAlloca_of_lt
          (by
            simp only [chainPtr_id, nextFreeBlock_allocaChain]; omega)]
      exact ih h
    · have : j = n := by omega
      subst this; rfl

/-- Every cell of the chain still fits at the end of it. -/
theorem fits_chainPtr {j k : Nat} (hj : j < k) :
    Fits (s.allocaChain w k).mem (s.chainPtr w j) (w j) := by
  refine fits_of_live?_eq (live?_allocaChain_of_lt k hj) ?_
  show Fits ((s.allocaChain w j).afterAlloca (w j)).mem _ _
  exact fits_afterAlloca _ _

end GlobalState

/-- Every block below `n₀` reads in `s'` as it did in `s`. With
`n₀ = s.alloc.nextFreeBlock` this is the frame condition of a region entered
at `s`: everything the caller could address is untouched. -/
def FrameBelow (n₀ : Nat) (s s' : GlobalState) : Prop :=
  ∀ b : BlockId, b.id < n₀ → s'.mem.live? b = s.mem.live? b

namespace FrameBelow

variable {n₀ : Nat} {s s' s'' : GlobalState}

protected theorem refl (n₀ : Nat) (s : GlobalState) : FrameBelow n₀ s s := fun _ _ => rfl

protected theorem trans (h : FrameBelow n₀ s s') (h' : FrameBelow n₀ s' s'') :
    FrameBelow n₀ s s'' := fun b hb => (h' b hb).trans (h b hb)

/-- An `alloca` in a state whose counter is at or above `n₀` allocates outside
the frame. -/
theorem afterAlloca {w : Nat} (h : n₀ ≤ s'.alloc.nextFreeBlock) (hf : FrameBelow n₀ s s') :
    FrameBelow n₀ s (s'.afterAlloca w) := fun b hb =>
  (live?_afterAlloca_of_lt (by omega)).trans (hf b hb)

/-- A run of `n` successive `alloca`s allocates outside the frame. -/
theorem allocaChain {w : Nat → Nat} (h : n₀ ≤ s'.alloc.nextFreeBlock) (hf : FrameBelow n₀ s s') :
    ∀ k, FrameBelow n₀ s (s'.allocaChain w k)
  | 0 => hf
  | k + 1 =>
    FrameBelow.afterAlloca
      (by
        rw [GlobalState.nextFreeBlock_allocaChain]; omega)
      (FrameBelow.allocaChain h hf k)

/-- A store to a local -- a pointer whose block id is at or above `n₀` --
stays outside the frame. -/
theorem splice {t : Pointer} {w : Nat} {x : BitVec w} (ht : n₀ ≤ t.id.id)
    (hf : FrameBelow n₀ s s') : FrameBelow n₀ s { s' with mem := s'.mem.splice t x } := fun b hb =>
  (live?_splice_ne fun h => absurd (h ▸ hb) (by omega)).trans (hf b hb)

/-- A callee's result state is equivalent to a splice state; the frame
transports along the equivalence. -/
theorem of_equiv (he : s' ≈ s'') (hf : FrameBelow n₀ s s') : FrameBelow n₀ s s'' := fun b hb =>
  (he.live b).symm.trans (hf b hb)

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

/-- Writing a block's own bits back changes nothing. -/
theorem live?_splice_extract {m : MemoryState} {p : Pointer} {blk : LiveBlock} (w : Nat)
    (hl : m.live? p.id = some blk) (q : BlockId) :
    (m.splice p (blk.bytes.extractLsb' p.offsetInBits w)).live? q = m.live? q := by
  by_cases hq : p.id = q
  · subst hq
    rw [splicedLive m p blk hl, hl]
    cases blk with
    | mk len bytes =>
      congr 2
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      simp only [getLsbD_spliceBits, BitVec.getLsbD_extractLsb']
      split_ifs with h1
      · simp only [show i - p.offsetInBits < w by omega, decide_true, Bool.true_and]
        congr 1; omega
      · rfl
  · exact live?_splice_ne hq

/-- The `popFrame` ending of a region that wrote exactly one caller block `o`
(through an out-parameter) and otherwise kept its frame: the result is the
entry state with one splice. `hoval` says `m` holds at `o` what the splice
puts there -- typically via `live?_splice_congr` and the frame up to the final
write. -/
theorem popFrame_equiv_splice {s : GlobalState} {m : MemoryState} {o : Pointer} {w : Nat}
    {x : BitVec w} (hs : s.WF) (ho : o.id.id < s.alloc.nextFreeBlock)
    (hf : ∀ b : BlockId, b.id < s.alloc.nextFreeBlock → b ≠ o.id → m.live? b = s.mem.live? b)
    (hoval : m.live? o.id = (s.mem.splice o x).live? o.id) :
    ({ s with mem := s.mem.splice o x } : GlobalState) ≈ s.popFrame m := by
  refine ⟨rfl, rfl, fun b => ?_⟩
  show (s.mem.splice o x).live? b = (m.killFrom s.alloc.nextFreeBlock).live? b
  by_cases hb : b.id < s.alloc.nextFreeBlock
  · rw [live?_killFrom_of_lt hb]
    by_cases hbo : b = o.id
    · rw [hbo, ← hoval]
    · rw [hf b hb hbo, live?_splice_ne (fun h => hbo h.symm)]
  · rw [live?_killFrom_of_le (by omega),
      live?_splice_ne
        (fun h => by
          rw [← h] at hb; omega),
      hs b (by omega)]

/-- `popFrame_equiv_splice` for a region that wrote more than once: `written`
names the caller blocks it touched, `n` is any memory agreeing with `s.mem`
off them, and the caller supplies the readback at each. -/
theorem popFrame_equiv_written {s : GlobalState} {m n : MemoryState} (written : BlockId → Prop)
    [DecidablePred written] (hs : s.WF)
    (hbelow : ∀ b : BlockId, written b → b.id < s.alloc.nextFreeBlock)
    (hfm : ∀ b : BlockId, b.id < s.alloc.nextFreeBlock → ¬written b → m.live? b = s.mem.live? b)
    (hfn : ∀ b : BlockId, ¬written b → n.live? b = s.mem.live? b)
    (hval : ∀ b : BlockId, written b → m.live? b = n.live? b) :
    s.popFrame m ≈ ({ alloc := s.alloc, mem := n, globals := s.globals } : GlobalState) := by
  refine ⟨rfl, rfl, fun b => ?_⟩
  show (m.killFrom s.alloc.nextFreeBlock).live? b = n.live? b
  by_cases hw : written b
  · rw [live?_killFrom_of_lt (hbelow b hw), hval b hw]
  · by_cases hb : b.id < s.alloc.nextFreeBlock
    · rw [live?_killFrom_of_lt hb, hfm b hb hw, hfn b hw]
    · rw [live?_killFrom_of_le (by omega), hfn b hw, hs b (by omega)]

/-- ... and the single-block case: a region writing only its out-parameter,
`fd_ed25519_point_from`'s four coordinate stores included. -/
theorem popFrame_equiv_block {s : GlobalState} {m n : MemoryState} {o : BlockId} (hs : s.WF)
    (ho : o.id < s.alloc.nextFreeBlock)
    (hfm : ∀ b : BlockId, b.id < s.alloc.nextFreeBlock → b ≠ o → m.live? b = s.mem.live? b)
    (hfn : ∀ b : BlockId, b ≠ o → n.live? b = s.mem.live? b) (hoval : m.live? o = n.live? o) :
    s.popFrame m ≈ ({ alloc := s.alloc, mem := n, globals := s.globals } : GlobalState) :=
  popFrame_equiv_written (· = o) hs (fun _ h => h ▸ ho) hfm hfn (fun _ h => h ▸ hoval)

/-- One step of an `allocaChain`, with the index given as a literal so `rw`
can key on it: `allocaChain_step s w 0 1 rfl : s.allocaChain w 1 = …`. -/
theorem allocaChain_step (s : GlobalState) (w : Nat → Nat) (k j : Nat) (h : j = k + 1) :
    s.allocaChain w j = (s.allocaChain w k).afterAlloca (w k) := by
  subst h; rfl

/-- Supply the second witness of a two-variable existential up front: a spec's
`∃ s' ret` has to give `ret` before `run_runFunction'` can take the state. -/
lemma existsISecond {α β : Type} {f : α → β → Prop} (v : β) (h : ∃ x, f x v) : ∃ x y, f x y := by
  obtain ⟨u, hu⟩ := h
  refine ⟨u, v, hu⟩

/-- Strip the `runFunction` wrapper while keeping the existential in place, so
the final state is supplied at the end from a name the walk introduced rather
than a metavariable that predates it. A copy of `fiat_25519_selectznz`'s; they
move together. -/
theorem run_runFunction' {α : Type} {body : EffectM α} {rets : α} {s : GlobalState}
    (P : GlobalState → Prop)
    (h : ∃ s' : GlobalState, StateT.run body s = .value (rets, s') ∧ P (s.popFrame s'.mem)) :
    ∃ s' : GlobalState, StateT.run (runFunction body) s = .value (rets, s') ∧ P s' :=
  let ⟨t, hrun, hP⟩ := h
  ⟨s.popFrame t.mem, run_runFunction hrun, hP⟩

end Firedancer
