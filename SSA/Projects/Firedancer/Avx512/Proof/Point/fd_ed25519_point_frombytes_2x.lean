/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.Firedancer.Avx512.Spec.Point.fd_ed25519_point_frombytes_2x
import SSA.Projects.Firedancer.Avx512.Proof.Point.fd_r43x6_ge_decode2
import SSA.Projects.Firedancer.Avx512.Proof.Step.Basic

/-!
# `fd_ed25519_point_frombytes_2x` conforms to its spec

Six `alloca`s, one call, six load/store pairs. Nothing arithmetic happens
here: every claim about the decoded points is `fd_r43x6_ge_decode2_conforms`,
and what is proved is the copy -- that slot `k` reaches the field it belongs
to, and that the frame goes away again.

The six slots live at or above the entry counter and `r₁`, `r₂` below it, so
no store can hit a slot and no slot survives the `popFrame`. That one fact,
`slot_ne`, is what carries the loads across the stores they are interleaved
with.

## What the callee's `≈` costs, and why nothing here uses it backwards

`fd_r43x6_ge_decode2_conforms` hands back `w ≈ { sAlloc with mem := m }`,
where `m` is six `splice`s deep. Two shapes read that, and only one of them
elaborates.

Backwards -- any lemma whose `p`/`x` are pinned by its *conclusion* alone,
chained and then handed to an `of_equiv` -- does not. Each level hands the
unifier `?s'.alloc =?= sAlloc.alloc` together with `?s'.mem =?= <the splices
below it>`: projections of a record literal against a metavariable,
re-traversing the whole six-splice term, six times over. It type-checks and it
never finishes.

Three shapes in this file were written that way and all three hung:
`FrameBelow.of_equiv` over six `FrameBelow.splice`s, `GlobalState.WF.of_equiv`
over six `GlobalState.WF.splice`s, and `rw [hn₂', hn₁']` on the copy's state
equations. `readVec?_splice_self` is the same trap seen from the other side:
handed `hslot k`, it pins the base memory to `sAlloc.mem` and its pattern then
matches nothing, because slot `k`'s splice sits on top of slots `0 … k-1`.

Forwards -- `intro b hb`, then one `live?_splice_ne` per splice -- does, and
every readback below is written that way. `live?_of_equiv_mem'` is the other
half of it: `heqw.live q` states its right-hand side as
`({ sAlloc with mem := m }).mem`, a projection no `rw` can see `m`'s splices
through, so it is restated at `m` once and used everywhere.
-/

namespace Firedancer.Avx512
open LeanMLIR SLLVM
open InstCombine (LLVM)
open Ed25519

/- Scaffolding for the `fd_ed25519_point_frombytes_2x` derivation. Only
`fd_ed25519_point_frombytes_2x_conforms`, below, escapes. -/
namespace FromBytes2x

/-! ### The frame

Six `wwl_t` locals, all one width -- `FD_R43X6_GE_DECODE2` decodes into three
per point and then packs them into the caller's QUADs. -/

/-- The six locals' width, in allocation order: a `wwl_t` each. -/
def cw : Nat → Nat := fun _ => 512

/-- The locals as pointers: consecutive blocks from the entry counter. Slots
`0`-`2` are `%1`-`%3`, the first point's three vectors; `3`-`5` are `%4`-`%6`,
the second's. -/
def slotPtr (s : GlobalState) (k : Nat) : Pointer := s.chainPtr cw k

/-- Fold a pointer the `alloca` prologue leaves expanded back to
`slotPtr s k`. -/
@[simp] theorem slotPtr_0 (s : GlobalState) :
    (⟨⟨(s.allocaChain cw 0).alloc.nextFreeBlock⟩, 0⟩ : Pointer) = slotPtr s 0 := rfl
@[simp] theorem slotPtr_1 (s : GlobalState) :
    (⟨⟨(s.allocaChain cw 1).alloc.nextFreeBlock⟩, 0⟩ : Pointer) = slotPtr s 1 := rfl
@[simp] theorem slotPtr_2 (s : GlobalState) :
    (⟨⟨(s.allocaChain cw 2).alloc.nextFreeBlock⟩, 0⟩ : Pointer) = slotPtr s 2 := rfl
@[simp] theorem slotPtr_3 (s : GlobalState) :
    (⟨⟨(s.allocaChain cw 3).alloc.nextFreeBlock⟩, 0⟩ : Pointer) = slotPtr s 3 := rfl
@[simp] theorem slotPtr_4 (s : GlobalState) :
    (⟨⟨(s.allocaChain cw 4).alloc.nextFreeBlock⟩, 0⟩ : Pointer) = slotPtr s 4 := rfl
@[simp] theorem slotPtr_5 (s : GlobalState) :
    (⟨⟨(s.allocaChain cw 5).alloc.nextFreeBlock⟩, 0⟩ : Pointer) = slotPtr s 5 := rfl

/-- What holds of a state part-way through the region. -/
structure Frame (t : Nat → Pointer) (n₀ : Nat) (s₀ u : GlobalState) : Prop where
  wf : u.WF
  fits : ∀ k, k < 6 → Fits u.mem (t k) 512
  fb : FrameBelow n₀ s₀ u

/-- The prologue's facts, with the state it reaches handed out opaquely --
`hsAlloc` is the only place `allocaChain` is written, which keeps every later
`isDefEq` off the six-step chain. -/
theorem exists_slots_frame (s : GlobalState) (hs : s.WF) :
    ∃ sAlloc : GlobalState, sAlloc = s.allocaChain cw 6
      ∧ GeDecode2.Slots (slotPtr s) s.alloc.nextFreeBlock
      ∧ Frame (slotPtr s) s.alloc.nextFreeBlock s sAlloc :=
  ⟨_, rfl,
   { id := fun k => GlobalState.chainPtr_id k
     off := fun k => GlobalState.chainPtr_offset k },
   { wf := GlobalState.WF.allocaChain hs 6
     fits := fun _ hk => GlobalState.fits_chainPtr hk
     fb := FrameBelow.allocaChain (le_refl _) (FrameBelow.refl _ _) 6 }⟩

/-- A caller's pointer and a frame slot are different blocks: the slots start
at the entry counter and everything the caller can address predates it. -/
theorem slot_ne {t : Nat → Pointer} {n₀ k : Nat} (slots : GeDecode2.Slots t n₀)
    {q : Pointer} (hq : q.id.id < n₀) : q.id ≠ (t k).id := fun he => by
  have hid := slots.id k
  rw [← he] at hid
  omega

/-- A `wwl_t` slot reads the same across a store to a caller block. This is
what carries the six loads through the six stores they are interleaved
with. -/
theorem readVec?_thru {t : Nat → Pointer} {n₀ k : Nat} (slots : GeDecode2.Slots t n₀)
    {m : MemoryState} {q : Pointer} (hq : q.id.id < n₀) {w : Nat} {x : BitVec w}
    {v : Vector (BitVec 64) 8} (h : readVec? (t k) m = some v) :
    readVec? (t k) (m.splice q x) = some v :=
  (readVec?_splice_ne (slot_ne slots hq)).trans h

/-! ### Carrying a fact across a store, by the store's *memory* equation

`name_of` hands each store's state out as `n₂` with `hn₂' : n₂ = { n₁ with
mem := … }`, and there are two wrong ways to spend that.

`rw [hn₂', hn₁']` on the goal is one: one rewrite leaves `({ n₁ with mem :=
… }).mem` behind, two leave it nested, and the `exact` after is reconciling
projections of record literals against a metavariable memory.

A lemma taking `hu : u' = { u with mem := u.mem.splice q x }` is the other,
and it is the *same* trap one level further in -- matching that pattern
against a concrete state equation asks the unifier for `?u.alloc =?= n₁.alloc`
before anything else is known. `hs1` survived it and `hs2` did not.

So these three take `hm : m' = m.splice q x`, between memories, where every
implicit is first-order. The state equations reach them through
`hm₁ … hm₆` below, each proved by `rw [hnₖ']` -- a rewrite of a *variable*,
which matches trivially, and the one place the record update is unfolded. -/

/-- A slot still reads the same after a store to a caller block. -/
theorem readVec?_thru' {t : Nat → Pointer} {n₀ k : Nat} (slots : GeDecode2.Slots t n₀)
    {m m' : MemoryState} {q : Pointer} {wd : Nat} {x : BitVec wd}
    (hm : m' = m.splice q x) (hq : q.id.id < n₀)
    {v : Vector (BitVec 64) 8} (h : readVec? (t k) m = some v) :
    readVec? (t k) m' = some v := by
  subst hm; exact readVec?_thru slots hq h

/-- ... and still fits. -/
theorem fits_thru {m m' : MemoryState} {q p : Pointer} {wd n : Nat} {x : BitVec wd}
    (hm : m' = m.splice q x) (h : Fits m p n) : Fits m' p n := by
  subst hm; exact fits_splice h

/-- ... `IsVecPtr` and all. -/
theorem isVecPtr_thru {m m' : MemoryState} {q p : Pointer} {wd : Nat} {x : BitVec wd}
    (hm : m' = m.splice q x) (h : IsVecPtr m p) : IsVecPtr m' p := by
  subst hm; exact ⟨fits_splice h.1, h.2⟩

/-- A `vector<4xi64>` slot reads the same in two states that agree on its
block: `readWv`'s counterpart of `readVec?_of_live?_eq`, with the witness
carried rather than existentially quantified. -/
theorem readWv_of_live?_eq {m m' : MemoryState} {p : Pointer}
    (hl : m'.live? p.id = m.live? p.id) (h : IsWvPtr m p) (h' : IsWvPtr m' p) :
    readWv h' = readWv h := by
  simp only [readWv, readWv?, hl]

/-- The memory side of a callee's `u ≈ { s with mem := m }`, stated at `m`
rather than at the record update.

`heqw.live q` proves the same thing, but with `({ s with mem := m }).mem` as
its right-hand side -- a projection of a record literal, which no `rw` can see
`m`'s splices through. Restating it once here is what keeps every readback
below a first-order rewrite. -/
theorem live?_of_equiv_mem' {u s : GlobalState} {m : MemoryState}
    (he : u ≈ ({ s with mem := m } : GlobalState)) (q : BlockId) :
    u.mem.live? q = m.live? q := he.live q

/-- ... and the counter side of the same equivalence, for the same reason. -/
theorem alloc_of_equiv_mem' {u s : GlobalState} {m : MemoryState}
    (he : u ≈ ({ s with mem := m } : GlobalState)) : u.alloc = s.alloc := he.alloc

/-- A store leaves a block it misses alone, and one it hits equal to whatever
the same store makes of an equal block: the `b`-indexed
`live?_splice_congr`. -/
theorem live?_splice_congr' {m₁ m₂ : MemoryState} {p : Pointer} {w : Nat} {x : BitVec w}
    {b : BlockId} (h : m₁.live? b = m₂.live? b) :
    (m₁.splice p x).live? b = (m₂.splice p x).live? b := by
  by_cases hb : b = p.id
  · subst hb; exact live?_splice_congr h
  · rw [live?_splice_ne (fun he => hb he.symm), live?_splice_ne (fun he => hb he.symm)]
    exact h

/-- Supply the last three witnesses of a four-variable existential up front:
the spec's `∃ s' ret q₁ q₂` has to give all three before `run_runFunction'`
can take the state. `existsISecond` at one more binder. -/
theorem existsLastThree {α β γ δ : Sort u} {f : α → β → γ → δ → Prop}
    (b : β) (c : γ) (d : δ) (h : ∃ a, f a b c d) : ∃ a b c d, f a b c d :=
  let ⟨a, ha⟩ := h; ⟨a, b, c, d, ha⟩

end FromBytes2x

open FromBytes2x in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
/-- The region is `FD_R43X6_GE_DECODE2` and nothing else, so its hypotheses
are the callee's: two QUADs to write and two encodings to read. No
disjointness is asked for -- the encodings are read before anything is
written, and if the two QUADs are the same object the second one's stores
simply win. -/
theorem fd_ed25519_point_frombytes_2x_conforms (r₁ buf₁ r₂ buf₂ : Pointer)
    (s : GlobalState) (hs : s.WF)
    (hr₁ : IsQuadPtr s.mem r₁) (hbuf₁ : IsWvPtr s.mem buf₁)
    (hr₂ : IsQuadPtr s.mem r₂) (hbuf₂ : IsWvPtr s.mem buf₂) :
    fd_ed25519_point_frombytes_2x_spec r₁ buf₁ r₂ buf₂ s hr₁ hbuf₁ hr₂ hbuf₂ := by
  obtain ⟨sAlloc, hsAlloc, slots, frame⟩ := exists_slots_frame s hs
  -- the caller's four objects predate the frame
  have hn₁ : r₁.id.id < s.alloc.nextFreeBlock := lt_nextFreeBlock_of_fits hs hr₁.1
  have hn₂ : r₂.id.id < s.alloc.nextFreeBlock := lt_nextFreeBlock_of_fits hs hr₂.1
  have hnb₁ : buf₁.id.id < s.alloc.nextFreeBlock := lt_nextFreeBlock_of_fits hs hbuf₁.1
  have hnb₂ : buf₂.id.id < s.alloc.nextFreeBlock := lt_nextFreeBlock_of_fits hs hbuf₂.1

  -- the six slots and the two encodings, at the state the call is made in
  have hslot : ∀ k, k < 6 → IsVecPtr sAlloc.mem (slotPtr s k) := fun k hk =>
    ⟨frame.fits k hk, by simp [slots.off k]⟩
  have hbuf₁' : IsWvPtr sAlloc.mem buf₁ :=
    ⟨fits_of_live?_eq (frame.fb buf₁.id hnb₁) hbuf₁.1, hbuf₁.2⟩
  have hbuf₂' : IsWvPtr sAlloc.mem buf₂ :=
    ⟨fits_of_live?_eq (frame.fb buf₂.id hnb₂) hbuf₂.1, hbuf₂.2⟩
  have hread₁ : readWv hbuf₁' = readWv hbuf₁ :=
    readWv_of_live?_eq (frame.fb buf₁.id hnb₁) hbuf₁ hbuf₁'
  have hread₂ : readWv hbuf₂' = readWv hbuf₂ :=
    readWv_of_live?_eq (frame.fb buf₂.id hnb₂) hbuf₂ hbuf₂'

  obtain ⟨w, ret, hrun, va03, va14, va25, vb03, vb14, vb25, heqw, hok, hf₁, hf₂⟩ :=
    fd_r43x6_ge_decode2_conforms (slotPtr s 0) (slotPtr s 1) (slotPtr s 2) buf₁
      (slotPtr s 3) (slotPtr s 4) (slotPtr s 5) buf₂ sAlloc frame.wf
      (hslot 0 (by norm_num)) (hslot 1 (by norm_num)) (hslot 2 (by norm_num))
      (hslot 3 (by norm_num)) (hslot 4 (by norm_num)) (hslot 5 (by norm_num))
      hbuf₁' hbuf₂'
      ⟨slots.ne (by decide), slots.ne (by decide), slots.ne (by decide),
       slots.ne (by decide), slots.ne (by decide), slots.ne (by decide),
       slots.ne (by decide), slots.ne (by decide), slots.ne (by decide),
       slots.ne (by decide), slots.ne (by decide), slots.ne (by decide),
       slots.ne (by decide), slots.ne (by decide), slots.ne (by decide)⟩
  rw [hread₁] at hok hf₁ hf₂
  rw [hread₂] at hok hf₂

  -- the frame invariant across the call: the six writes are all to slots.
  --
  -- Forward and pointwise, deliberately. Six nested `FrameBelow.splice`s
  -- under a `FrameBelow.of_equiv` type-check, but they do not *elaborate*:
  -- `FrameBelow.splice` pins its `t` and `x` from the expected type alone, so
  -- each level asks the unifier to solve `?s'.alloc =?= sAlloc.alloc`
  -- alongside `?s'.mem =?= <the splices below it>` -- projections of a record
  -- literal against a metavariable, over the whole six-splice term, six times
  -- over. That is where this proof used to hang. Rewriting `live?` one splice
  -- at a time keeps every step first-order.
  have fbw : FrameBelow s.alloc.nextFreeBlock s w := by
    intro b hb
    have hne : ∀ k : Nat, (slotPtr s k).id ≠ b := fun k he => by
      have hid := slots.id k
      rw [he] at hid
      omega
    rw [live?_of_equiv_mem' heqw b, live?_splice_ne (hne 5), live?_splice_ne (hne 4),
      live?_splice_ne (hne 3), live?_splice_ne (hne 2), live?_splice_ne (hne 1),
      live?_splice_ne (hne 0)]
    exact frame.fb b hb
  -- No `w.WF` here on purpose: nothing below needs it -- the `popFrame`
  -- ending is stated against the *entry* state's `hs`. If a later change does
  -- want it, write it forward (see the module docstring); the natural
  -- `GlobalState.WF.of_equiv frame.wf.splice.splice.splice.splice.splice.splice
  -- heqw.symm` is the same six-metavariable unification as `fbw`'s, and hangs.

  -- what each slot holds afterwards: its own splice wrote it, and the later
  -- ones in the chain miss its block
  have hb0 : readVec? (slotPtr s 0) w.mem = some va03 := by
    rw [readVec?_of_live?_eq (live?_of_equiv_mem' heqw (slotPtr s 0).id)]
    rw [readVec?_splice_ne (slots.ne (show (5 : Nat) ≠ 0 by decide)),
      readVec?_splice_ne (slots.ne (show (4 : Nat) ≠ 0 by decide)),
      readVec?_splice_ne (slots.ne (show (3 : Nat) ≠ 0 by decide)),
      readVec?_splice_ne (slots.ne (show (2 : Nat) ≠ 0 by decide)),
      readVec?_splice_ne (slots.ne (show (1 : Nat) ≠ 0 by decide)),
      readVec?_splice_self va03 (hslot 0 (by norm_num))]
  -- slot `k`'s own splice sits on top of slots `0 … k-1`, so the witness the
  -- readback wants is `hslot k` under that many `isVecPtr_splice`s -- and it
  -- goes in an `exact`, where the expected type is known, rather than in the
  -- `rw` list, where the extra splices would be metavariables
  have hb1 : readVec? (slotPtr s 1) w.mem = some va14 := by
    rw [readVec?_of_live?_eq (live?_of_equiv_mem' heqw (slotPtr s 1).id),
      readVec?_splice_ne (slots.ne (show (5 : Nat) ≠ 1 by decide)),
      readVec?_splice_ne (slots.ne (show (4 : Nat) ≠ 1 by decide)),
      readVec?_splice_ne (slots.ne (show (3 : Nat) ≠ 1 by decide)),
      readVec?_splice_ne (slots.ne (show (2 : Nat) ≠ 1 by decide))]
    exact readVec?_splice_self va14 (isVecPtr_splice (hslot 1 (by norm_num)))
  have hb2 : readVec? (slotPtr s 2) w.mem = some va25 := by
    rw [readVec?_of_live?_eq (live?_of_equiv_mem' heqw (slotPtr s 2).id),
      readVec?_splice_ne (slots.ne (show (5 : Nat) ≠ 2 by decide)),
      readVec?_splice_ne (slots.ne (show (4 : Nat) ≠ 2 by decide)),
      readVec?_splice_ne (slots.ne (show (3 : Nat) ≠ 2 by decide))]
    exact readVec?_splice_self va25
      (isVecPtr_splice (isVecPtr_splice (hslot 2 (by norm_num))))
  have hb3 : readVec? (slotPtr s 3) w.mem = some vb03 := by
    rw [readVec?_of_live?_eq (live?_of_equiv_mem' heqw (slotPtr s 3).id),
      readVec?_splice_ne (slots.ne (show (5 : Nat) ≠ 3 by decide)),
      readVec?_splice_ne (slots.ne (show (4 : Nat) ≠ 3 by decide))]
    exact readVec?_splice_self vb03
      (isVecPtr_splice (isVecPtr_splice (isVecPtr_splice (hslot 3 (by norm_num)))))
  have hb4 : readVec? (slotPtr s 4) w.mem = some vb14 := by
    rw [readVec?_of_live?_eq (live?_of_equiv_mem' heqw (slotPtr s 4).id),
      readVec?_splice_ne (slots.ne (show (5 : Nat) ≠ 4 by decide))]
    exact readVec?_splice_self vb14 (isVecPtr_splice (isVecPtr_splice
      (isVecPtr_splice (isVecPtr_splice (hslot 4 (by norm_num))))))
  have hb5 : readVec? (slotPtr s 5) w.mem = some vb25 := by
    rw [readVec?_of_live?_eq (live?_of_equiv_mem' heqw (slotPtr s 5).id)]
    exact readVec?_splice_self vb25 (isVecPtr_splice (isVecPtr_splice
      (isVecPtr_splice (isVecPtr_splice (isVecPtr_splice (hslot 5 (by norm_num)))))))

  -- ... and that they still fit there
  have hfw : ∀ k, k < 6 → IsVecPtr w.mem (slotPtr s k) := fun k hk =>
    ⟨fits_of_live?_eq (live?_of_equiv_mem' heqw (slotPtr s k).id)
      (fits_splice (fits_splice (fits_splice (fits_splice (fits_splice
        (fits_splice (frame.fits k hk))))))), by simp [slots.off k]⟩

  -- the two QUADs, at the state the copy runs in
  have hq₁ : Fits w.mem r₁ (3 * 8 * 64) := fits_of_live?_eq (fbw r₁.id hn₁) hr₁.1
  have hq₂ : Fits w.mem r₂ (3 * 8 * 64) := fits_of_live?_eq (fbw r₂.id hn₂) hr₂.1

  -- the six states the copy walks through
  refine name_of ({ w with mem := w.mem.splice r₁ (vecBV va03) }) fun n₁ hn₁' => ?_
  refine name_of ({ n₁ with mem := n₁.mem.splice (r₁.withOffset 64) (vecBV va14) }) fun n₂ hn₂' => ?_
  refine name_of ({ n₂ with mem := n₂.mem.splice (r₁.withOffset 128) (vecBV va25) }) fun n₃ hn₃' => ?_
  refine name_of ({ n₃ with mem := n₃.mem.splice r₂ (vecBV vb03) }) fun n₄ hn₄' => ?_
  refine name_of ({ n₄ with mem := n₄.mem.splice (r₂.withOffset 64) (vecBV vb14) }) fun n₅ hn₅' => ?_
  refine name_of ({ n₅ with mem := n₅.mem.splice (r₂.withOffset 128) (vecBV vb25) }) fun n₆ hn₆' => ?_

  -- what each slot still holds when its load comes round: every store so far
  -- was to a caller block, and no caller block is a slot
  -- the six stores' memories, named. `rw [hnₖ']` rewrites a *variable*, so
  -- this is the one place the record update is taken apart -- and it is taken
  -- apart against a goal rather than against a metavariable.
  have hm₁ : n₁.mem = w.mem.splice r₁ (vecBV va03) := by rw [hn₁']
  have hm₂ : n₂.mem = n₁.mem.splice (r₁.withOffset 64) (vecBV va14) := by rw [hn₂']
  have hm₃ : n₃.mem = n₂.mem.splice (r₁.withOffset 128) (vecBV va25) := by rw [hn₃']
  have hm₄ : n₄.mem = n₃.mem.splice r₂ (vecBV vb03) := by rw [hn₄']
  have hm₅ : n₅.mem = n₄.mem.splice (r₂.withOffset 64) (vecBV vb14) := by rw [hn₅']
  have hm₆ : n₆.mem = n₅.mem.splice (r₂.withOffset 128) (vecBV vb25) := by rw [hn₆']
  -- a field pointer sits in its QUAD's block, so it predates the frame too
  have hg₁ : ∀ o : BitVec 64, (r₁.withOffset o).id.id < s.alloc.nextFreeBlock :=
    fun _ => hn₁
  have hg₂ : ∀ o : BitVec 64, (r₂.withOffset o).id.id < s.alloc.nextFreeBlock :=
    fun _ => hn₂
  -- the two field offsets as naturals. `remainingFits` states the space it
  -- leaves as `n - o.toNat * 8`, and neither `norm_num` nor `omega` evaluates
  -- `BitVec.toNat` of a literal -- `is_zero` carries the same two `rfl`s.
  have h64 : (64 : BitVec 64).toNat = 64 := rfl
  have h128 : (128 : BitVec 64).toNat = 128 := rfl

  have hs1 : readVec? (slotPtr s 1) n₁.mem = some va14 :=
    readVec?_thru' slots hm₁ hn₁ hb1
  have hs2 : readVec? (slotPtr s 2) n₂.mem = some va25 :=
    readVec?_thru' slots hm₂ (hg₁ 64) (readVec?_thru' slots hm₁ hn₁ hb2)
  have hs3 : readVec? (slotPtr s 3) n₃.mem = some vb03 :=
    readVec?_thru' slots hm₃ (hg₁ 128) (readVec?_thru' slots hm₂ (hg₁ 64)
      (readVec?_thru' slots hm₁ hn₁ hb3))
  have hs4 : readVec? (slotPtr s 4) n₄.mem = some vb14 :=
    readVec?_thru' slots hm₄ hn₂ (readVec?_thru' slots hm₃ (hg₁ 128)
      (readVec?_thru' slots hm₂ (hg₁ 64) (readVec?_thru' slots hm₁ hn₁ hb4)))
  have hs5 : readVec? (slotPtr s 5) n₅.mem = some vb25 :=
    readVec?_thru' slots hm₅ (hg₂ 64) (readVec?_thru' slots hm₄ hn₂
      (readVec?_thru' slots hm₃ (hg₁ 128) (readVec?_thru' slots hm₂ (hg₁ 64)
        (readVec?_thru' slots hm₁ hn₁ hb5))))

  -- ... and that the slot and the QUAD being written still fit
  have hp1 : IsVecPtr n₁.mem (slotPtr s 1) :=
    isVecPtr_thru hm₁ (hfw 1 (by norm_num))
  have hp2 : IsVecPtr n₂.mem (slotPtr s 2) :=
    isVecPtr_thru hm₂ (isVecPtr_thru hm₁ (hfw 2 (by norm_num)))
  have hp3 : IsVecPtr n₃.mem (slotPtr s 3) :=
    isVecPtr_thru hm₃ (isVecPtr_thru hm₂ (isVecPtr_thru hm₁ (hfw 3 (by norm_num))))
  have hp4 : IsVecPtr n₄.mem (slotPtr s 4) :=
    isVecPtr_thru hm₄ (isVecPtr_thru hm₃ (isVecPtr_thru hm₂
      (isVecPtr_thru hm₁ (hfw 4 (by norm_num)))))
  have hp5 : IsVecPtr n₅.mem (slotPtr s 5) :=
    isVecPtr_thru hm₅ (isVecPtr_thru hm₄ (isVecPtr_thru hm₃
      (isVecPtr_thru hm₂ (isVecPtr_thru hm₁ (hfw 5 (by norm_num))))))
  have hf₁₁ : Fits n₁.mem r₁ (3 * 8 * 64) := fits_thru hm₁ hq₁
  have hf₁₂ : Fits n₂.mem r₁ (3 * 8 * 64) := fits_thru hm₂ (fits_thru hm₁ hq₁)
  have hf₂₃ : Fits n₃.mem r₂ (3 * 8 * 64) :=
    fits_thru hm₃ (fits_thru hm₂ (fits_thru hm₁ hq₂))
  have hf₂₄ : Fits n₄.mem r₂ (3 * 8 * 64) :=
    fits_thru hm₄ (fits_thru hm₃ (fits_thru hm₂ (fits_thru hm₁ hq₂)))
  have hf₂₅ : Fits n₅.mem r₂ (3 * 8 * 64) :=
    fits_thru hm₅ (fits_thru hm₄ (fits_thru hm₃ (fits_thru hm₂ (fits_thru hm₁ hq₂))))

  simp only [fd_ed25519_point_frombytes_2x_spec, Cfg.denote]
  refine existsLastThree ret ⟨va03, va14, va25⟩ ⟨vb03, vb14, vb25⟩ ?_
  refine Firedancer.run_runFunction' _ ?_
  refine ⟨n₆, ?_, ?_⟩

  case _ =>
    -- %0: the `alloca` count
    denote_step_reduce v 0 [LLVM.const?]
    subst hv0
    -- %1-%6: the six `wwl_t` locals
    peel_alloca_chain s, cw, 6
    simp only [slotPtr_0, slotPtr_1, slotPtr_2, slotPtr_3, slotPtr_4, slotPtr_5]
    rw [← hsAlloc]
    iterate 6 peel_lifetime
    -- %7: `fd_r43x6_ge_decode2`
    peel_call hrun with simp_spine

    -- `r₁`: three loads and three stores, at fields 0, 64 and 128
    peel_load_vec va03, (slotPtr s 0), (hfw 0 (by norm_num)), (readVec_eq_of hb0), w
    peel_store va03, r₁, hq₁, w as n₁ := hn₁'
    peel_load_vec va14, (slotPtr s 1), hp1, (readVec_eq_of hs1), n₁
    -- `peel_gep` leaves the size as `remainingFits` states it, `n - o.toNat *
    -- 8`; `peel_store`'s own `Fits.mono … (by omega)` cannot evaluate the
    -- `BitVec.toNat`, so each field's `Fits` is cut down to a literal here.
    peel_gep 64 with r₁, hf₁₁, n₁ as r₁f1
    have hs₁f1 : Fits n₁.mem r₁f1 512 := Fits.mono hr₁f1 (by simp only [h64]; omega)
    peel_store va14, r₁f1, hs₁f1, n₁ as n₂ := hn₂'
    peel_load_vec va25, (slotPtr s 2), hp2, (readVec_eq_of hs2), n₂
    peel_gep 128 with r₁, hf₁₂, n₂ as r₁f2
    have hs₁f2 : Fits n₂.mem r₁f2 512 := Fits.mono hr₁f2 (by simp only [h128]; omega)
    peel_store va25, r₁f2, hs₁f2, n₂ as n₃ := hn₃'

    -- `r₂`, the same three steps one state along
    peel_load_vec vb03, (slotPtr s 3), hp3, (readVec_eq_of hs3), n₃
    peel_store vb03, r₂, hf₂₃, n₃ as n₄ := hn₄'
    peel_load_vec vb14, (slotPtr s 4), hp4, (readVec_eq_of hs4), n₄
    peel_gep 64 with r₂, hf₂₄, n₄ as r₂f1
    have hs₂f1 : Fits n₄.mem r₂f1 512 := Fits.mono hr₂f1 (by simp only [h64]; omega)
    peel_store vb14, r₂f1, hs₂f1, n₄ as n₅ := hn₅'
    peel_load_vec vb25, (slotPtr s 5), hp5, (readVec_eq_of hs5), n₅
    peel_gep 128 with r₂, hf₂₅, n₅ as r₂f2
    have hs₂f2 : Fits n₅.mem r₂f2 512 := Fits.mono hr₂f2 (by simp only [h128]; omega)
    peel_store vb25, r₂f2, hs₂f2, n₅ as n₆ := hn₆'
    iterate 6 peel_lifetime
    simp_return

  case _ =>
    -- the frame goes away; what is left is `r₁`'s three stores and `r₂`'s
    have hmem : n₆.mem = (((((w.mem.splice r₁ (vecBV va03)).splice
        (r₁.withOffset 64) (vecBV va14)).splice
        (r₁.withOffset 128) (vecBV va25)).splice r₂ (vecBV vb03)).splice
        (r₂.withOffset 64) (vecBV vb14)).splice (r₂.withOffset 128) (vecBV vb25) := by
      rw [hm₆, hm₅, hm₄, hm₃, hm₂, hm₁]
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- the memory
      refine popFrame_equiv_written (fun b => b = r₁.id ∨ b = r₂.id) hs
        (fun b hb => by rcases hb with rfl | rfl <;> assumption) ?_ ?_ ?_
      -- the six disequalities, named. A bare `fun he => hbw (Or.inl he.symm)`
      -- leaves `live?_splice_ne`'s pointer a metavariable -- nothing in that
      -- lambda's type says which splice it is about -- and the rewrite then
      -- matches nothing. Naming them pins each `p` by first-order matching on
      -- `?p.id`, the way `slots.ne` does for the slots.
      · intro b hb hbw
        have e₁ : r₁.id ≠ b := fun he => hbw (Or.inl he.symm)
        have e₂ : r₂.id ≠ b := fun he => hbw (Or.inr he.symm)
        have f₁ : ∀ o : BitVec 64, (r₁.withOffset o).id ≠ b :=
          fun _ he => hbw (Or.inl he.symm)
        have f₂ : ∀ o : BitVec 64, (r₂.withOffset o).id ≠ b :=
          fun _ he => hbw (Or.inr he.symm)
        rw [hmem, live?_splice_ne (f₂ 128), live?_splice_ne (f₂ 64),
          live?_splice_ne e₂, live?_splice_ne (f₁ 128), live?_splice_ne (f₁ 64),
          live?_splice_ne e₁]
        exact fbw b hb
      · intro b hbw
        have e₁ : r₁.id ≠ b := fun he => hbw (Or.inl he.symm)
        have e₂ : r₂.id ≠ b := fun he => hbw (Or.inr he.symm)
        have f₁ : ∀ o : BitVec 64, (r₁.withOffset o).id ≠ b :=
          fun _ he => hbw (Or.inl he.symm)
        have f₂ : ∀ o : BitVec 64, (r₂.withOffset o).id ≠ b :=
          fun _ he => hbw (Or.inr he.symm)
        show (MemoryState.writeQuad (MemoryState.writeQuad s.mem r₁ _) r₂ _).live? b = _
        simp only [MemoryState.writeQuad]
        rw [live?_splice_ne (f₂ 128), live?_splice_ne (f₂ 64), live?_splice_ne e₂,
          live?_splice_ne (f₁ 128), live?_splice_ne (f₁ 64), live?_splice_ne e₁]
      · intro b hb
        have hbase : w.mem.live? b = s.mem.live? b :=
          fbw b (by rcases hb with rfl | rfl <;> assumption)
        rw [hmem]
        show _ = (MemoryState.writeQuad (MemoryState.writeQuad s.mem r₁ _) r₂ _).live? b
        simp only [MemoryState.writeQuad]
        exact live?_splice_congr' (live?_splice_congr' (live?_splice_congr'
          (live?_splice_congr' (live?_splice_congr' (live?_splice_congr' hbase)))))
    · exact fun h₁ h₂ => hok h₁ h₂
    · intro h₁
      obtain ⟨hr, e0, e1, e2, e3, e4, e5⟩ := hf₁ h₁
      exact ⟨hr, by rw [Quad.ext_iff]; exact ⟨e0, e1, e2⟩,
        by rw [Quad.ext_iff]; exact ⟨e3, e4, e5⟩⟩
    · intro h₁ h₂
      obtain ⟨hr, e0, e1, e2, e3, e4, e5⟩ := hf₂ h₁ h₂
      exact ⟨hr, by rw [Quad.ext_iff]; exact ⟨e0, e1, e2⟩,
        by rw [Quad.ext_iff]; exact ⟨e3, e4, e5⟩⟩

end Firedancer.Avx512
