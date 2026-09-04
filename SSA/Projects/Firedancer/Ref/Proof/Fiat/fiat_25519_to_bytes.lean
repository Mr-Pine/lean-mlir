/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.Firedancer.Ref.Spec.Fiat.fiat_25519_to_bytes
import SSA.Projects.Firedancer.MLIR.DenoteStep
import SSA.Projects.Firedancer.Ref.Proof.MemoryOperations
import SSA.Projects.Firedancer.Ref.Proof.Fiat.fiat_25519_subborrowx_u51
import SSA.Projects.Firedancer.Ref.Proof.Fiat.fiat_25519_addcarryx_u51
import SSA.Projects.Firedancer.Ref.Proof.Fiat.fiat_25519_cmovznz_u64
import Mathlib.Tactic.Zify
import Mathlib.Tactic.LinearCombination

/-!
# `fiat_25519_to_bytes` conforms to its spec

One basic block: 21 scratch cells, a five-step borrow chain against `p`, a
`cmovznz` mask, a five-step add-back, then 32 byte stores into the caller's
buffer.

The cells are indexed rather than named. Their ids run consecutively from the
entry counter, so separation between any two is an arithmetic fact about their
indices — with 21 cells the alternative is 210 disequalities.

`Wrote₁`/`Wrote₂` package one peeled kernel call: the cells it wrote, and the
one clause (`other`) from which every surviving fact is transported.
-/

namespace Firedancer.Ref
open LeanMLIR SLLVM
open InstCombine (LLVM)

namespace ToBytes

/-! ### The scratch frame -/

/-- Widths of the 21 cells, in allocation order: each `subborrowx`/`addcarryx`
takes a 64-bit limb cell and an 8-bit borrow cell, and the `cmovznz` mask at
index 10 sits between the two chains. Indexed by `Nat`, not `Fin`, because
`GlobalState.allocaChain` is. -/
def cw (i : Nat) : Nat :=
  ([64, 8, 64, 8, 64, 8, 64, 8, 64, 8, 64,
    64, 8, 64, 8, 64, 8, 64, 8, 64, 8] : List Nat).getD i 0

/-- The 21 cells, as the chain's pointers. -/
def cellPtr (s : GlobalState) : Fin 21 → Pointer := fun i => s.chainPtr cw i.val

/-- `p`'s base-`2 ^ 51` limbs, which the borrow chain subtracts one at a time:
`2 ^ 51 - 19` at the bottom, `2 ^ 51 - 1` above it. The region carries them as
64-bit constants; naming them keeps the digit equations readable. -/
def pLimb (k : ℕ) : ℕ := if k = 0 then 2 ^ 51 - 19 else 2 ^ 51 - 1

/-- The state the prologue reaches: the entry state plus the 21 `alloca`s.
The step equation is `rfl`, which is what `peel_alloca` wants. -/
abbrev frameState (s : GlobalState) : GlobalState := s.allocaChain cw 21

/-- The frame `fiat_25519_to_bytes` allocates. `id` is the whole separation
story: consecutive ids from `n₀`, with the caller's buffer `o` and input `q`
strictly below. -/
structure Cells (t : Fin 21 → Pointer) (o q : Pointer) (n₀ : Nat) : Prop where
  id : ∀ i, (t i).id.id = n₀ + i.val
  off : ∀ i, (t i).offset = 0
  ido : o.id.id < n₀
  idq : q.id.id < n₀

namespace Cells

variable {t : Fin 21 → Pointer} {o q : Pointer} {n₀ : Nat} (hc : Cells t o q n₀)
include hc

/-- Distinct cells are distinct blocks -- by `omega` on the indices. -/
theorem ne {i j : Fin 21} (hij : i ≠ j) : (t i).id ≠ (t j).id := fun h => by
  have hi := hc.id i
  have hj := hc.id j
  have h' : (t i).id.id = (t j).id.id := by rw [h]
  exact hij (Fin.ext (by omega))

/-- A cell is never one of the caller's blocks: it is at or above `n₀`. -/
theorem ne_below {i : Fin 21} {b : BlockId} (hb : b.id < n₀) : (t i).id ≠ b := fun h => by
  have hi := hc.id i
  have h' : (t i).id.id = b.id := by rw [h]
  omega

theorem ne_o (i : Fin 21) : (t i).id ≠ o.id := hc.ne_below hc.ido
theorem ne_q (i : Fin 21) : (t i).id ≠ q.id := hc.ne_below hc.idq

end Cells

/-- What holds of a state part-way through the walk. `Cells` is about the
pointers and is fixed once; this is about the state and is rebuilt at every
call, by `step₁`/`step₂`. Cell *values* stay outside it: each is needed over a
different stretch of the walk, so carrying all 21 would be dead weight. -/
structure Frame (t : Fin 21 → Pointer) (n₀ : Nat) (s₀ u : GlobalState) : Prop where
  wf : u.WF
  fits : ∀ i, Fits u.mem (t i) (cw i.val)
  fb : FrameBelow n₀ s₀ u

/-- The prologue's facts: `Cells` for the pointers, `Frame` for the state. -/
lemma cells_frame (s : GlobalState) (hs : s.WF) {o q : Pointer}
    (ho : Fits s.mem o (32 * 8)) (hq : Fits s.mem q (5 * 64)) :
    Cells (cellPtr s) o q s.alloc.nextFreeBlock
    ∧ Frame (cellPtr s) s.alloc.nextFreeBlock s (frameState s) :=
  ⟨{ id := fun i => GlobalState.chainPtr_id i.val
     off := fun i => GlobalState.chainPtr_offset i.val
     ido := lt_nextFreeBlock_of_fits hs ho
     idq := lt_nextFreeBlock_of_fits hs hq },
   { wf := GlobalState.WF.allocaChain hs 21
     fits := fun i => GlobalState.fits_chainPtr i.isLt
     fb := FrameBelow.allocaChain (le_refl _) (FrameBelow.refl _ _) 21 }⟩

/-! ### What one kernel call leaves behind

Each callee writes through its out-parameters and nothing else. `other` is
the handle: with it, `readWord?_of_live?_eq` transports any cell value, and
`FrameBelow` extends, across the call. -/

/-- A call that wrote one 64-bit cell (`cmovznz`). -/
structure Wrote₁ (a : Pointer) (x : BitVec 64) (u u' : GlobalState) : Prop where
  wf : u'.WF
  fit : Fits u'.mem a 64
  val : readWord fit = x
  other : ∀ c : BlockId, c ≠ a.id → u'.mem.live? c = u.mem.live? c

/-- A call that wrote a 64-bit cell and an 8-bit cell (`subborrowx`,
`addcarryx`). -/
structure Wrote₂ (a b : Pointer) (x : BitVec 64) (y : BitVec 8)
    (u u' : GlobalState) : Prop where
  wf : u'.WF
  fita : Fits u'.mem a 64
  fitb : Fits u'.mem b 8
  vala : readWord fita = x
  valb : readWord fitb = y
  other : ∀ c : BlockId, c ≠ a.id → c ≠ b.id → u'.mem.live? c = u.mem.live? c

namespace Wrote₁
variable {a : Pointer} {x : BitVec 64} {u u' : GlobalState}

/-- A cell the call did not write keeps its value, `Fits` witness and all. -/
theorem survive (w : Wrote₁ a x u u') {r : Pointer} {n : Nat} (hr : r.id ≠ a.id)
    (h : Fits u.mem r n) : ∃ h' : Fits u'.mem r n, readWord h' = readWord h :=
  readWord_of_live?_eq (w.other r.id hr) h

/-- The proof-free transport, matching `Wrote₂.survive?`. -/
theorem survive? (w : Wrote₁ a x u u') {r : Pointer} (n : Nat) (hra : r.id ≠ a.id) :
    readWord? r n u'.mem = readWord? r n u.mem :=
  readWord?_of_live?_eq (w.other r.id hra)

theorem frame (w : Wrote₁ a x u u') {n₀ : Nat} {s₀ : GlobalState}
    (ha : n₀ ≤ a.id.id) (hf : FrameBelow n₀ s₀ u) : FrameBelow n₀ s₀ u' :=
  fun b hb => (w.other b (fun h => by rw [h] at hb; omega)).trans (hf b hb)

end Wrote₁

namespace Wrote₂
variable {a b : Pointer} {x : BitVec 64} {y : BitVec 8} {u u' : GlobalState}

theorem survive (w : Wrote₂ a b x y u u') {r : Pointer} {n : Nat}
    (hra : r.id ≠ a.id) (hrb : r.id ≠ b.id) (h : Fits u.mem r n) :
    ∃ h' : Fits u'.mem r n, readWord h' = readWord h :=
  readWord_of_live?_eq (w.other r.id hra hrb) h

/-- The same, proof-free: what a cell the call did not write reads as. Chains,
so a value written several calls back can be recovered at the current state. -/
theorem survive? (w : Wrote₂ a b x y u u') {r : Pointer} (n : Nat)
    (hra : r.id ≠ a.id) (hrb : r.id ≠ b.id) :
    readWord? r n u'.mem = readWord? r n u.mem :=
  readWord?_of_live?_eq (w.other r.id hra hrb)

theorem frame (w : Wrote₂ a b x y u u') {n₀ : Nat} {s₀ : GlobalState}
    (ha : n₀ ≤ a.id.id) (hb : n₀ ≤ b.id.id) (hf : FrameBelow n₀ s₀ u) :
    FrameBelow n₀ s₀ u' :=
  fun c hc => (w.other c (fun h => by rw [h] at hc; omega)
    (fun h => by rw [h] at hc; omega)).trans (hf c hc)

end Wrote₂

/-! ### Rebuilding the frame after a call

One lemma per kernel shape. The two written cells come from the `Wrote` facts;
every other cell is transported by `other`, and separation is `Cells.ne`. -/

namespace Frame
variable {t : Fin 21 → Pointer} {o q : Pointer} {n₀ : Nat} {s₀ u u' : GlobalState}

theorem step₁ (hf : Frame t n₀ s₀ u) (hc : Cells t o q n₀) {i : Fin 21}
    (hci : cw i.val = 64) {x : BitVec 64} (w : Wrote₁ (t i) x u u') :
    Frame t n₀ s₀ u' where
  wf := w.wf
  fits := fun k => by
    by_cases hki : k = i
    · subst hki; rw [hci]; exact w.fit
    · exact fits_of_live?_eq (w.other _ (hc.ne hki)) (hf.fits k)
  fb := w.frame (by rw [hc.id i]; omega) hf.fb

theorem step₂ (hf : Frame t n₀ s₀ u) (hc : Cells t o q n₀) {i j : Fin 21} (hij : i ≠ j)
    (hci : cw i.val = 64) (hcj : cw j.val = 8) {x : BitVec 64} {y : BitVec 8}
    (w : Wrote₂ (t i) (t j) x y u u') : Frame t n₀ s₀ u' where
  wf := w.wf
  fits := fun k => by
    by_cases hki : k = i
    · subst hki; rw [hci]; exact w.fita
    by_cases hkj : k = j
    · subst hkj; rw [hcj]; exact w.fitb
    · exact fits_of_live?_eq (w.other _ (hc.ne hki) (hc.ne hkj)) (hf.fits k)
  fb := w.frame (by rw [hc.id i]; omega) (by rw [hc.id j]; omega) hf.fb

end Frame

/-! ### The limb values the borrow chain leaves

`Frame` carries `Fits` for every cell; the add-back also needs the *values* of
the borrow chain's limbs, because `addcarry_step`'s contract bounds its
operands. `Limbs t u k` is that, as far as the chain has got: cells
`0, 2, …, 2(k-1)` hold reduced limbs. It is stated over `readWord?` rather than
`readWord`, so a call transports it with `readWord?_of_live?_eq` and a use
discharges it from the cell's block. -/

/-- The cell holding the borrow chain's `j`-th limb. -/
def limbCell (j : Fin 5) : Fin 21 := ⟨2 * j.val, by have := j.isLt; omega⟩

theorem limbCell_ne {a b : Fin 5} (h : a ≠ b) : limbCell a ≠ limbCell b := by
  have := Fin.val_ne_of_ne h
  simp only [limbCell, ne_eq, Fin.mk.injEq]
  omega

/-- The first `k` limb cells hold reduced limbs. -/
def Limbs (t : Fin 21 → Pointer) (u : GlobalState) (k : ℕ) : Prop :=
  ∀ j : Fin 5, j.val < k → ∀ v : BitVec 64,
    readWord? (t (limbCell j)) 64 u.mem = some v → v.toNat < 2 ^ 51

namespace Limbs
variable {t : Fin 21 → Pointer} {o q : Pointer} {n₀ k : Nat} {u u' : GlobalState}

/-- Before the chain starts there is nothing to know. -/
theorem nil : Limbs t u 0 := fun _ hj _ _ => absurd hj (by omega)

/-- A call that wrote no limb cell below `k` leaves the invariant alone. -/
theorem keep₂ (hl : Limbs t u k) (hc : Cells t o q n₀) {i j : Fin 21}
    (hi : ∀ b : Fin 5, b.val < k → limbCell b ≠ i)
    (hj : ∀ b : Fin 5, b.val < k → limbCell b ≠ j)
    {x : BitVec 64} {y : BitVec 8} (w : Wrote₂ (t i) (t j) x y u u') : Limbs t u' k :=
  fun b hb v hv => hl b hb v (by
    rwa [readWord?_of_live?_eq (w.other _ (hc.ne (hi b hb)) (hc.ne (hj b hb)))] at hv)

/-- The `cmovznz` version. -/
theorem keep₁ (hl : Limbs t u k) (hc : Cells t o q n₀) {i : Fin 21}
    (hi : ∀ b : Fin 5, b.val < k → limbCell b ≠ i)
    {x : BitVec 64} (w : Wrote₁ (t i) x u u') : Limbs t u' k :=
  fun b hb v hv => hl b hb v (by
    rwa [readWord?_of_live?_eq (w.other _ (hc.ne (hi b hb)))] at hv)

/-- The `k`-th subborrow writes limb cell `k`, extending the invariant by one. -/
theorem grow (hl : Limbs t u k) (hc : Cells t o q n₀) {c : Fin 5} (hck : c.val = k)
    {j : Fin 21} (hj : ∀ b : Fin 5, b.val ≤ k → limbCell b ≠ j)
    {x : BitVec 64} {y : BitVec 8} (w : Wrote₂ (t (limbCell c)) (t j) x y u u')
    (hx : x.toNat < 2 ^ 51) : Limbs t u' (k + 1) := by
  intro b hb v hv
  by_cases hbc : b = c
  · subst hbc
    rw [readWord?_eq_some w.fita w.vala] at hv
    have : v = x := by simpa using hv.symm
    exact this ▸ hx
  · have hbk : b.val < k := by
      have := Fin.val_ne_of_ne hbc
      omega
    rw [readWord?_of_live?_eq (w.other _ (hc.ne (limbCell_ne hbc))
      (hc.ne (hj b (by omega))))] at hv
    exact hl b hbk v hv

end Limbs

/-- A read of `arg1[k]` in any state the frame reaches *is* the spec's
`readLimb` at the entry state: a callee writes only its own scratch cells, so
the frame transports the caller's block. This is what keeps the borrow chain's
digit equations stated over the field element rather than over a block slice. -/
theorem limb_read {s u : GlobalState} {q qp : Pointer}
    (hq : IsFieldElemPtr s.mem q)
    (hfb : u.mem.live? q.id = s.mem.live? q.id)
    {k : Fin 5} (hid : qp.id = q.id)
    (hoff : qp.offsetInBits = q.offsetInBits + 64 * k.toNat)
    {v : BitVec 64} (hv : readWord? qp 64 u.mem = some v) :
    v.toNat = readLimb k hq := by
  rw [readWord?_of_live?_eq (p := qp) (m := s.mem) (by rw [hid]; exact hfb)] at hv
  have he := readLimb_eq_of_readWord? hq hid hoff hv
  have hlt := readLimb_lt k hq
  rw [← he]
  simp only [BitVec.natCast_eq_ofNat, BitVec.toNat_ofNat]
  omega

/-- `limb_read` at the `BitVec` level, for folding the load itself: the word
the walk holds is the spec's limb, cast. Frees the block from the goal. -/
theorem limb_readBV {s u : GlobalState} {q qp : Pointer}
    (hq : IsFieldElemPtr s.mem q) (hfb : u.mem.live? q.id = s.mem.live? q.id)
    {k : Fin 5} (hid : qp.id = q.id)
    (hoff : qp.offsetInBits = q.offsetInBits + 64 * k.toNat)
    {v : BitVec 64} (hv : readWord? qp 64 u.mem = some v) :
    v = ((readLimb k hq : ℕ) : BitVec 64) := by
  apply BitVec.eq_of_toNat_eq
  rw [limb_read hq hfb hid hoff hv]
  simp only [BitVec.natCast_eq_ofNat, BitVec.toNat_ofNat]
  exact (Nat.mod_eq_of_lt (readLimb_lt k hq)).symm

/-- ... and so it inherits `LimbBounds`. -/
theorem limb_bound {s u : GlobalState} {q qp : Pointer} {bound : ℕ}
    (hq : IsFieldElemPtr s.mem q) (hbd : LimbBounds hq bound)
    (hfb : u.mem.live? q.id = s.mem.live? q.id)
    {k : Fin 5} (hid : qp.id = q.id)
    (hoff : qp.offsetInBits = q.offsetInBits + 64 * k.toNat)
    {v : BitVec 64} (hv : readWord? qp 64 u.mem = some v) : v.toNat ≤ bound := by
  rw [limb_read hq hfb hid hoff hv]; exact hbd k

/-! ### The kernels, peeled

One lemma per callee, turning its conformance statement into the run equation
`peel_call_nil` consumes plus a `Wrote₁`/`Wrote₂`. The output values are
spelled as the callee's spec spells them; the arithmetic that identifies them
with the borrow chain is a separate, memory-free argument. -/

/-- `subborrowx(a, b, c, x, y)`: `a` and `b` split `x - c - y` into a limb and a
borrow. `hx`/`hcy`/`hcy'` are the spec's contract; `bo ≤ 1` is the half of it the
next step in the chain needs back. -/
lemma subborrow_step {a b : Pointer} {c : BitVec 8} {x y : BitVec 64}
    {u : GlobalState} (hu : u.WF) (hab : a.id ≠ b.id)
    (ha : Fits u.mem a 64) (hb : Fits u.mem b 8)
    (hx : x.toNat ≤ 2 ^ 51) (hcy : 1 ≤ c.toNat + y.toNat) (hcy' : c.toNat + y.toNat ≤ 2 ^ 51) :
    ∃ (u' : GlobalState) (lo : BitVec 64) (bo : BitVec 8),
      StateT.run (runFunction (fiat_25519_subborrowx_u51.denote
        (Ctxt.Valuation.ofHVector [.value y, .value x, .value c, .value b, .value a]ₕ))) u
        = .value ([]ₕ, u')
      ∧ lo.toNat < 2 ^ 51
      ∧ bo.toNat ≤ 1
      ∧ lo.toNat + c.toNat + y.toNat = x.toNat + 2 ^ 51 * bo.toNat
      ∧ Wrote₂ a b lo bo u u' := by
  obtain ⟨lo, bo, hlo, hsum, u', hrun, heq⟩ :=
    fiat_25519_subborrowx_u51_conforms a b c x y u hu ha hb hx hcy hcy'
  have hbo : bo.toNat ≤ 1 := by omega
  exact ⟨u', lo, bo, hrun, hlo, hbo, hsum, {
    wf := GlobalState.WF.of_equiv hu.splice.splice heq
    fita := fits_of_live?_eq (heq.live a.id).symm (fits_splice (fits_splice ha))
    fitb := fits_of_live?_eq (heq.live b.id).symm (fits_splice (fits_splice hb))
    vala := readWord_eq_of (by
      rw [readWord?_of_live?_eq (heq.live a.id).symm, readWord?_splice_ne (Ne.symm hab)]
      exact readWord?_splice_self _ ha)
    valb := readWord_eq_of (by
      rw [readWord?_of_live?_eq (heq.live b.id).symm]
      exact readWord?_splice_self _ (fits_splice hb))
    other := fun z hza hzb => by
      rw [← heq.live z, live?_splice_ne (fun h => hzb h.symm),
        live?_splice_ne (fun h => hza h.symm)] }⟩

/-- `addcarryx(a, b, c, x, y)`: `a` and `b` are the base-`2 ^ 51` digits of
`c + x + y`. `hc`/`hx`/`hy` are fiat's contract, passed through to the spec;
`co ≤ 1` is the half of it the next step in the chain needs back. -/
lemma addcarry_step {a b : Pointer} {c : BitVec 8} {x y : BitVec 64}
    {u : GlobalState} (hu : u.WF) (hab : a.id ≠ b.id)
    (ha : Fits u.mem a 64) (hb : Fits u.mem b 8)
    (hc : c.toNat ≤ 1) (hx : x.toNat < 2 ^ 51) (hy : y.toNat < 2 ^ 51) :
    ∃ (u' : GlobalState) (lo : BitVec 64) (co : BitVec 8),
      StateT.run (runFunction (fiat_25519_addcarryx_u51.denote
        (Ctxt.Valuation.ofHVector [.value y, .value x, .value c, .value b, .value a]ₕ))) u
        = .value ([]ₕ, u')
      ∧ lo.toNat < 2 ^ 51
      ∧ co.toNat ≤ 1
      ∧ lo.toNat + 2 ^ 51 * co.toNat = c.toNat + x.toNat + y.toNat
      ∧ Wrote₂ a b lo co u u' := by
  obtain ⟨lo, co, hlo, hsum, u', hrun, heq⟩ :=
    fiat_25519_addcarryx_u51_conforms a b c x y u hu ha hb hc hx hy
  have hco : co.toNat ≤ 1 := by omega
  exact ⟨u', lo, co, hrun, hlo, hco, hsum, {
    wf := GlobalState.WF.of_equiv hu.splice.splice heq
    fita := fits_of_live?_eq (heq.live a.id).symm (fits_splice (fits_splice ha))
    fitb := fits_of_live?_eq (heq.live b.id).symm (fits_splice (fits_splice hb))
    vala := readWord_eq_of (by
      rw [readWord?_of_live?_eq (heq.live a.id).symm, readWord?_splice_ne (Ne.symm hab)]
      exact readWord?_splice_self _ ha)
    valb := readWord_eq_of (by
      rw [readWord?_of_live?_eq (heq.live b.id).symm]
      exact readWord?_splice_self _ (fits_splice hb))
    other := fun z hza hzb => by
      rw [← heq.live z, live?_splice_ne (fun h => hzb h.symm),
        live?_splice_ne (fun h => hza h.symm)] }⟩

/-- `cmovznz(a, c, x, y)`: `a ← x` on a zero condition byte, `y` otherwise. -/
lemma cmovznz_step {a : Pointer} {c : BitVec 8} {x y : BitVec 64}
    {u : GlobalState} (hu : u.WF) (ha : Fits u.mem a 64) :
    ∃ (u' : GlobalState) (v : BitVec 64),
      StateT.run (runFunction (fiat_25519_cmovznz_u64.denote
        (Ctxt.Valuation.ofHVector [.value y, .value x, .value c, .value a]ₕ))) u
        = .value ([]ₕ, u')
      ∧ v = (if c = 0#8 then x else y)
      ∧ Wrote₁ a v u u' := by
  obtain ⟨u', hrun, heq⟩ := fiat_25519_cmovznz_u64_conforms a c x y u hu ha
  exact ⟨u', _, hrun, rfl, {
    wf := GlobalState.WF.of_equiv hu.splice heq
    fit := fits_of_live?_eq (heq.live a.id).symm (fits_splice ha)
    val := readWord_eq_of (by
      rw [readWord?_of_live?_eq (heq.live a.id).symm]
      exact readWord?_splice_self _ ha)
    other := fun z hz => by
      rw [← heq.live z, live?_splice_ne (fun h => hz h.symm)] }⟩

/-! ### The walk

Cell `2k` holds fiat's `x(2k+1)` and cell `2k+1` its borrow `x(2k+2)`, for
`k < 5`; cell 10 is the `cmovznz` mask `x11`; cell `11+2k` holds `x(12+2k)`
and cell `12+2k` its carry `x(13+2k)`. Names follow
`third_party/fiat-crypto/curve25519_64.c`. -/

/-! ### Walk shorthands

Three shapes repeat once per kernel call. Spelled out they bury the argument
that is actually being made; each is a line here. All three assume the entry
state is named `s` and the frame facts `cells`/`hq`, as the walk below has
them. Staged with the lemmas above. -/

open Lean Elab Tactic in
/-- `cell_facts w, i, u, f` names the block behind scratch cell `i`, which is
`w` bits wide, in state `u` under frame `f`. Pure bookkeeping: it never reads
the goal, so it belongs *above* the split, where the goal is still one line.
Run against the walk's goal each `obtain` reverts the whole thing and costs
over a second. -/
elab "cell_facts " w:num ", " i:num ", " u:term ", " f:term : tactic => do
  let sfx := subscript i.getNat
  let st := mkIdent (Name.mkSimple "s")
  let hcell := mkIdent (Name.mkSimple ("hcell" ++ sfx))
  let blk := mkIdent (Name.mkSimple ("c" ++ sfx ++ "blk"))
  let hblk := mkIdent (Name.mkSimple ("hc" ++ sfx ++ "blk"))
  let hlen := mkIdent (Name.mkSimple ("hc" ++ sfx ++ "len"))
  evalTactic (← `(tactic| have $hcell:ident :
    Fits ($u).mem (cellPtr $st $i) $w := ($f).fits $i))
  evalTactic (← `(tactic| obtain ⟨$blk:ident, $hblk:ident, $hlen:ident⟩ := id $hcell))

open Lean Elab Tactic in
/-- `peel_cell w, i, u` runs the load of scratch cell `i` against the block
`cell_facts` named. -/
elab "peel_cell " w:num ", " i:num ", " u:term : tactic => do
  let sfx := subscript i.getNat
  let st := mkIdent (Name.mkSimple "s")
  let blk := mkIdent (Name.mkSimple ("c" ++ sfx ++ "blk"))
  let hblk := mkIdent (Name.mkSimple ("hc" ++ sfx ++ "blk"))
  evalTactic (← `(tactic|
    peel_load (.bitvec (.concrete $w)), $blk, (cellPtr $st $i), $hblk, $u))

open Lean Elab Tactic in
/-- `limb_facts k, u, f` names the pointer to `arg1[k]`, its `Fits` and its
block. Pure bookkeeping, so it belongs above the split. -/
elab "limb_facts " k:num ", " u:term ", " f:term : tactic => do
  let sfx := subscript k.getNat
  let qq := mkIdent (Name.mkSimple "q")
  let hqq := mkIdent (Name.mkSimple "hq")
  let hcells := mkIdent (Name.mkSimple "cells")
  let hqu := mkIdent (Name.mkSimple ("hqu" ++ sfx))
  let qp := mkIdent (Name.mkSimple ("qp" ++ sfx))
  let hqp := mkIdent (Name.mkSimple ("hqp" ++ sfx))
  let qblk := mkIdent (Name.mkSimple ("qblk" ++ sfx))
  let hqblk := mkIdent (Name.mkSimple ("hqblk" ++ sfx))
  let hqlen := mkIdent (Name.mkSimple ("hqlen" ++ sfx))
  let off := Syntax.mkNumLit (toString (8 * k.getNat))
  let rem := Syntax.mkNumLit (toString ((5 - k.getNat) * 64))
  evalTactic (← `(tactic| have $hqu:ident : Fits ($u).mem $qq (5 * 64) :=
    fits_of_live?_eq (($f).fb ($qq).id ($hcells).idq) ($hqq).left))
  evalTactic (← `(tactic| let $qp:ident := ($qq).withOffset (($off) : BitVec 64)))
  evalTactic (← `(tactic| have $hqp:ident : Fits ($u).mem $qp $rem := by
    simpa using remainingFits ($u).mem $qq $hqu ($off) (by simp)))
  evalTactic (← `(tactic| obtain ⟨$qblk:ident, $hqblk:ident, $hqlen:ident⟩ := id $hqp))

open Lean Elab Tactic in
/-- `limb_peel k, u` runs the `getelementptr`/`load` pair for `arg1[k]` against
the pointer `limb_facts` named. -/
elab "limb_peel " k:num ", " u:term : tactic => do
  let sfx := subscript k.getNat
  let vBase := mkIdent (Name.mkSimple "v")
  let n ← nextStepIndex (← getMainGoal)
  let nLit := Syntax.mkNumLit (toString n)
  let v := mkIdent (Name.mkSimple ("v" ++ toString n))
  let hv := mkIdent (Name.mkSimple ("hv" ++ toString n))
  let qp := mkIdent (Name.mkSimple ("qp" ++ sfx))
  let qblk := mkIdent (Name.mkSimple ("qblk" ++ sfx))
  let hqblk := mkIdent (Name.mkSimple ("hqblk" ++ sfx))
  evalTactic (← `(tactic| denote_step_all $vBase $nLit))
  evalTactic (← `(tactic| denote_eval $vBase $nLit $nLit))
  evalTactic (← `(tactic| have vValue : $v = .value $qp := by
    simp [$hv:ident, gep, ptradd, $qp:ident, Pointer.withOffset,
      Ctxt.Valuation.singleton, LLVM.add, LLVM.mul, LLVM.const?, LLVM.add?,
      LLVM.mul?, simp_sllvm]))
  evalTactic (← `(tactic| subst vValue))
  evalTactic (← `(tactic| clear $hv))
  evalTactic (← `(tactic| peel_load (.bitvec (.concrete 64)), $qblk, $qp, $hqblk, $u))

/-- The borrow and carry kernels share one signature. -/
macro "peel_kernel_call " h:ident : tactic =>
  `(tactic| rw [BlockCom.run_bind_denote_call_cfg_of_nil
      (argTys := [Ty.ptr, Ty.ptr, Ty.bitvec 8, Ty.bitvec 64, Ty.bitvec 64]) (by rfl) $h])

open Lean Elab Tactic in
/-- Rebuild the frame across a two-cell write. -/
elab "frame_step₂ " nm:ident " from " pf:term " by " w:term : tactic => do
  let hcells := mkIdent (Name.mkSimple "cells")
  evalTactic (← `(tactic| have $nm:ident := ($pf).step₂ $hcells (by decide) rfl rfl $w))

open Lean Elab Tactic in
/-- `borrow_peel k from f giving f' with l giving l'` runs the `k`-th
`subborrowx`. It writes cells `2k-2` and `2k-1`, and binds the limb bound
`hx(2k-1)`, the borrow bound `hx(2k)` and the digit equation `hsum<k>`. The run
equation is consumed here and cleared, so it never reaches the context.

The three contract arguments come from: `limb_bound` for `arg1[k-1]`, whose
`LimbBounds` is inclusive at `2 ^ 51`; `decide` for the constant subtrahend; and
for the borrow carried in, the previous step's bound read back out of its cell
-- same state, so `readWord?_eq_some` on its `Wrote₂` suffices. -/
elab "borrow_peel " k:num " from " pf:ident " giving " nf:ident
    " with " pl:ident " giving " nl:ident : tactic => do
  let n := k.getNat
  let sfx := subscript n
  let st := mkIdent (Name.mkSimple "s")
  let hcells := mkIdent (Name.mkSimple "cells")
  let hq := mkIdent (Name.mkSimple "hq")
  let hqlimb := mkIdent (Name.mkSimple "hqlimb")
  let u := mkIdent (Name.mkSimple ("u" ++ sfx))
  let hrun := mkIdent (Name.mkSimple ("hrun" ++ sfx))
  let w := mkIdent (Name.mkSimple ("w" ++ sfx))
  let xlo := mkIdent (Name.mkSimple s!"x{2 * n - 1}")
  let xbo := mkIdent (Name.mkSimple s!"x{2 * n}")
  let hxlo := mkIdent (Name.mkSimple s!"hx{2 * n - 1}")
  let hxbo := mkIdent (Name.mkSimple s!"hx{2 * n}")
  let hsum := mkIdent (Name.mkSimple ("hsum" ++ sfx))
  let a := Syntax.mkNumLit (toString (2 * (n - 1)))
  let b := Syntax.mkNumLit (toString (2 * n - 1))
  let kFin := Syntax.mkNumLit (toString (n - 1))
  -- pinned: a metavariable surviving the facts phase is assigned later against
  -- the walk's goal, and every hypothesis mentioning it is updated with it
  -- the borrow carried in is the previous step's, folded to its name at the
  -- load, so the operand is an atom rather than a block slice
  let cin ← if n == 1 then `(BitVec.ofInt 8 0)
    else pure (mkIdent (Name.mkSimple s!"x{2 * (n - 1)}"))
  let xin ← if n == 1 then do
      let qq := mkIdent (Name.mkSimple "q")
      let qb := mkIdent (Name.mkSimple "qblk")
      `(BitVec.extractLsb' ($qq).offsetInBits 64 ($qb).bytes)
    else do
      let qp := mkIdent (Name.mkSimple ("qp" ++ subscript (n - 1)))
      let qb := mkIdent (Name.mkSimple ("qblk" ++ subscript (n - 1)))
      `(BitVec.extractLsb' ($qp).offsetInBits 64 ($qb).bytes)
  let yin ← if n == 1 then `(BitVec.ofInt 64 2251799813685229)
    else `(BitVec.ofInt 64 2251799813685247)
  -- the limb read, named once: it carries the operand's bound *and* restates
  -- the digit equation over `readLimb` instead of the block slice
  let qq := mkIdent (Name.mkSimple "q")
  let hqread := mkIdent (Name.mkSimple ("hqread" ++ sfx))
  let qhb := mkIdent (Name.mkSimple (if n == 1 then "hqblk" else "hqblk" ++ subscript (n - 1)))
  let qpT : Term := if n == 1 then qq else mkIdent (Name.mkSimple ("qp" ++ subscript (n - 1)))
  let hoffPf ← if n == 1 then `((by simp))
    else `(limbOffsetInBits ($hq).right (k := $kFin) (by omega) (by simp))
  evalTactic (← `(tactic| have $hqread:ident : ($xin).toNat
      = readLimb ($kFin : Fin 5) $hq :=
    limb_read $hq (($pf).fb ($qq).id ($hcells).idq) (qp := $qpT) (k := ($kFin : Fin 5)) rfl
      $hoffPf (by simp [readWord?, MemoryState.live?, $qhb:ident])))
  let hqreadBV := mkIdent (Name.mkSimple ("hqreadBV" ++ sfx))
  evalTactic (← `(tactic| have $hqreadBV:ident : $xin
      = ((readLimb ($kFin : Fin 5) $hq : ℕ) : BitVec 64) :=
    limb_readBV $hq (($pf).fb ($qq).id ($hcells).idq) (qp := $qpT) (k := ($kFin : Fin 5)) rfl
      $hoffPf (by simp [readWord?, MemoryState.live?, $qhb:ident])))
  let hxbound ← `((by rw [$hqread:ident]; exact le_trans ($hqlimb _) (by norm_num)))
  -- the borrow carried in: 0 at the head, else the previous step's bound
  let hcy ← if n == 1 then `((by decide : (1 : ℕ) ≤
        (BitVec.ofInt 8 0).toNat + (BitVec.ofInt 64 2251799813685229).toNat))
    else `((by
        have hy : (BitVec.ofInt 64 2251799813685247).toNat = 2251799813685247 := by decide
        omega))
  let hcy' ← if n == 1 then `((by decide : (BitVec.ofInt 8 0).toNat
        + (BitVec.ofInt 64 2251799813685229).toNat ≤ 2 ^ 51))
    else `((by
        have hy : (BitVec.ofInt 64 2251799813685247).toNat = 2251799813685247 := by decide
        omega))
  evalTactic (← `(tactic| obtain ⟨$u:ident, $xlo:ident, $xbo:ident, $hrun:ident,
      $hxlo:ident, $hxbo:ident, $hsum:ident, $w:ident⟩ :=
    subborrow_step (a := cellPtr $st $a) (b := cellPtr $st $b)
      (c := $cin) (x := $xin) (y := $yin)
      ($pf).wf (($hcells).ne (by decide)) (($pf).fits $a) (($pf).fits $b)
      $hxbound $hcy $hcy'))
  evalTactic (← `(tactic| frame_step₂ $nf from $pf by $w))
  evalTactic (← `(tactic| have $nl:ident :=
    ($pl).grow $hcells (c := ($kFin : Fin 5)) rfl (by decide) $w $hxlo))
  evalTactic (← `(tactic| rw [$hqread:ident] at $hsum:ident))
  let spent : Array Ident := if n == 1
    then #["hqblk", "hqlen", "qblk"].map (mkIdent ∘ Name.mkSimple)
    else #["hqblk", "hqlen", "hqp", "hqu", "qblk"].map fun b =>
      mkIdent (Name.mkSimple (b ++ subscript (n - 1)))
  evalTactic (← `(tactic| clear $hqread $pl $pf))
  -- the subtrahend is one of `p`'s limbs; `rw` rather than `simp only`, whose
  -- `Nat.reduceSub` simproc would turn `pLimb` straight back into the literal
  let yNum := Syntax.mkNumLit (if n == 1 then "2251799813685229" else "2251799813685247")
  let yIdx := Syntax.mkNumLit (if n == 1 then "0" else "1")
  evalTactic (← `(tactic| rw [show (BitVec.ofInt 64 $yNum).toNat = pLimb $yIdx from by
    simp [pLimb]] at $hsum:ident))
  if n == 1 then
    evalTactic (← `(tactic| rw [show (BitVec.ofInt 8 0).toNat = 0 from by decide,
      Nat.add_zero] at $hsum:ident))
  -- the call is matched against the slice, so it goes first; then the goal is
  -- folded to the spec's limb, which is what frees the block
  evalTactic (← `(tactic| peel_kernel_call $hrun))
  evalTactic (← `(tactic| clear $hrun))
  evalTactic (← `(tactic| simp only [$hqreadBV:ident]))
  evalTactic (← `(tactic| clear $hqreadBV $spent*))

open Lean Elab Tactic in
/-- `addback_facts j from f giving f' with l giving l'` runs the `j`-th
`addcarryx`. It writes cells `9+2j` and `10+2j`, adds fiat's `x(12+2j-2)` back
to the limb the borrow chain left in cell `2j-2`, and carries in cell
`10+2j-2`'s byte. The operands are pinned: left to unification each costs a
search of the whole valuation.

The contract arguments come from: the carried-in byte's own bound, read back out
of its cell in the state that wrote it; `Limbs` for the borrow-chain limb, which
was written several calls ago and is why the invariant is threaded at all; and
`Nat.and_le_right` for the masked constant. -/
elab "addback_facts " j:num " from " pf:ident " giving " nf:ident
    " with " pl:ident " giving " nl:ident : tactic => do
  let m := j.getNat
  let n := 6 + m
  let sfx := subscript n
  let st := mkIdent (Name.mkSimple "s")
  let hcells := mkIdent (Name.mkSimple "cells")
  let u := mkIdent (Name.mkSimple ("u" ++ sfx))
  let pu := mkIdent (Name.mkSimple ("u" ++ subscript (n - 1)))
  let hrun := mkIdent (Name.mkSimple ("hrun" ++ sfx))
  let w := mkIdent (Name.mkSimple ("w" ++ sfx))
  let bcell := 12 + 2 * (m - 1)          -- carry cell this step writes
  let acell := 11 + 2 * (m - 1)          -- limb cell this step writes
  let src := 2 * (m - 1)                 -- borrow-chain limb being added back
  let xlo := mkIdent (Name.mkSimple s!"x{bcell}")
  let xco := mkIdent (Name.mkSimple s!"x{bcell + 1}")
  let hxlo := mkIdent (Name.mkSimple s!"hx{bcell}")
  let hxco := mkIdent (Name.mkSimple s!"hx{bcell + 1}")
  let hsum := mkIdent (Name.mkSimple ("hsum" ++ sfx))
  let a := Syntax.mkNumLit (toString acell)
  let b := Syntax.mkNumLit (toString bcell)
  let srcN := Syntax.mkNumLit (toString src)
  let srcBlk := mkIdent (Name.mkSimple ("c" ++ subscript src ++ "blk"))
  let srcHBlk := mkIdent (Name.mkSimple ("hc" ++ subscript src ++ "blk"))
  -- the carry in is the previous step's, folded to its name at the load
  let cin ← if m == 1 then `(BitVec.ofInt 8 0)
    else pure (mkIdent (Name.mkSimple s!"x{bcell - 1}"))
  let yin := mkIdent (Name.mkSimple (if m == 1 then "mask₀" else "mask₁"))
  let hmask := mkIdent (Name.mkSimple (if m == 1 then "hmask₀" else "hmask₁"))
  let hc ← if m == 1 then `((by decide : (BitVec.ofInt 8 0).toNat ≤ 1))
    else `((by omega))
  -- the limb, out of the invariant
  let kFin := Syntax.mkNumLit (toString (m - 1))
  let hx ← `(($pl) ($kFin : Fin 5) (by omega)
      (BitVec.extractLsb' (cellPtr $st $srcN).offsetInBits 64 ($srcBlk).bytes)
      (show readWord? (cellPtr $st $srcN) 64 ($pu).mem
          = some (BitVec.extractLsb' (cellPtr $st $srcN).offsetInBits 64 ($srcBlk).bytes) from by
        simp [readWord?, MemoryState.live?, $srcHBlk:ident]))
  -- the masked constant is below its mask, which is below `2 ^ 51`
  let hy ← `((by
      rw [$hmask:ident]
      split <;> norm_num [pLimb]))
  evalTactic (← `(tactic| obtain ⟨$u:ident, $xlo:ident, $xco:ident, $hrun:ident,
      $hxlo:ident, $hxco:ident, $hsum:ident, $w:ident⟩ :=
    addcarry_step (a := cellPtr $st $a) (b := cellPtr $st $b)
      (c := $cin)
      (x := BitVec.extractLsb' (cellPtr $st $srcN).offsetInBits 64 ($srcBlk).bytes)
      (y := $yin)
      ($pf).wf (($hcells).ne (by decide)) (($pf).fits $a) (($pf).fits $b)
      $hc $hx $hy))
  evalTactic (← `(tactic| frame_step₂ $nf from $pf by $w))
  evalTactic (← `(tactic| have $nl:ident := ($pl).keep₂ $hcells (by decide) (by decide) $w))
  -- The limb added back is what subborrow `m` wrote into cell `2m-2`; the five
  -- calls since then wrote other cells, so its value survives and the digit
  -- equation can be stated over `x(2m-1)` rather than over a block slice.
  let srcX := mkIdent (Name.mkSimple s!"x{2 * m - 1}")
  let srcW := mkIdent (Name.mkSimple ("w" ++ subscript m))
  let srcU := mkIdent (Name.mkSimple ("u" ++ subscript m))
  let hload := mkIdent (Name.mkSimple ("hload" ++ subscript src))
  let mut chain : Array Term := #[]
  for j in [m + 1 : n] do
    let wj := mkIdent (Name.mkSimple ("w" ++ subscript j))
    chain := chain.push (← if j == 6
      then `(($wj).survive? 64 (($hcells).ne (by decide)))
      else `(($wj).survive? 64 (($hcells).ne (by decide)) (($hcells).ne (by decide))))
  -- outermost state first: each `rw` peels one call off the left-hand side
  chain := chain.reverse
  evalTactic (← `(tactic| have $hload:ident :
      BitVec.extractLsb' (cellPtr $st $srcN).offsetInBits 64 ($srcBlk).bytes = $srcX := by
    have hread : readWord? (cellPtr $st $srcN) 64 ($pu).mem
        = some (BitVec.extractLsb' (cellPtr $st $srcN).offsetInBits 64 ($srcBlk).bytes) := by
      simp [readWord?, MemoryState.live?, $srcHBlk:ident]
    have hchain : readWord? (cellPtr $st $srcN) 64 ($pu).mem
        = readWord? (cellPtr $st $srcN) 64 ($srcU).mem := by
      rw [$[$chain:term],*]
    simpa using (hread.symm.trans hchain).trans
      (readWord?_eq_some ($srcW).fita ($srcW).vala)))
  evalTactic (← `(tactic| rw [$hload:ident] at $hsum:ident))
  -- The call is matched against the slice, so it goes first; then the goal is
  -- folded too, which is what frees the block.
  evalTactic (← `(tactic| peel_kernel_call $hrun))
  evalTactic (← `(tactic| clear $hrun))
  evalTactic (← `(tactic| simp only [$hload:ident]))
  let srcLen := mkIdent (Name.mkSimple ("hc" ++ subscript src ++ "len"))
  let srcCell := mkIdent (Name.mkSimple ("hcell" ++ subscript src))
  evalTactic (← `(tactic| clear $hload $srcHBlk $srcLen $srcBlk $srcCell $pl $pf))

open Lean Elab Tactic in
/-! ### PLAN §2: the borrow chain and the add-back canonicalise

Over the limb sums the two chains telescope, and what is left is a case on the
final borrow. Stated over abstract limbs so the proofs run in an empty context. -/

/-- Subtracting `p` digit-wise: every borrow cancels against the next digit's
carry-in except the last, which surfaces at `2 ^ 255`. -/
theorem borrow_tel {L0 L1 L2 L3 L4 y0 y1 y2 y3 y4 b1 b2 b3 b4 b5 : ℕ}
    (s0 : y0 + pLimb 0 = L0 + 2^51 * b1)
    (s1 : y1 + b1 + pLimb 1 = L1 + 2^51 * b2)
    (s2 : y2 + b2 + pLimb 1 = L2 + 2^51 * b3)
    (s3 : y3 + b3 + pLimb 1 = L3 + 2^51 * b4)
    (s4 : y4 + b4 + pLimb 1 = L4 + 2^51 * b5) :
    y0 + 2^51 * y1 + 2^102 * y2 + 2^153 * y3 + 2^204 * y4 + (2^255 - 19)
      = L0 + 2^51 * L1 + 2^102 * L2 + 2^153 * L3 + 2^204 * L4 + 2^255 * b5 := by
  simp only [pLimb, if_true, show (1 : ℕ) = 0 ↔ False from by decide, if_false] at *
  zify [show 19 ≤ 2^51 from by norm_num, show 1 ≤ 2^51 from by norm_num,
    show 19 ≤ 2^255 from by norm_num] at *
  linear_combination s0 + 2^51 * s1 + 2^102 * s2 + 2^153 * s3 + 2^204 * s4

/-- The add-back telescopes the same way; `c5` is its discarded last carry and
`m0`, `m1` the mask's value on the low limb and the four above it. -/
theorem addback_tel {y0 y1 y2 y3 y4 m0 m1 r0 r1 r2 r3 r4 c1 c2 c3 c4 c5 : ℕ}
    (a0 : r0 + 2^51 * c1 = y0 + m0)
    (a1 : r1 + 2^51 * c2 = c1 + y1 + m1)
    (a2 : r2 + 2^51 * c3 = c2 + y2 + m1)
    (a3 : r3 + 2^51 * c4 = c3 + y3 + m1)
    (a4 : r4 + 2^51 * c5 = c4 + y4 + m1) :
    r0 + 2^51 * r1 + 2^102 * r2 + 2^153 * r3 + 2^204 * r4 + 2^255 * c5
      = y0 + 2^51 * y1 + 2^102 * y2 + 2^153 * y3 + 2^204 * y4
        + (m0 + m1 * (2^51 + 2^102 + 2^153 + 2^204)) := by
  zify at *
  linear_combination a0 + 2^51 * a1 + 2^102 * a2 + 2^153 * a3 + 2^204 * a4

/-- What the telescopings leave: with `V` the input, `Y` the difference and `R`
the result, `R` is `V` reduced. Below `p` the borrow is set and `p` is added
back (forcing the last carry); at or above it neither happens. -/
theorem canon {V Y R b5 c5 : ℕ} (hV : V < 2^256 - 38) (hY : Y < 2^255) (hR : R < 2^255)
    (hb5 : b5 ≤ 1)
    (hbor : Y + (2^255 - 19) = V + 2^255 * b5)
    (hadd : R + 2^255 * c5 = Y + (if b5 = 0 then 0 else 2^255 - 19)) :
    R = V % (2^255 - 19) := by
  obtain rfl | rfl : b5 = 0 ∨ b5 = 1 := by omega
  · simp only [if_true] at hadd; omega
  · simp only [show (1 : ℕ) = 0 ↔ False from by decide, if_false] at hadd; omega

set_option maxRecDepth 8000 in
/-- The spec's value is the limb sum reduced: `decodeFieldElem` is that sum cast
into `ZMod p`, and `ZMod.val` of a cast is `% p`. -/
theorem readFieldElem_val {m : MemoryState} {q : Pointer} (hq : IsFieldElemPtr m q) :
    (readFieldElem hq).val
      = (readLimb 0 hq + 2^51 * readLimb 1 hq + 2^102 * readLimb 2 hq + 2^153 * readLimb 3 hq
          + 2^204 * readLimb 4 hq) % (2^255 - 19) := by
  rw [readFieldElem_eq_decode]
  simp only [decodeFieldElem, Fin.isValue]
  rw [← ZMod.val_natCast]
  simp only [show 51 * Fin.toNat (0 : Fin 5) = 0 from rfl, show 51 * Fin.toNat (1 : Fin 5) = 51 from rfl,
    show 51 * Fin.toNat (2 : Fin 5) = 102 from rfl, show 51 * Fin.toNat (3 : Fin 5) = 153 from rfl,
    show 51 * Fin.toNat (4 : Fin 5) = 204 from rfl]
  congr 1
  simp only [Nat.cast_add, Nat.cast_mul, pow_zero, mul_one]
  ring

/-! The buffer-shaping lemmas. All four are closed facts about `BitVec` and
`MemoryState`; stated inside the walk their `omega`s and `simp`s would each
scan its whole context. -/

theorem stickBack {v w : ℕ} {d : BitVec v} :
    (BitVec.setWidth 8 (d >>> (w : ℕ)) ++ BitVec.setWidth w d)
      = BitVec.setWidth (8 + w) d := by
  apply BitVec.eq_of_getLsbD_eq
  intro i
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight]
  split <;> rename_i h <;> intro hi
  · simp [h, hi]
  · rw [show w + (i - w) = i by omega]
    simp [hi, show i - w < 8 by omega]

theorem merge {n w' : ℕ} {u m : GlobalState} {p : Pointer} {off : BitVec 64}
    {acc : BitVec n} {b : BitVec w'}
    (h : m ≈ { u with mem := u.mem.splice p acc })
    (hoff : (p.withOffset off).offsetInBits = p.offsetInBits + n) :
    ({ m with mem := m.mem.splice (p.withOffset off) b } : GlobalState)
      ≈ { u with mem := u.mem.splice p (b ++ acc) } :=
  GlobalState.Equiv.trans (splice_equiv (p := p.withOffset off) (x := b) h)
    (splice_splice_append_equiv (s := u) (p := p) acc b hoff)

theorem step {v w : ℕ} {u m : GlobalState} {p : Pointer} {off : BitVec 64} {d : BitVec v}
    (h : m ≈ { u with mem := u.mem.splice p (BitVec.setWidth w d) })
    (hoff : (p.withOffset off).offsetInBits = p.offsetInBits + w) :
    ({ m with mem := m.mem.splice (p.withOffset off) (BitVec.setWidth 8 (d >>> (w : ℕ))) }
        : GlobalState)
      ≈ { u with mem := u.mem.splice p (BitVec.setWidth (8 + w) d) } := by
  have hcat := merge (b := BitVec.setWidth 8 (d >>> (w : ℕ))) h hoff
  rwa [stickBack] at hcat

theorem hpack {a b : BitVec 64} :
    BitVec.setWidth 48 b ++ BitVec.setWidth 48 a
      = BitVec.ofNat 96 (a.toNat % 2 ^ 48 + 2 ^ 48 * (b.toNat % 2 ^ 48)) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_append,
    ← Nat.shiftLeft_add_eq_or_of_lt (by simp only [BitVec.toNat_setWidth]; omega),
    Nat.shiftLeft_eq, BitVec.toNat_ofNat]
  simp only [BitVec.toNat_setWidth]
  omega

/-- `++` as a number: the left operand sits above the right one. Exact, since
the concatenation is as wide as both together. -/
theorem packAt {n m : ℕ} {a : BitVec n} {b : BitVec m} :
    b ++ a = BitVec.ofNat (m + n) (a.toNat + 2 ^ n * b.toNat) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt a.isLt, Nat.shiftLeft_eq,
    BitVec.toNat_ofNat]
  have h1 : a.toNat + 2 ^ n * b.toNat < 2 ^ n * (b.toNat + 1) := by
    rw [Nat.mul_succ]; have := a.isLt; omega
  have h2 : 2 ^ n * (b.toNat + 1) ≤ 2 ^ m * 2 ^ n := by
    rw [Nat.mul_comm (2 ^ m)]; exact Nat.mul_le_mul_left _ (Nat.succ_le_of_lt b.isLt)
  rw [Nat.mod_eq_of_lt (by rw [Nat.pow_add]; exact Nat.lt_of_lt_of_le h1 h2),
    Nat.mul_comm, Nat.add_comm]

/-! A group's bytes telescope onto the bytes before them: the accumulator they
were cut from holds exactly the earlier bytes' quotient, plus the next limb. One
instance per group boundary, since `omega` needs the exponents literal. -/

theorem join48 {a c : ℕ} :
    a % 2 ^ 48 + 2 ^ 48 * ((a / 2 ^ 48 + c) % 2 ^ 48) = (a + 2 ^ 48 * c) % 2 ^ 96 := by omega
theorem join96 {a c : ℕ} :
    a % 2 ^ 96 + 2 ^ 96 * ((a / 2 ^ 96 + c) % 2 ^ 56) = (a + 2 ^ 96 * c) % 2 ^ 152 := by omega
theorem join152 {a c : ℕ} :
    a % 2 ^ 152 + 2 ^ 152 * ((a / 2 ^ 152 + c) % 2 ^ 48) = (a + 2 ^ 152 * c) % 2 ^ 200 := by omega
theorem join200 {a c : ℕ} :
    a % 2 ^ 200 + 2 ^ 200 * ((a / 2 ^ 200 + c) % 2 ^ 56) = (a + 2 ^ 200 * c) % 2 ^ 256 := by omega

/-! ... and each accumulator's quotient is the running total's, so the chain of
`/ 2 ^ 48`, `/ 2 ^ 56` steps collapses to one division by the bytes so far. -/

theorem divChain48 {a b : ℕ} : (a / 2 ^ 48 + b) / 2 ^ 48 = (a + 2 ^ 48 * b) / 2 ^ 96 := by omega
theorem divChain96 {a b : ℕ} : (a / 2 ^ 96 + b) / 2 ^ 56 = (a + 2 ^ 96 * b) / 2 ^ 152 := by omega
theorem divChain152 {a b : ℕ} : (a / 2 ^ 152 + b) / 2 ^ 48 = (a + 2 ^ 152 * b) / 2 ^ 200 := by omega

/-- One accumulator step: the byte the previous group left over, above the next
limb already scaled to its boundary. `ha` is what makes the region's `&&& 255`
a no-op -- the shifted-out part is at most a byte wide. Nothing needs to be said
about wrapping: both sides reduce mod `2 ^ 64` the same way. -/
theorem accStep {a b : BitVec 64} (ha : a.toNat < 2 ^ 56) :
    (a >>> 48#64 &&& 255#64) + b = BitVec.ofNat 64 (a.toNat / 2 ^ 48 + b.toNat) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_and, BitVec.toNat_ushiftRight,
    BitVec.ushiftRight_eq', BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
    Nat.reducePow, Nat.reduceMod]
  rw [show (255 : ℕ) = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  omega

/-- The seven-byte variant: the group leaves a full byte, so the region emits no
mask and the shift is by 56. -/
theorem accStep' {a b : BitVec 64} :
    a >>> 56#64 + b = BitVec.ofNat 64 (a.toNat / 2 ^ 56 + b.toNat) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ushiftRight, BitVec.ushiftRight_eq',
    BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Nat.reducePow, Nat.reduceMod]

/-- Byte `k` of the buffer, as the region computes it. Limb `j` starts at bit
`51 * j`, hence at byte `51 * j / 8` -- the boundaries 0, 6, 12, 19, 25 -- and
its accumulator carries the `51 * j % 8` bits the previous limb left over,
which is where the shifts 0, 3, 6, 1, 4 in the region come from. -/
def storedByte (x12 x38 x51 x66 x79 : BitVec 64) (k : Nat) : BitVec 8 :=
  if k < 51 * 1 / 8 then BitVec.truncate 8 (x12 >>> BitVec.ofNat 64 (8 * k))
  else if k < 51 * 2 / 8 then
    BitVec.truncate 8 (x38 >>> BitVec.ofNat 64 (8 * (k - 51 * 1 / 8)))
  else if k < 51 * 3 / 8 then
    BitVec.truncate 8 (x51 >>> BitVec.ofNat 64 (8 * (k - 51 * 2 / 8)))
  else if k < 51 * 4 / 8 then
    BitVec.truncate 8 (x66 >>> BitVec.ofNat 64 (8 * (k - 51 * 3 / 8)))
  else BitVec.truncate 8 (x79 >>> BitVec.ofNat 64 (8 * (k - 51 * 4 / 8)))

/-- Byte `k` of the buffer is the value of `%(byteSrc k)`: the region emits
bytes 0-5 out of `x12`, 6-11 out of `x38`, 12-18 out of `x51`, 19-24 out of
`x66` and 25-31 out of `x79`, two instructions per byte. -/
def byteSrc (k : Nat) : Nat :=
  if k < 6 then 98 + 2 * k
  else if k < 12 then 112 + 2 * (k - 6)
  else if k < 19 then 126 + 2 * (k - 12)
  else if k < 25 then 141 + 2 * (k - 19)
  else 155 + 2 * (k - 25)

/-- `peel_store` into a state that is *already named*. `hnm : nm = …` bridges
to the splice, and the store's own rewrite then installs the opaque `nm` in the
goal — so unlike `set`-after-the-fact, nothing has to be abstracted back out of
it, and the name needs no `clear_value`. Byte stores only. Staged; belongs
beside `peel_store`. -/
macro "peel_store_as " x:term ", " p:term ", " hp:term ", " st:term ", "
    nm:term ", " hnm:term : tactic =>
  `(tactic|
    (try simp only [bind_assoc]
     rw [BlockCom.run_bind_denote_var_of_nil (s' := $nm)
       (by rw [$hnm:term]
           simp only [Expr.denoteOp, Ctxt.Valuation.singleton, simp_denote, simp_sllvm]
           rw [run_liftM (run_store (t := .bitvec (.concrete 8)) (x := PoisonOr.value $x) rfl
             (show Fits (($st).mem) $p 8 from Fits.mono $hp (by omega)))]
           rfl)]))

open Lean Elab Tactic Meta in
/-- `clear_subscript lo hi p q ...` clears `p<lo>` .. `p<hi>` for every prefix
given, in `₀`-subscript form. Names absent from the context are skipped, so a
range may overshoot one family. Clearing runs newest-first, which is dependency
order for anything these tactics introduce (`obtain ⟨m, hm⟩` puts `hm` after
`m`), so the prefixes can be listed in any order -- but a family and what
mentions it must be cleared by the *same* call, since a name that fails is not
retried. -/
elab "clear_subscript " lo:num hi:num ps:(ppSpace colGt ident)+ : tactic => do
  let g ← getMainGoal
  let fvars ← g.withContext do
    let lctx ← getLCtx
    let mut acc : Array (Nat × FVarId) := #[]
    for p in ps do
      for k in [lo.getNat : hi.getNat + 1] do
        let n := Name.mkSimple (p.getId.eraseMacroScopes.toString ++ subscript k)
        if let some d := lctx.findFromUserName? n then acc := acc.push (d.index, d.fvarId)
    pure (acc.qsort (fun a b => a.1 > b.1) |>.map Prod.snd)
  replaceMainGoal [← g.tryClearMany fvars]

open Lean Elab Tactic Meta in
/-- `store_bytes lo hi, o, ho, u` runs bytes `lo` to `hi - 1` of the store chain
the region ends in: byte `k` at `o + k`, each but byte 0 behind its own
`getelementptr`. Values are read off their `hv` equations rather than written
out. Leaves the buffer states as `m<k>` with defining equations `hm<k>`, the
gep'd pointers as `o<k>`, and `g<k> : Fits m<k>.mem o (32 * 8)`, since a store
changes no block's size.

`u` is the state before byte `lo` and `ho` its `Fits`, so a run picks up exactly
where the previous one's `m<lo>`/`g<lo>` left off. Costs about 4s per store,
flat. Staged here; belongs beside `store_limbs`. -/
elab "store_bytes " lo:num ppSpace hi:num ", " p:ident ", " hp:term ", " st:ident : tactic => do
  let pbase := p.getId.eraseMacroScopes.toString
  let loN := lo.getNat
  let hiN := hi.getNat
  let gOf (k : Nat) : Ident := mkIdent (Name.mkSimple s!"g{subscript k}")
  let mOf (k : Nat) : Term := mkIdent (Name.mkSimple s!"m{subscript k}")
  let hmOf (k : Nat) : Ident := mkIdent (Name.mkSimple s!"hm{subscript k}")
  -- One rewrite for all the values instead of a `subst` per store: each pass
  -- over this goal is expensive and all but one of them were redundant.
  let hvs : Array Term := (List.range (hiN - loN)).toArray.map fun j =>
    mkIdent (Name.mkSimple s!"hv{byteSrc (loN + j)}")
  evalTactic (← `(tactic| simp only [$[$hvs:term],*]))
  for k in [loN:hiN] do
    let i := byteSrc k
    let hv := mkIdent (Name.mkSimple s!"hv{i}")
    let val ← (← getMainGoal).withContext do
      let some d := (← getLCtx).findFromUserName? hv.getId
        | throwError "store_bytes: no hv{i} for byte {k}"
      let some (_, _, rhs) := (← instantiateMVars d.type).eq?
        | throwError "store_bytes: hv{i} is not an equation"
      unless rhs.isAppOfArity ``PoisonOr.value 2 do
        throwError "store_bytes: %{i} did not reduce to a value"
      Term.exprToSyntax rhs.appArg!
    -- the state this store lands in, and the pointer and `Fits` it needs
    let cur : Term := if k == loN then st else mOf k
    let nxt := mkIdent (Name.mkSimple s!"m{subscript (k+1)}")
    let hnxt := hmOf (k+1)
    let mut ptr : Term := p
    let mut ptrFits : Term := hp
    if k != 0 then
      let kLit := Syntax.mkNumLit (toString k)
      -- the run's first state arrives with its `Fits` in hand; the rest derive
      -- theirs from the store that produced them
      let mut gk : Term := hp
      if k != loN then
        let gkId := gOf k
        let prevFits : Term := if k == loN + 1 then hp else ⟨(gOf (k-1)).raw⟩
        evalTactic (← `(tactic| have $gkId:ident : Fits ($cur).mem $p (32 * 8) := by
          rw [$(hmOf k):ident]; exact fits_splice $prevFits))
        gk := ⟨gkId.raw⟩
      evalTactic (← `(tactic| peel_gep_byte $kLit, $p, $gk, $cur, $p))
      ptr := mkIdent (Name.mkSimple (pbase ++ subscript k))
      ptrFits := mkIdent (Name.mkSimple ("h" ++ pbase ++ subscript k))
    -- name the result first: `obtain` never touches the goal, and the store's
    -- rewrite then puts the opaque name there directly
    evalTactic (← `(tactic| obtain ⟨$nxt:ident, $hnxt:ident⟩ :
      ∃ z, z = { $cur with mem := ($cur).mem.splice $ptr $val } := ⟨_, rfl⟩))
    evalTactic (← `(tactic| peel_store_as $val, $ptr, $ptrFits, $cur, $nxt, $hnxt))
  evalTactic (← `(tactic| clear $hvs*))
  -- the final state's `Fits`, so the next run can start from it
  if hiN > loN then
    let prevFits : Term := if hiN - 1 == loN then hp else ⟨(gOf (hiN - 1)).raw⟩
    evalTactic (← `(tactic| have $(gOf hiN):ident : Fits ($(mOf hiN)).mem $p (32 * 8) := by
      rw [$(hmOf hiN):ident]; exact fits_splice $prevFits))

end ToBytes

open ToBytes in
set_option linter.all false in
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 2000 in
theorem fiat_25519_to_bytes_conforms (o q : Pointer) (s : GlobalState)
    (hs : s.WF) (ho : IsByteBufPtr s.mem o) (hq : IsFieldElemPtr s.mem q)
    (hqlimb : LimbBounds hq) :
    fiat_25519_to_bytes_spec o q s ho hq := by
  simp only [fiat_25519_to_bytes_spec]
  -- Facts first, while the goal is still one line. Every `obtain` below
  -- reverts the goal to case on its hypothesis; run against the walk's goal
  -- each costs over a second, and there are more than thirty.
  obtain ⟨cells, frame⟩ := cells_frame s hs ho.left hq.left
  obtain ⟨qblk, hqblk, hqlen⟩ :=
    id (fits_of_live?_eq (frame.fb q.id cells.idq) hq.left)
  have l₀ : Limbs (cellPtr s) (frameState s) 0 := Limbs.nil

  -- The buffer is the spec's own claim, so it is supplied here; the final
  -- state is not, and comes at the end from a name the walk introduces.
  refine ⟨BitVec.ofNat 256 (readFieldElem hq).val, readBuf_splice (m := s.mem) _ ho, ?_⟩
  refine run_runFunction' _ ?_
  simp only [Cfg.denote]
  -- %0-%41: the constants, substituted away
  denote_step_all v 41
  eval_consts v 0 41
  -- %42-%62: the 21 scratch cells
  peel_alloca_chain s, cw, 21
  fold_cells s, cw, cellPtr, 21
  -- The 21 `lifetime.start` markers move neither state nor valuation.
  iterate 21 peel_lifetime
  -- %63: `arg1[0]`, the first borrow operand
  peel_load (.bitvec (.concrete 64)), qblk, q, hqblk, (s.allocaChain cw 21)
  -- Each step is one line: `borrow_peel` pins the operands, discharges the
  -- contract and runs the call. `cell_facts`/`limb_facts` after it name the
  -- blocks this step's loads and the *next* step's operands are read out of.
  borrow_peel 1 from frame giving f₁ with l₀ giving l₁
  cell_facts 8, 1, u₁, f₁
  limb_facts 1, u₁, f₁
  peel_cell 8, 1, u₁
  -- cell 1 is subborrow 1's borrow byte, read in the state that wrote it
  have hload₁ : BitVec.extractLsb' (cellPtr s 1).offsetInBits 8 c₁blk.bytes
      = x2 := by
    have hread : readWord? (cellPtr s 1) 8 u₁.mem
        = some (BitVec.extractLsb' (cellPtr s 1).offsetInBits 8 c₁blk.bytes) := by
      simp [readWord?, MemoryState.live?, hc₁blk]
    simpa using hread.symm.trans (readWord?_eq_some w₁.fitb w₁.valb)
  simp only [hload₁]
  clear hload₁ hc₁blk hc₁len c₁blk hcell₁
  limb_peel 1, u₁
  borrow_peel 2 from f₁ giving f₂ with l₁ giving l₂
  cell_facts 8, 3, u₂, f₂
  limb_facts 2, u₂, f₂
  peel_cell 8, 3, u₂
  -- cell 3 is subborrow 2's borrow byte, read in the state that wrote it
  have hload₃ : BitVec.extractLsb' (cellPtr s 3).offsetInBits 8 c₃blk.bytes
      = x4 := by
    have hread : readWord? (cellPtr s 3) 8 u₂.mem
        = some (BitVec.extractLsb' (cellPtr s 3).offsetInBits 8 c₃blk.bytes) := by
      simp [readWord?, MemoryState.live?, hc₃blk]
    simpa using hread.symm.trans (readWord?_eq_some w₂.fitb w₂.valb)
  simp only [hload₃]
  clear hload₃ hc₃blk hc₃len c₃blk hcell₃
  limb_peel 2, u₂
  borrow_peel 3 from f₂ giving f₃ with l₂ giving l₃
  cell_facts 8, 5, u₃, f₃
  limb_facts 3, u₃, f₃
  peel_cell 8, 5, u₃
  -- cell 5 is subborrow 3's borrow byte, read in the state that wrote it
  have hload₅ : BitVec.extractLsb' (cellPtr s 5).offsetInBits 8 c₅blk.bytes
      = x6 := by
    have hread : readWord? (cellPtr s 5) 8 u₃.mem
        = some (BitVec.extractLsb' (cellPtr s 5).offsetInBits 8 c₅blk.bytes) := by
      simp [readWord?, MemoryState.live?, hc₅blk]
    simpa using hread.symm.trans (readWord?_eq_some w₃.fitb w₃.valb)
  simp only [hload₅]
  clear hload₅ hc₅blk hc₅len c₅blk hcell₅
  limb_peel 3, u₃
  borrow_peel 4 from f₃ giving f₄ with l₃ giving l₄
  cell_facts 8, 7, u₄, f₄
  limb_facts 4, u₄, f₄
  peel_cell 8, 7, u₄
  -- cell 7 is subborrow 4's borrow byte, read in the state that wrote it
  have hload₇ : BitVec.extractLsb' (cellPtr s 7).offsetInBits 8 c₇blk.bytes
      = x8 := by
    have hread : readWord? (cellPtr s 7) 8 u₄.mem
        = some (BitVec.extractLsb' (cellPtr s 7).offsetInBits 8 c₇blk.bytes) := by
      simp [readWord?, MemoryState.live?, hc₇blk]
    simpa using hread.symm.trans (readWord?_eq_some w₄.fitb w₄.valb)
  simp only [hload₇]
  clear hload₇ hc₇blk hc₇len c₇blk hcell₇
  limb_peel 4, u₄
  borrow_peel 5 from f₄ giving f₅ with l₄ giving l₅
  cell_facts 8, 9, u₅, f₅
  peel_cell 8, 9, u₅
  -- cell 9 is subborrow 5's borrow byte, `x10`: the condition the `cmovznz`
  -- selects on, and read back in the state that wrote it
  have hload₉ : BitVec.extractLsb' (cellPtr s 9).offsetInBits 8 c₉blk.bytes = x10 := by
    have hread : readWord? (cellPtr s 9) 8 u₅.mem
        = some (BitVec.extractLsb' (cellPtr s 9).offsetInBits 8 c₉blk.bytes) := by
      simp [readWord?, MemoryState.live?, hc₉blk]
    simpa using hread.symm.trans (readWord?_eq_some w₅.fitb w₅.valb)
  simp only [hload₉]
  clear hload₉ hc₉blk hc₉len c₉blk hcell₉
  obtain ⟨u₆, x11, hrun₆, hx11, w₆⟩ := cmovznz_step (a := cellPtr s 10) f₅.wf (f₅.fits 10)
  have f₆ := f₅.step₁ cells rfl w₆
  have l₆ := l₅.keep₁ cells (by decide) w₆
  peel_call_nil hrun₆
  clear hrun₆ l₅ f₅
  cell_facts 64, 0, u₆, f₆
  cell_facts 64, 10, u₆, f₆
  peel_cell 64, 0, u₆
  peel_cell 64, 10, u₆
  -- cell 10 is the `cmovznz` output, read back in the very state that wrote it
  have hload₁₀ : BitVec.extractLsb' (cellPtr s 10).offsetInBits 64 c₁₀blk.bytes = x11 := by
    have hread : readWord? (cellPtr s 10) 64 u₆.mem
        = some (BitVec.extractLsb' (cellPtr s 10).offsetInBits 64 c₁₀blk.bytes) := by
      simp [readWord?, MemoryState.live?, hc₁₀blk]
    simpa using hread.symm.trans (readWord?_eq_some w₆.fit w₆.val)
  simp only [hload₁₀]
  clear hload₁₀ hc₁₀blk hc₁₀len c₁₀blk hcell₁₀
  -- `%79` and `%82`: `x11` against `p`'s low and upper limbs, named before the
  -- instructions that build them so the add-back operands can be pinned.
  obtain ⟨mask₀, hmask₀⟩ : ∃ z, z = if x10 = 0#8 then 0#64 else BitVec.ofNat 64 (pLimb 0) :=
    ⟨_, rfl⟩
  obtain ⟨mask₁, hmask₁⟩ : ∃ z, z = if x10 = 0#8 then 0#64 else BitVec.ofNat 64 (pLimb 1) :=
    ⟨_, rfl⟩
  -- %79: the mask meets `p`'s low limb
  denote_step_all v 79
  denote_eval v 79 79
  eval_llvm 79 [show x11 &&& 2251799813685229#64 = mask₀ from by
    rw [hmask₀, hx11]; split <;> decide]
  subst hv79
  addback_facts 1 from f₆ giving f₇ with l₆ giving l₇
  cell_facts 8, 12, u₇, f₇
  cell_facts 64, 2, u₇, f₇
  peel_cell 8, 12, u₇
  -- cell 12 is add-back 1's carry byte, read in the state that wrote it
  have hload₁₂ : BitVec.extractLsb' (cellPtr s 12).offsetInBits 8 c₁₂blk.bytes
      = x13 := by
    have hread : readWord? (cellPtr s 12) 8 u₇.mem
        = some (BitVec.extractLsb' (cellPtr s 12).offsetInBits 8 c₁₂blk.bytes) := by
      simp [readWord?, MemoryState.live?, hc₁₂blk]
    simpa using hread.symm.trans (readWord?_eq_some w₇.fitb w₇.valb)
  simp only [hload₁₂]
  clear hload₁₂ hc₁₂blk hc₁₂len c₁₂blk hcell₁₂
  peel_cell 64, 2, u₇
  -- %82: the mask meets `p`'s upper limbs, shared by the last four steps
  denote_step_all v 82
  denote_eval v 82 82
  eval_llvm 82 [show x11 &&& 2251799813685247#64 = mask₁ from by
    rw [hmask₁, hx11]; split <;> decide]
  subst hv82
  addback_facts 2 from f₇ giving f₈ with l₇ giving l₈
  cell_facts 8, 14, u₈, f₈
  cell_facts 64, 4, u₈, f₈
  peel_cell 8, 14, u₈
  -- cell 14 is add-back 2's carry byte, read in the state that wrote it
  have hload₁₄ : BitVec.extractLsb' (cellPtr s 14).offsetInBits 8 c₁₄blk.bytes
      = x15 := by
    have hread : readWord? (cellPtr s 14) 8 u₈.mem
        = some (BitVec.extractLsb' (cellPtr s 14).offsetInBits 8 c₁₄blk.bytes) := by
      simp [readWord?, MemoryState.live?, hc₁₄blk]
    simpa using hread.symm.trans (readWord?_eq_some w₈.fitb w₈.valb)
  simp only [hload₁₄]
  clear hload₁₄ hc₁₄blk hc₁₄len c₁₄blk hcell₁₄
  peel_cell 64, 4, u₈
  addback_facts 3 from f₈ giving f₉ with l₈ giving l₉
  cell_facts 8, 16, u₉, f₉
  cell_facts 64, 6, u₉, f₉
  peel_cell 8, 16, u₉
  -- cell 16 is add-back 3's carry byte, read in the state that wrote it
  have hload₁₆ : BitVec.extractLsb' (cellPtr s 16).offsetInBits 8 c₁₆blk.bytes
      = x17 := by
    have hread : readWord? (cellPtr s 16) 8 u₉.mem
        = some (BitVec.extractLsb' (cellPtr s 16).offsetInBits 8 c₁₆blk.bytes) := by
      simp [readWord?, MemoryState.live?, hc₁₆blk]
    simpa using hread.symm.trans (readWord?_eq_some w₉.fitb w₉.valb)
  simp only [hload₁₆]
  clear hload₁₆ hc₁₆blk hc₁₆len c₁₆blk hcell₁₆
  peel_cell 64, 6, u₉
  addback_facts 4 from f₉ giving f₁₀ with l₉ giving l₁₀
  cell_facts 8, 18, u₁₀, f₁₀
  cell_facts 64, 8, u₁₀, f₁₀
  peel_cell 8, 18, u₁₀
  -- cell 18 is add-back 4's carry byte, read in the state that wrote it
  have hload₁₈ : BitVec.extractLsb' (cellPtr s 18).offsetInBits 8 c₁₈blk.bytes
      = x19 := by
    have hread : readWord? (cellPtr s 18) 8 u₁₀.mem
        = some (BitVec.extractLsb' (cellPtr s 18).offsetInBits 8 c₁₈blk.bytes) := by
      simp [readWord?, MemoryState.live?, hc₁₈blk]
    simpa using hread.symm.trans (readWord?_eq_some w₁₀.fitb w₁₀.valb)
  simp only [hload₁₈]
  clear hload₁₈ hc₁₈blk hc₁₈len c₁₈blk hcell₁₈
  peel_cell 64, 8, u₁₀
  addback_facts 5 from f₁₀ giving f₁₁ with l₁₀ giving l₁₁
  -- %89-%97: the five reduced limbs, each shifted into the position its bytes
  -- occupy. fiat's `x22`-`x25`; `x20` needs none.
  cell_facts 64, 19, u₁₁, f₁₁
  peel_cell 64, 19, u₁₁
  -- cell 19 holds add-back 5's limb, fiat's `x20`
  have hload₁₉ : BitVec.extractLsb' (cellPtr s 19).offsetInBits 64 c₁₉blk.bytes
      = x20 := by
    have hread : readWord? (cellPtr s 19) 64 u₁₁.mem
        = some (BitVec.extractLsb' (cellPtr s 19).offsetInBits 64 c₁₉blk.bytes) := by
      simp [readWord?, MemoryState.live?, hc₁₉blk]
    simpa using hread.symm.trans (readWord?_eq_some w₁₁.fita w₁₁.vala)
  simp only [hload₁₉]
  clear hload₁₉ hc₁₉blk hc₁₉len c₁₉blk hcell₁₉
  obtain ⟨x22, hx22⟩ : ∃ z, z = BitVec.ofNat 64 (16 * x20.toNat) := ⟨_, rfl⟩
  denote_step_all v 90
  denote_eval v 90 90
  eval_llvm 90 [show x20 <<< 4#64 = x22 from by
    rw [hx22]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.shiftLeft_eq', BitVec.toNat_shiftLeft, BitVec.toNat_ofNat,
      Nat.shiftLeft_eq, Nat.reducePow, Nat.reduceMod]
    omega]
  cell_facts 64, 17, u₁₁, f₁₁
  peel_cell 64, 17, u₁₁
  -- cell 17 holds add-back 4's limb, fiat's `x18`
  have hload₁₇ : BitVec.extractLsb' (cellPtr s 17).offsetInBits 64 c₁₇blk.bytes
      = x18 := by
    have hread : readWord? (cellPtr s 17) 64 u₁₁.mem
        = some (BitVec.extractLsb' (cellPtr s 17).offsetInBits 64 c₁₇blk.bytes) := by
      simp [readWord?, MemoryState.live?, hc₁₇blk]
    have hchain : readWord? (cellPtr s 17) 64 u₁₁.mem
        = readWord? (cellPtr s 17) 64 u₁₀.mem := by
      rw [w₁₁.survive? 64 (cells.ne (by decide)) (cells.ne (by decide))]
    simpa using (hread.symm.trans hchain).trans
      (readWord?_eq_some w₁₀.fita w₁₀.vala)
  simp only [hload₁₇]
  clear hload₁₇ hc₁₇blk hc₁₇len c₁₇blk hcell₁₇
  obtain ⟨x23, hx23⟩ : ∃ z, z = BitVec.ofNat 64 (2 * x18.toNat) := ⟨_, rfl⟩
  denote_step_all v 92
  denote_eval v 92 92
  eval_llvm 92 [show x18 <<< 1#64 = x23 from by
    rw [hx23]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.shiftLeft_eq', BitVec.toNat_shiftLeft, BitVec.toNat_ofNat,
      Nat.shiftLeft_eq, Nat.reducePow, Nat.reduceMod]
    omega]
  cell_facts 64, 15, u₁₁, f₁₁
  peel_cell 64, 15, u₁₁
  -- cell 15 holds add-back 3's limb, fiat's `x16`
  have hload₁₅ : BitVec.extractLsb' (cellPtr s 15).offsetInBits 64 c₁₅blk.bytes
      = x16 := by
    have hread : readWord? (cellPtr s 15) 64 u₁₁.mem
        = some (BitVec.extractLsb' (cellPtr s 15).offsetInBits 64 c₁₅blk.bytes) := by
      simp [readWord?, MemoryState.live?, hc₁₅blk]
    have hchain : readWord? (cellPtr s 15) 64 u₁₁.mem
        = readWord? (cellPtr s 15) 64 u₉.mem := by
      rw [w₁₁.survive? 64 (cells.ne (by decide)) (cells.ne (by decide)),
        w₁₀.survive? 64 (cells.ne (by decide)) (cells.ne (by decide))]
    simpa using (hread.symm.trans hchain).trans
      (readWord?_eq_some w₉.fita w₉.vala)
  simp only [hload₁₅]
  clear hload₁₅ hc₁₅blk hc₁₅len c₁₅blk hcell₁₅
  obtain ⟨x24, hx24⟩ : ∃ z, z = BitVec.ofNat 64 (64 * x16.toNat) := ⟨_, rfl⟩
  denote_step_all v 94
  denote_eval v 94 94
  eval_llvm 94 [show x16 <<< 6#64 = x24 from by
    rw [hx24]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.shiftLeft_eq', BitVec.toNat_shiftLeft, BitVec.toNat_ofNat,
      Nat.shiftLeft_eq, Nat.reducePow, Nat.reduceMod]
    omega]
  -- Cell 13 is what add-back 2 wrote, fiat's `x14`; add-backs 3-5 wrote cells
  -- 15-20, so `w₈`'s value survives to `u₁₁`.
  cell_facts 64, 13, u₁₁, f₁₁
  peel_cell 64, 13, u₁₁
  have hload₁₃ : BitVec.extractLsb' (cellPtr s 13).offsetInBits 64 c₁₃blk.bytes = x14 := by
    have hread : readWord? (cellPtr s 13) 64 u₁₁.mem
        = some (BitVec.extractLsb' (cellPtr s 13).offsetInBits 64 c₁₃blk.bytes) := by
      simp [readWord?, MemoryState.live?, hc₁₃blk]
    have hchain : readWord? (cellPtr s 13) 64 u₁₁.mem = readWord? (cellPtr s 13) 64 u₈.mem := by
      rw [w₁₁.survive? 64 (cells.ne (by decide)) (cells.ne (by decide)),
        w₁₀.survive? 64 (cells.ne (by decide)) (cells.ne (by decide)),
        w₉.survive? 64 (cells.ne (by decide)) (cells.ne (by decide))]
    simpa using (hread.symm.trans hchain).trans (readWord?_eq_some w₈.fita w₈.vala)
  simp only [hload₁₃]
  clear hload₁₃ hc₁₃blk hc₁₃len c₁₃blk hcell₁₃
  -- the shift is plain scaling; the stepper's bit-level form is proved back
  -- from this where it is needed, rather than carried alongside it
  obtain ⟨x25, hx25⟩ : ∃ z, z = BitVec.ofNat 64 (8 * x14.toNat) := ⟨_, rfl⟩
  denote_step_all v 96
  denote_eval v 96 96
  eval_llvm 96 [show x14 <<< 3#64 = x25 from by
    rw [hx25]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.shiftLeft_eq', BitVec.toNat_shiftLeft, BitVec.toNat_ofNat,
      Nat.shiftLeft_eq, Nat.reducePow, Nat.reduceMod]
    omega]
  -- Cell 11 is what add-back 1 wrote, i.e. fiat's `x12`. The four calls since
  -- then wrote cells 13-20, so `w₇`'s value survives to `u₁₁` and the load can
  -- be read back as `x12` -- which is what the store chain below is stated over.
  cell_facts 64, 11, u₁₁, f₁₁
  peel_cell 64, 11, u₁₁
  have hload₁₁ : BitVec.extractLsb' (cellPtr s 11).offsetInBits 64 c₁₁blk.bytes = x12 := by
    have hread : readWord? (cellPtr s 11) 64 u₁₁.mem
        = some (BitVec.extractLsb' (cellPtr s 11).offsetInBits 64 c₁₁blk.bytes) := by
      simp [readWord?, MemoryState.live?, hc₁₁blk]
    have hchain : readWord? (cellPtr s 11) 64 u₁₁.mem = readWord? (cellPtr s 11) 64 u₇.mem := by
      rw [w₁₁.survive? 64 (cells.ne (by decide)) (cells.ne (by decide)),
        w₁₀.survive? 64 (cells.ne (by decide)) (cells.ne (by decide)),
        w₉.survive? 64 (cells.ne (by decide)) (cells.ne (by decide)),
        w₈.survive? 64 (cells.ne (by decide)) (cells.ne (by decide))]
    simpa using (hread.symm.trans hchain).trans (readWord?_eq_some w₇.fita w₇.vala)
  simp only [hload₁₁]
  clear hload₁₁ hc₁₁blk hc₁₁len c₁₁blk hcell₁₁
  clear_subscript 1 11 w
  clear l₁₁
  -- the four byte accumulators, named before the extraction so it folds them
  -- rather than duplicating the chain behind each into every consumer
  -- `x12` is a limb, so its top three bits are all the mask can keep: the
  -- accumulator is the bits `x12`'s six bytes left over, plus `x14` above them
  obtain ⟨x38, hx38⟩ : ∃ z, z = BitVec.ofNat 64 (x12.toNat / 2 ^ 48 + x25.toNat) :=
    ⟨_, rfl⟩
  -- The accumulator chain in ℕ, stated here while every operand is still an
  -- atom. Each is the previous one's overflow above the bytes just written plus
  -- the next limb scaled to its boundary; the bounds interleave because the
  -- region's `&&& 255` is a no-op only once the shifted-out part is a byte.
  have hx25lt : x25.toNat < 2 ^ 54 := by rw [hx25, BitVec.toNat_ofNat]; omega
  have hx22nat : x22.toNat = 16 * x20.toNat := by
    rw [hx22, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hx23nat : x23.toNat = 2 * x18.toNat := by
    rw [hx23, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hx24nat : x24.toNat = 64 * x16.toNat := by
    rw [hx24, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hx38nat : x38.toNat = x12.toNat / 2 ^ 48 + x25.toNat := by
    rw [hx38, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hx38lt : x38.toNat < 2 ^ 55 := by rw [hx38nat]; omega
  have hx38bits : (x12 >>> 48#64 &&& 255#64) + x25 = x38 :=
    (accStep (a := x12) (b := x25) (by omega)).trans hx38.symm
  obtain ⟨x51, hx51⟩ : ∃ z, z = BitVec.ofNat 64 (x38.toNat / 2 ^ 48 + x24.toNat) := ⟨_, rfl⟩
  have hx51nat : x51.toNat = x38.toNat / 2 ^ 48 + x24.toNat := by
    rw [hx51, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hx51lt : x51.toNat < 2 ^ 58 := by rw [hx51nat]; omega
  have hx51bits : (x38 >>> 48#64 &&& 255#64) + x24 = x51 :=
    (accStep (a := x38) (b := x24) (by omega)).trans hx51.symm
  obtain ⟨x66, hx66⟩ : ∃ z, z = BitVec.ofNat 64 (x51.toNat / 2 ^ 56 + x23.toNat) := ⟨_, rfl⟩
  have hx66nat : x66.toNat = x51.toNat / 2 ^ 56 + x23.toNat := by
    rw [hx66, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hx66lt : x66.toNat < 2 ^ 53 := by rw [hx66nat]; omega
  have hx66bits : (x51 >>> 56#64) + x23 = x66 :=
    (accStep' (a := x51) (b := x23)).trans hx66.symm
  obtain ⟨x79, hx79⟩ : ∃ z, z = BitVec.ofNat 64 (x66.toNat / 2 ^ 48 + x22.toNat) := ⟨_, rfl⟩
  have hx79nat : x79.toNat = x66.toNat / 2 ^ 48 + x22.toNat := by
    rw [hx79, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hx79bits : (x66 >>> 48#64 &&& 255#64) + x22 = x79 :=
    (accStep (a := x66) (b := x22) (by omega)).trans hx79.symm
  -- %98-%167: the byte extraction, fiat's `x26`-`x91`. Pure arithmetic, so
  -- the stepper runs all of it in one go.
  denote_step_all v 167
  -- fiat's `x38`, `x51`, `x66`, `x79` each feed seven byte extractions.
  -- Evaluating a consumer inlines its operand's equation, so unless each is
  -- named first the chain behind it is duplicated into every consumer and the
  -- terms grow multiplicatively.
  denote_eval v 98 111
  eval_llvm_range 98 110
  eval_llvm 111 [hx38bits]
  denote_eval v 112 125
  eval_llvm_range 112 124
  eval_llvm 125 [hx51bits]
  denote_eval v 126 140
  eval_llvm_range 126 139
  eval_llvm 140 [hx66bits]
  denote_eval v 141 154
  eval_llvm_range 141 153
  eval_llvm 154 [hx79bits]
  clear hx38bits hx51bits hx66bits hx79bits hx25lt hx38lt hx51lt hx66lt
  denote_eval v 155 167
  eval_llvm_range 155 167
  -- The out-buffer, reached through the frame.
  have hou : Fits u₁₁.mem o (32 * 8) := fits_of_live?_eq (f₁₁.fb o.id cells.ido) ho.left

  clear hx4 hx6 hx8 hx11 hx13

  store_bytes 0 6, o, hou, u₁₁

  -- `++` puts its left argument in the high bits, so stacking byte `w / 8` on
  -- the low `w` bits of `d` just extends the prefix. Bounds are irrelevant:
  -- past `v` both sides read zero.

  -- One store absorbed: transport the accumulated equivalence through the new
  -- splice, then merge the two adjacent ranges into one. Both arguments have to
  -- be pinned -- neither `h` nor `hoff` fixes what was stored, and the record
  -- literal `h` ends in stops the unifier from inverting `?s.mem` against it.

  -- `merge` where the buffer is a prefix of one word, so the two ranges fold
  -- back into a longer prefix.


  simp only [o₁, o₂, o₃, o₄, o₅, BitVec.truncate_eq_setWidth, BitVec.ushiftRight_eq',
    BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at hm₁ hm₂ hm₃ hm₄ hm₅ hm₆

  have e₁ : m₁ ≈ { u₁₁ with mem := u₁₁.mem.splice o (BitVec.setWidth 8 x12) } := by rw [hm₁]
  have e₂ : m₂ ≈ { u₁₁ with mem := u₁₁.mem.splice o (BitVec.setWidth 16 x12) } := by
    rw [hm₂]; exact step e₁ (byteOffsetInBits ho.right (k := 1) (by omega) (by simp))
  have e₃ : m₃ ≈ { u₁₁ with mem := u₁₁.mem.splice o (BitVec.setWidth 24 x12) } := by
    rw [hm₃]; exact step e₂ (byteOffsetInBits ho.right (k := 2) (by omega) (by simp))
  have e₄ : m₄ ≈ { u₁₁ with mem := u₁₁.mem.splice o (BitVec.setWidth 32 x12) } := by
    rw [hm₄]; exact step e₃ (byteOffsetInBits ho.right (k := 3) (by omega) (by simp))
  have e₅ : m₅ ≈ { u₁₁ with mem := u₁₁.mem.splice o (BitVec.setWidth 40 x12) } := by
    rw [hm₅]; exact step e₄ (byteOffsetInBits ho.right (k := 4) (by omega) (by simp))
  have e₆ : m₆ ≈ { u₁₁ with mem := u₁₁.mem.splice o (BitVec.setWidth 48 x12) } := by
    rw [hm₆]; exact step e₅ (byteOffsetInBits ho.right (k := 5) (by omega) (by simp))

  -- `g₆` outlives its family: the next run of stores starts from it
  have gbuf := g₆
  clear_subscript 1 5 e g m hm ho
  -- `x12` is the low digit of add-back 1's sum, and that whole sum -- subtract
  -- `p`'s limb with a borrow, add the mask back -- is one reduction mod
  -- `2 ^ 51`. The borrow stays explicit so that this and `hx13val`, the matching
  -- quotient, are the same numerator: `%` would tolerate absorbing it into the
  -- `2 ^ 51`, `/` would not.
  have hx12nat : x12.toNat = (x1.toNat + mask₀.toNat) % 2 ^ 51 := by
    have hlow := eq_mod_of_split hx12 hsum₇
    simp only [show (BitVec.ofInt 8 0).toNat = 0 from by decide, Nat.zero_add] at hlow
    rw [hlow]

  store_bytes 6 12, o, gbuf, m₆

  -- Bytes 6-11 come out of `x38`. Restating them against `m₆` and `o₆` -- the
  -- state and pointer the group starts at -- keeps the buffer a prefix of one
  -- word, so the `x12` bytes need not be carried along; the two groups are
  -- joined at the end by one more `merge`.
  simp only [o₇, o₈, o₉, o₁₀, o₁₁, BitVec.truncate_eq_setWidth, BitVec.ushiftRight_eq',
    BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at hm₇ hm₈ hm₉ hm₁₀ hm₁₁ hm₁₂

  -- the walk geps off `o`, `step` off the group's own base
  have hgep {x y : BitVec 64} (hxy : x = 6#64 + y) : o.withOffset x = o₆.withOffset y := by
    simp [o₆, Pointer.withOffset, hxy, BitVec.add_assoc]
  -- and its offsets are the buffer's, less the six bytes already there
  have hoff₆ {k : ℕ} (hk6 : 6 ≤ k) (hk : k ≤ 31) {y : BitVec 64} (hy : (6#64 + y).toNat = k) :
      (o₆.withOffset y).offsetInBits = o₆.offsetInBits + 8 * (k - 6) := by
    rw [← hgep (by rfl), byteOffsetInBits ho.right hk hy]
    unfold o₆
    rw [byteOffsetInBits ho.right (k := 6) (off := (6 : BitVec _)) (by omega) (by simp), Nat.add_assoc, ← Nat.mul_add, Nat.add_sub_cancel' hk6]

  have e₇ : m₇ ≈ { m₆ with mem := m₆.mem.splice o₆ (BitVec.setWidth 8 x38) } := by rw [hm₇]
  have e₈ : m₈ ≈ { m₆ with mem := m₆.mem.splice o₆ (BitVec.setWidth 16 x38) } := by
    rw [hm₈, hgep (x := (7 : BitVec 64)) (y := (1 : BitVec 64)) (by decide)]
    exact step e₇ (hoff₆ (k := 7) (by omega) (by omega) (by decide))
  have e₉ : m₉ ≈ { m₆ with mem := m₆.mem.splice o₆ (BitVec.setWidth 24 x38) } := by
    rw [hm₉, hgep (x := (8 : BitVec 64)) (y := (2 : BitVec 64)) (by decide)]
    exact step e₈ (hoff₆ (k := 8) (by omega) (by omega) (by decide))
  have e₁₀ : m₁₀ ≈ { m₆ with mem := m₆.mem.splice o₆ (BitVec.setWidth 32 x38) } := by
    rw [hm₁₀, hgep (x := (9 : BitVec 64)) (y := (3 : BitVec 64)) (by decide)]
    exact step e₉ (hoff₆ (k := 9) (by omega) (by omega) (by decide))
  have e₁₁ : m₁₁ ≈ { m₆ with mem := m₆.mem.splice o₆ (BitVec.setWidth 40 x38) } := by
    rw [hm₁₁, hgep (x := (10 : BitVec 64)) (y := (4 : BitVec 64)) (by decide)]
    exact step e₁₀ (hoff₆ (k := 10) (by omega) (by omega) (by decide))
  have e₁₂ : m₁₂ ≈ { m₆ with mem := m₆.mem.splice o₆ (BitVec.setWidth 48 x38) } := by
    rw [hm₁₂, hgep (x := (11 : BitVec 64)) (y := (5 : BitVec 64)) (by decide)]
    exact step e₁₁ (hoff₆ (k := 11) (by omega) (by omega) (by decide))

  clear hoff₆
  clear_subscript 7 11 e g m hm ho

  have hx13val : x13.toNat
      = (readLimb 0 hq + 2 ^ 51 * x2.toNat - pLimb 0 + mask₀.toNat) / 2 ^ 51 := by
    rw [eq_div_of_split hx12 hsum₇]
    simp only [show (BitVec.ofInt 8 0).toNat = 0 from by decide, Nat.zero_add]
    rw [limb_eq_of_split hsum₁]
  have hx3val : x3.toNat = readLimb 1 hq + 2 ^ 51 * x4.toNat - (x2.toNat + pLimb 1) :=
    limb_eq_of_split (Nat.add_assoc _ _ _ ▸ hsum₂)

  -- The two groups joined: `merge` again, with a 48-bit `b` this time. `e₆` is
  -- the accumulator, `e₁₂` the range above it, and `o₆` is 48 bits along.
  replace e₁₂ := GlobalState.Equiv.trans e₁₂
    (merge (b := BitVec.setWidth 48 x38) (off := (6 : BitVec 64)) e₆
      (byteOffsetInBits ho.right (k := 6) (by omega) (by simp)))
  -- Two 48-bit halves are one 96-bit number: `++` puts `b` above `a`, and the
  -- halves cannot overlap, so the `|||` core states it with is an addition.
  rw [hpack] at e₁₂
  -- Reassembled: the high half carries exactly `x12`'s quotient, so the two
  -- ranges telescope back into `x12` with `x25` shifted to byte 6.
  -- `x25` in ℕ: `x14` is a limb, so the scaling stays inside `2 ^ 54`
  have hx25nat : x25.toNat
      = (8 * x13.toNat + 8 * x3.toNat + 8 * mask₁.toNat) % 2 ^ 54 := by
    rw [hx25, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      eq_mod_of_split hx14 hsum₈, ← Nat.mul_add, ← Nat.mul_add,
      show (2:ℕ) ^ 54 = 8 * 2 ^ 51 from rfl, Nat.mul_mod_mul_left]
  have hjoin : x12.toNat % 2 ^ 48 + 2 ^ 48 * (x38.toNat % 2 ^ 48)
      = (x12.toNat + 2 ^ 48 * x25.toNat) % 2 ^ 96 := by
    rw [hx38nat]; exact join48
  rw [hjoin] at e₁₂



  -- Bytes 12-18, out of `x51`, against `m₁₂`/`o₁₂`.
  store_bytes 12 19, o, g₁₂, m₁₂
  simp only [o₁₃, o₁₄, o₁₅, o₁₆, o₁₇, o₁₈, BitVec.truncate_eq_setWidth, BitVec.ushiftRight_eq',
    BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at hm₁₃ hm₁₄ hm₁₅ hm₁₆ hm₁₇ hm₁₈ hm₁₉

  have hgep₁₂ {x y : BitVec 64} (hxy : x = 12#64 + y) :
      o.withOffset x = o₁₂.withOffset y := by
    simp [o₁₂, Pointer.withOffset, hxy, BitVec.add_assoc]
  have hoff₁₂ {k : ℕ} (hlo : 12 ≤ k) (hk : k ≤ 31) {y : BitVec 64}
      (hy : (12#64 + y).toNat = k) :
      (o₁₂.withOffset y).offsetInBits = o₁₂.offsetInBits + 8 * (k - 12) := by
    rw [← hgep₁₂ (by rfl), byteOffsetInBits ho.right hk hy]
    unfold o₁₂
    rw [byteOffsetInBits ho.right (k := 12) (off := (12 : BitVec _)) (by omega) (by simp), Nat.add_assoc, ← Nat.mul_add, Nat.add_sub_cancel' hlo]

  have e₁₃ : m₁₃ ≈ { m₁₂ with mem := m₁₂.mem.splice o₁₂ (BitVec.setWidth 8 x51) } := by
    rw [hm₁₃]
  have e₁₄ : m₁₄ ≈ { m₁₂ with mem := m₁₂.mem.splice o₁₂ (BitVec.setWidth 16 x51) } := by
    rw [hm₁₄, hgep₁₂ (x := (13 : BitVec 64)) (y := (1 : BitVec 64)) (by decide)]
    exact step e₁₃ (hoff₁₂ (k := 13) (by omega) (by omega) (by decide))
  have e₁₅ : m₁₅ ≈ { m₁₂ with mem := m₁₂.mem.splice o₁₂ (BitVec.setWidth 24 x51) } := by
    rw [hm₁₅, hgep₁₂ (x := (14 : BitVec 64)) (y := (2 : BitVec 64)) (by decide)]
    exact step e₁₄ (hoff₁₂ (k := 14) (by omega) (by omega) (by decide))
  have e₁₆ : m₁₆ ≈ { m₁₂ with mem := m₁₂.mem.splice o₁₂ (BitVec.setWidth 32 x51) } := by
    rw [hm₁₆, hgep₁₂ (x := (15 : BitVec 64)) (y := (3 : BitVec 64)) (by decide)]
    exact step e₁₅ (hoff₁₂ (k := 15) (by omega) (by omega) (by decide))
  have e₁₇ : m₁₇ ≈ { m₁₂ with mem := m₁₂.mem.splice o₁₂ (BitVec.setWidth 40 x51) } := by
    rw [hm₁₇, hgep₁₂ (x := (16 : BitVec 64)) (y := (4 : BitVec 64)) (by decide)]
    exact step e₁₆ (hoff₁₂ (k := 16) (by omega) (by omega) (by decide))
  have e₁₈ : m₁₈ ≈ { m₁₂ with mem := m₁₂.mem.splice o₁₂ (BitVec.setWidth 48 x51) } := by
    rw [hm₁₈, hgep₁₂ (x := (17 : BitVec 64)) (y := (5 : BitVec 64)) (by decide)]
    exact step e₁₇ (hoff₁₂ (k := 17) (by omega) (by omega) (by decide))
  have e₁₉ : m₁₉ ≈ { m₁₂ with mem := m₁₂.mem.splice o₁₂ (BitVec.setWidth 56 x51) } := by
    rw [hm₁₉, hgep₁₂ (x := (18 : BitVec 64)) (y := (6 : BitVec 64)) (by decide)]
    exact step e₁₈ (hoff₁₂ (k := 18) (by omega) (by omega) (by decide))

  clear hoff₁₂
  clear_subscript 13 18 e g m hm ho
  have ebuf₁₂ := GlobalState.Equiv.trans e₁₉
    (merge (b := BitVec.setWidth 56 x51) (off := (12 : BitVec 64)) e₁₂
      (byteOffsetInBits ho.right (k := 12) (by omega) (by simp)))
  -- `x51` is the running total's quotient above byte 12, plus `x24`; so bytes
  -- 0-18 are the total with `x24` shifted to byte 12
  have hx51tot : x51.toNat = (x12.toNat + 2 ^ 48 * x25.toNat) / 2 ^ 96 + x24.toNat := by
    rw [hx51nat, hx38nat, divChain48]
  rw [packAt, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_mod, hx51tot, join96] at ebuf₁₂

  -- Bytes 19-24, out of `x66`, against `m₁₉`/`o₁₉`.
  store_bytes 19 25, o, g₁₉, m₁₉
  simp only [o₂₀, o₂₁, o₂₂, o₂₃, o₂₄, BitVec.truncate_eq_setWidth, BitVec.ushiftRight_eq',
    BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at hm₂₀ hm₂₁ hm₂₂ hm₂₃ hm₂₄ hm₂₅

  have hgep₁₉ {x y : BitVec 64} (hxy : x = 19#64 + y) :
      o.withOffset x = o₁₉.withOffset y := by
    simp [o₁₉, Pointer.withOffset, hxy, BitVec.add_assoc]
  have hoff₁₉ {k : ℕ} (hlo : 19 ≤ k) (hk : k ≤ 31) {y : BitVec 64}
      (hy : (19#64 + y).toNat = k) :
      (o₁₉.withOffset y).offsetInBits = o₁₉.offsetInBits + 8 * (k - 19) := by
    rw [← hgep₁₉ (by rfl), byteOffsetInBits ho.right hk hy]
    unfold o₁₉
    rw [byteOffsetInBits ho.right (k := 19) (off := (19 : BitVec _)) (by omega) (by simp),
      Nat.add_assoc, ← Nat.mul_add, Nat.add_sub_cancel' hlo]

  have e₂₀ : m₂₀ ≈ { m₁₉ with mem := m₁₉.mem.splice o₁₉ (BitVec.setWidth 8 x66) } := by
    rw [hm₂₀]
  have e₂₁ : m₂₁ ≈ { m₁₉ with mem := m₁₉.mem.splice o₁₉ (BitVec.setWidth 16 x66) } := by
    rw [hm₂₁, hgep₁₉ (x := (20 : BitVec 64)) (y := (1 : BitVec 64)) (by decide)]
    exact step e₂₀ (hoff₁₉ (k := 20) (by omega) (by omega) (by decide))
  have e₂₂ : m₂₂ ≈ { m₁₉ with mem := m₁₉.mem.splice o₁₉ (BitVec.setWidth 24 x66) } := by
    rw [hm₂₂, hgep₁₉ (x := (21 : BitVec 64)) (y := (2 : BitVec 64)) (by decide)]
    exact step e₂₁ (hoff₁₉ (k := 21) (by omega) (by omega) (by decide))
  have e₂₃ : m₂₃ ≈ { m₁₉ with mem := m₁₉.mem.splice o₁₉ (BitVec.setWidth 32 x66) } := by
    rw [hm₂₃, hgep₁₉ (x := (22 : BitVec 64)) (y := (3 : BitVec 64)) (by decide)]
    exact step e₂₂ (hoff₁₉ (k := 22) (by omega) (by omega) (by decide))
  have e₂₄ : m₂₄ ≈ { m₁₉ with mem := m₁₉.mem.splice o₁₉ (BitVec.setWidth 40 x66) } := by
    rw [hm₂₄, hgep₁₉ (x := (23 : BitVec 64)) (y := (4 : BitVec 64)) (by decide)]
    exact step e₂₃ (hoff₁₉ (k := 23) (by omega) (by omega) (by decide))
  have e₂₅ : m₂₅ ≈ { m₁₉ with mem := m₁₉.mem.splice o₁₉ (BitVec.setWidth 48 x66) } := by
    rw [hm₂₅, hgep₁₉ (x := (24 : BitVec 64)) (y := (5 : BitVec 64)) (by decide)]
    exact step e₂₄ (hoff₁₉ (k := 24) (by omega) (by omega) (by decide))

  clear hoff₁₉
  clear_subscript 20 24 e g m hm ho
  have ebuf₁₉ := GlobalState.Equiv.trans e₂₅
    (merge (b := BitVec.setWidth 48 x66) (off := (19 : BitVec 64)) ebuf₁₂
      (byteOffsetInBits ho.right (k := 19) (by omega) (by simp)))
  have hx66tot : x66.toNat
      = (x12.toNat + 2 ^ 48 * x25.toNat + 2 ^ 96 * x24.toNat) / 2 ^ 152 + x23.toNat := by
    rw [hx66nat, hx51tot, divChain96]
  rw [packAt, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
    show (2 : ℕ) ^ (56 + 96) = 2 ^ 152 from rfl, Nat.mod_mod, hx66tot, join152] at ebuf₁₉

  -- Bytes 25-31, out of `x79`, against `m₂₅`/`o₂₅`.
  store_bytes 25 32, o, g₂₅, m₂₅
  simp only [o₂₆, o₂₇, o₂₈, o₂₉, o₃₀, o₃₁, BitVec.truncate_eq_setWidth, BitVec.ushiftRight_eq',
    BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at hm₂₆ hm₂₇ hm₂₈ hm₂₉ hm₃₀ hm₃₁ hm₃₂

  have hgep₂₅ {x y : BitVec 64} (hxy : x = 25#64 + y) :
      o.withOffset x = o₂₅.withOffset y := by
    simp [o₂₅, Pointer.withOffset, hxy, BitVec.add_assoc]
  have hoff₂₅ {k : ℕ} (hlo : 25 ≤ k) (hk : k ≤ 31) {y : BitVec 64}
      (hy : (25#64 + y).toNat = k) :
      (o₂₅.withOffset y).offsetInBits = o₂₅.offsetInBits + 8 * (k - 25) := by
    rw [← hgep₂₅ (by rfl), byteOffsetInBits ho.right hk hy]
    unfold o₂₅
    rw [byteOffsetInBits ho.right (k := 25) (off := (25 : BitVec _)) (by omega) (by simp),
      Nat.add_assoc, ← Nat.mul_add, Nat.add_sub_cancel' hlo]

  have e₂₆ : m₂₆ ≈ { m₂₅ with mem := m₂₅.mem.splice o₂₅ (BitVec.setWidth 8 x79) } := by
    rw [hm₂₆]
  have e₂₇ : m₂₇ ≈ { m₂₅ with mem := m₂₅.mem.splice o₂₅ (BitVec.setWidth 16 x79) } := by
    rw [hm₂₇, hgep₂₅ (x := (26 : BitVec 64)) (y := (1 : BitVec 64)) (by decide)]
    exact step e₂₆ (hoff₂₅ (k := 26) (by omega) (by omega) (by decide))
  have e₂₈ : m₂₈ ≈ { m₂₅ with mem := m₂₅.mem.splice o₂₅ (BitVec.setWidth 24 x79) } := by
    rw [hm₂₈, hgep₂₅ (x := (27 : BitVec 64)) (y := (2 : BitVec 64)) (by decide)]
    exact step e₂₇ (hoff₂₅ (k := 27) (by omega) (by omega) (by decide))
  have e₂₉ : m₂₉ ≈ { m₂₅ with mem := m₂₅.mem.splice o₂₅ (BitVec.setWidth 32 x79) } := by
    rw [hm₂₉, hgep₂₅ (x := (28 : BitVec 64)) (y := (3 : BitVec 64)) (by decide)]
    exact step e₂₈ (hoff₂₅ (k := 28) (by omega) (by omega) (by decide))
  have e₃₀ : m₃₀ ≈ { m₂₅ with mem := m₂₅.mem.splice o₂₅ (BitVec.setWidth 40 x79) } := by
    rw [hm₃₀, hgep₂₅ (x := (29 : BitVec 64)) (y := (4 : BitVec 64)) (by decide)]
    exact step e₂₉ (hoff₂₅ (k := 29) (by omega) (by omega) (by decide))
  have e₃₁ : m₃₁ ≈ { m₂₅ with mem := m₂₅.mem.splice o₂₅ (BitVec.setWidth 48 x79) } := by
    rw [hm₃₁, hgep₂₅ (x := (30 : BitVec 64)) (y := (5 : BitVec 64)) (by decide)]
    exact step e₃₀ (hoff₂₅ (k := 30) (by omega) (by omega) (by decide))
  have e₃₂ : m₃₂ ≈ { m₂₅ with mem := m₂₅.mem.splice o₂₅ (BitVec.setWidth 56 x79) } := by
    rw [hm₃₂, hgep₂₅ (x := (31 : BitVec 64)) (y := (6 : BitVec 64)) (by decide)]
    exact step e₃₁ (hoff₂₅ (k := 31) (by omega) (by omega) (by decide))

  clear hoff₂₅
  clear_subscript 26 31 e g m hm ho
  have ebuf₂₅ := GlobalState.Equiv.trans e₃₂
    (merge (b := BitVec.setWidth 56 x79) (off := (25 : BitVec 64)) ebuf₁₉
      (byteOffsetInBits ho.right (k := 25) (by omega) (by simp)))
  have hx79tot : x79.toNat
      = (x12.toNat + 2 ^ 48 * x25.toNat + 2 ^ 96 * x24.toNat + 2 ^ 152 * x23.toNat) / 2 ^ 200
        + x22.toNat := by
    rw [hx79nat, hx66tot, divChain152]
  rw [packAt, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
    show (2 : ℕ) ^ (48 + (56 + 96)) = 2 ^ 200 from rfl, Nat.mod_mod, hx79tot, join200] at ebuf₂₅


  iterate 21 peel_lifetime

  have hcanon : (x12.toNat + 2 ^ 48 * x25.toNat + 2 ^ 96 * x24.toNat + 2 ^ 152 * x23.toNat
      + 2 ^ 200 * x22.toNat) % 2 ^ 256 = (readFieldElem hq).val := by
    have hx25s : x25.toNat = 8 * x14.toNat := by
      rw [hx25, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    rw [hx25s, hx24nat, hx23nat, hx22nat, Nat.mod_eq_of_lt (by omega)]
    simp only [show (BitVec.ofInt 8 0).toNat = 0 from by decide, Nat.zero_add] at hsum₇
    have hadd := addback_tel hsum₇ hsum₈ hsum₉ hsum₁₀ hsum₁₁
    have hbor := borrow_tel hsum₁ hsum₂ hsum₃ hsum₄ hsum₅
    --rw [hR, hY]
    -- the mask is `p` exactly when the final borrow is set
    have hM : mask₀.toNat + mask₁.toNat * (2^51 + 2^102 + 2^153 + 2^204)
        = if x10.toNat = 0 then 0 else 2^255 - 19 := by
      rw [hmask₀, hmask₁]
      by_cases h : x10 = 0#8
      · simp [h]
      · have : x10.toNat ≠ 0 := fun h0 => h (BitVec.eq_of_toNat_eq h0)
        simp [h, this, pLimb]
    rw [hM] at hadd
    have hV : readLimb 0 hq + 2 ^ 51 * readLimb 1 hq + 2 ^ 102 * readLimb 2 hq
    + 2 ^ 153 * readLimb 3 hq + 2 ^ 204 * readLimb 4 hq < 2 ^ 256 - 38 :=
      calc readLimb 0 hq + 2 ^ 51 * readLimb 1 hq + 2 ^ 102 * readLimb 2 hq
          + 2 ^ 153 * readLimb 3 hq + 2 ^ 204 * readLimb 4 hq
          ≤ 2 ^ 51 + 2 ^ 51 * 2 ^ 51 + 2 ^ 102 * 2 ^ 51 + 2 ^ 153 * 2 ^ 51 + 2 ^ 204 * 2 ^ 51 := by
            gcongr <;> exact hqlimb _
        _ < 2 ^ 256 - 38 := by norm_num
    -- Both chains leave five digits below `2 ^ 51`, so each sum is at most
    -- `2 ^ 255 - 1`: the digit bounds, one weight at a time.
    have hY : x1.toNat + 2 ^ 51 * x3.toNat + 2 ^ 102 * x5.toNat + 2 ^ 153 * x7.toNat
        + 2 ^ 204 * x9.toNat < 2 ^ 255 := by
      have hd₁ := Nat.le_sub_one_of_lt hx1
      have hd₃ := Nat.le_sub_one_of_lt hx3
      have hd₅ := Nat.le_sub_one_of_lt hx5
      have hd₇ := Nat.le_sub_one_of_lt hx7
      have hd₉ := Nat.le_sub_one_of_lt hx9
      calc x1.toNat + 2 ^ 51 * x3.toNat + 2 ^ 102 * x5.toNat + 2 ^ 153 * x7.toNat
          + 2 ^ 204 * x9.toNat
          ≤ (2 ^ 51 - 1) + 2 ^ 51 * (2 ^ 51 - 1) + 2 ^ 102 * (2 ^ 51 - 1)
            + 2 ^ 153 * (2 ^ 51 - 1) + 2 ^ 204 * (2 ^ 51 - 1) := by gcongr
        _ < 2 ^ 255 := by norm_num
    have hR : x12.toNat + 2 ^ 51 * x14.toNat + 2 ^ 102 * x16.toNat + 2 ^ 153 * x18.toNat
        + 2 ^ 204 * x20.toNat < 2 ^ 255 :=
      have hd₁₂ := Nat.le_sub_one_of_lt hx12
      have hd₁₄ := Nat.le_sub_one_of_lt hx14
      have hd₁₆ := Nat.le_sub_one_of_lt hx16
      have hd₁₈ := Nat.le_sub_one_of_lt hx18
      have hd₂₀ := Nat.le_sub_one_of_lt hx20
      calc x12.toNat + 2 ^ 51 * x14.toNat + 2 ^ 102 * x16.toNat + 2 ^ 153 * x18.toNat
          + 2 ^ 204 * x20.toNat
          ≤ (2 ^ 51 - 1) + 2 ^ 51 * (2 ^ 51 - 1) + 2 ^ 102 * (2 ^ 51 - 1)
            + 2 ^ 153 * (2 ^ 51 - 1) + 2 ^ 204 * (2 ^ 51 - 1) := by gcongr
        _ < 2 ^ 255 := by norm_num
    have := canon hV hY hR hx10 hbor hadd
    simp only [readFieldElem_val, ← this]
    ring
  rw [hcanon] at ebuf₂₅

  -- `llvm.return` with no operands: the walk ends, and the final state is the
  -- one after the last store. The spec's two clauses are then read off
  -- `ebuf₂₅`, which says that state is `u₁₁` with the buffer spliced in.
  simp_return
  refine popFrame_equiv_splice hs (lt_nextFreeBlock_of_fits hs ho.left) ?frame ?buf
  case frame =>
    -- a block that is not the buffer's: untouched by the splice, and below the
    -- frame, so the walk carried it through unchanged
    intro b hb hbo
    rw [ebuf₂₅.live b, live?_splice_ne (Ne.symm hbo)]
    exact f₁₁.fb b hb
  case buf =>
    -- the buffer's block: both sides splice the same value into the same
    -- block, since the frame identifies `u₁₁`'s block at `o` with `s`'s
    obtain ⟨blk, hblk, -⟩ := ho.left
    have hs' : s.mem.live? o.id = some blk := by simp only [MemoryState.live?, hblk]
    have hu : u₁₁.mem.live? o.id = some blk := (f₁₁.fb o.id cells.ido).trans hs'
    rw [ebuf₂₅.live o.id, splicedLive u₁₁.mem o blk hu, splicedLive s.mem o blk hs']

end Firedancer.Ref
