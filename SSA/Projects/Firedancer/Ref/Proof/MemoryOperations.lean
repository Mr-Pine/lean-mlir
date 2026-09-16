import SSA.Projects.SLLVM.Dialect
import SSA.Projects.Firedancer.MLIR.DenoteStep
import SSA.Projects.Firedancer.Ref.Spec.F25519
import SSA.Projects.Firedancer.Proof.Memory
import SSA.Projects.Firedancer.Proof.Tactics.Memory

namespace Firedancer.Ref

open LeanMLIR SLLVM
open InstCombine (LLVM)

/-- A store overwritten by a second store at the same pointer is invisible. -/
theorem splice_splice_equiv {s : GlobalState} {p : Pointer} {w : Nat} (x y : BitVec w) :
    ({ s with mem := (s.mem.splice p x).splice p y } : GlobalState) ≈
      { s with mem := s.mem.splice p y } := by
  refine ⟨rfl, rfl, fun q => ?_⟩
  by_cases hq : p.id = q
  · subst hq
    cases hb : s.mem.live? p.id with
    | none => rw [splicedDead (splicedDead hb), splicedDead hb]
    | some b =>
      rw [splicedLive _ _ _ (splicedLive _ _ _ hb x), splicedLive _ _ _ hb,
        spliceBits_spliceBits_self]
  · rw [live?_splice_ne hq, live?_splice_ne hq, live?_splice_ne hq]

@[simp_sllvm]
theorem fits_equiv {s s' : GlobalState} {p : Pointer} {n : Nat} (hs : s ≈ s') (h : Fits s.mem p n) :
    Fits s'.mem p n := by
  obtain ⟨block, hblk, hlen⟩ := h
  have block_equiv := hs.live p.id
  simp only [MemoryState.live?, hblk] at block_equiv
  -- `live?` is a `match`, so `block_equiv` is one too; splitting it names the
  -- branch and hands over the scrutinee's equation, which is the lookup wanted.
  replace block_equiv : s'.mem[p.id]? = some (Block.live block) := by
    split at block_equiv <;> simp_all
  exact ⟨block, block_equiv, hlen⟩

/-! ### Transporting a field element between states

A field-element read at `p` sees only the block `p.id` addresses, so one `live?`
equation carries `IsFieldElemPtr`, the limb reads and the limb bounds together.
Chain the equations with `.trans` rather than re-deriving each consequence. -/

/-- A limb read looks only at the block the pointer addresses. -/
theorem readLimb?_of_live?_eq {m m' : MemoryState} {p : Pointer} (h : m'.live? p.id = m.live? p.id)
    (i : Fin 5) : readLimb? p i m' = readLimb? p i m := by simp only [readLimb?, h]

/-- ... and so does `IsFieldElemPtr`. -/
theorem isFieldElemPtr_of_live?_eq {m m' : MemoryState} {p : Pointer}
    (h : m'.live? p.id = m.live? p.id) (hp : IsFieldElemPtr m p) : IsFieldElemPtr m' p :=
  ⟨fits_of_live?_eq h hp.left, hp.right⟩

/-- ... and a byte buffer. -/
theorem isByteBufPtr_of_live?_eq {m m' : MemoryState} {p : Pointer}
    (h : m'.live? p.id = m.live? p.id) (hp : IsByteBufPtr m p) : IsByteBufPtr m' p :=
  ⟨fits_of_live?_eq h hp.left, hp.right⟩

/-- `GlobalState.Equiv.live` with the right-hand state spelled `{ s with mem
:= m }`: the equation comes back in terms of `m`, so the caller never reduces
a projection under the callee's write chain. -/
theorem live?_of_equiv_mem {w s : GlobalState} {m : MemoryState}
    (he : w ≈ ({ s with mem := m } : GlobalState)) (b : BlockId) : w.mem.live? b = m.live? b :=
  he.live b

/-- A buffer that fitted in the memory a callee returned still fits in the
state it returned. Stated over `{ s with mem := m }` rather than over a second
state: `m` then unifies as a whole, instead of the caller's write chain being
compared against a projection limb by limb. -/
theorem isByteBufPtr_of_equiv {w s : GlobalState} {m : MemoryState} {q : Pointer}
    (he : w ≈ ({ s with mem := m } : GlobalState)) (h : IsByteBufPtr m q) : IsByteBufPtr w.mem q :=
  isByteBufPtr_of_live?_eq (live?_of_equiv_mem he q.id) h

/-- ... and the limb bounds, in the `readLimb?`-shaped form. -/
theorem limbBounds_of_live?_eq {m m' : MemoryState} {p : Pointer} {n : ℕ}
    (h : m'.live? p.id = m.live? p.id)
    (hb : ∀ (i : Fin 5) (l : ℕ), readLimb? p i m = some l → l ≤ n) :
    ∀ (i : Fin 5) (l : ℕ), readLimb? p i m' = some l → l ≤ n := fun i l hl =>
  hb i l ((readLimb?_of_live?_eq h i).symm.trans hl)

/-- ... and a whole field-element read. -/
theorem readFieldElem?_of_live?_eq {m m' : MemoryState} {p : Pointer}
    (h : m'.live? p.id = m.live? p.id) : readFieldElem? p m' = readFieldElem? p m := by
  simp only [readFieldElem?, readLimb?_of_live?_eq h]

/-- The total read, once the partial one is known. -/
theorem readFieldElem_eq_of {m : MemoryState} {ptr : Pointer} {h : IsFieldElemPtr m ptr}
    {v : ZMod p} (hv : readFieldElem? ptr m = some v) : readFieldElem h = v := by
  simp only [readFieldElem, hv, Option.get_some]

/-- An `alloca (5 * 64)` hands back exactly one field element: 40 bytes at
offset 0, which cannot wrap. -/
theorem isFieldElemPtr_afterAlloca_self (s : GlobalState) :
    IsFieldElemPtr (s.afterAlloca (5 * 64)).mem ⟨⟨s.alloc.nextFreeBlock⟩, 0⟩ :=
  ⟨fits_afterAlloca_self s (5 * 64), by simp⟩

lemma extractLimb (q b c d e : BitVec 64) (i : Fin 5) :
    (e ++ d ++ c ++ b ++ q).extractLsb' (64 * i.toNat) 64 = ![q, b, c, d, e] i := by
  fin_cases i <;> simp <;> bv_decide

lemma limbReadback (m : MemoryState) (p : Pointer) (a b c d e : BitVec 64) (hp : Fits m p 320)
    (i : Fin 5) :
    readLimb? p i (m.splice p (e ++ d ++ c ++ b ++ a)) = .some (![a, b, c, d, e] i).toNat := by
  obtain ⟨blk, hblk, hfits⟩ := hp
  have hb : m.live? p.id = .some blk := by simp [MemoryState.live?, hblk]
  have hi : i.toNat < 5 := i.isLt
  simp only [readLimb?, splicedLive m p blk hb _, Option.bind_eq_bind, Option.bind_some,
    Option.pure_def]
  -- v4.34: `LiveBlock.lengthInBits` no longer unfolds while `rw` unifies, so `hfits` alone
  -- no longer pins `bytes`; name the arguments.
  rw [extractLsb'_spliceBits_of_subrange blk.bytes p.offsetInBits (p.offsetInBits + 64 * i.toNat)
      (e ++ d ++ c ++ b ++ a) (by omega) (by omega) hfits,
    Nat.add_sub_cancel_left, extractLimb]

/-- A limb read back out of a splice sees only the spliced bits, whatever the
block underneath held. Two states that both fit a field element at `p` therefore
read the same after splicing the same value there. -/
lemma limbSpliceReadback (m : MemoryState) (p : Pointer) (x : BitVec (5 * 64))
    (hp : Fits m p (5 * 64)) (i : Fin 5) :
    readLimb? p i (m.splice p x) = .some (x.extractLsb' (64 * i.toNat) 64).toNat := by
  obtain ⟨blk, hblk, hfits⟩ := hp
  have hb : m.live? p.id = .some blk := by simp [MemoryState.live?, hblk]
  have hi : i.toNat < 5 := i.isLt
  simp only [readLimb?, splicedLive m p blk hb _, Option.bind_eq_bind, Option.bind_some,
    Option.pure_def]
  rw [extractLsb'_spliceBits_of_subrange blk.bytes p.offsetInBits (p.offsetInBits + 64 * i.toNat) x
      (by omega) (by omega) hfits,
    Nat.add_sub_cancel_left]

/-- `limbReadback` for limbs given as a function rather than five variables --
the form the specs' `packLimbs` witness takes. -/
lemma limbReadbackPack (m : MemoryState) (p : Pointer) (l : Fin 5 → BitVec 64)
    (hp : Fits m p (5 * 64)) (i : Fin 5) :
    readLimb? p i (m.splice p (packLimbs l)) = .some (l i).toNat := by
  rw [limbSpliceReadback _ _ _ hp i, extractLsb'_packLimbs]

/-- What a field element spliced at `p` reads back as: only the spliced bits,
whatever the block underneath held. -/
theorem readFieldElem?_splice {m : MemoryState} {p : Pointer} (x : BitVec (5 * 64))
    (hp : Fits m p (5 * 64)) :
    readFieldElem? p (m.splice p x) =
      some (decodeFieldElem fun i => (x.extractLsb' (64 * i.toNat) 64).toNat) := by
  obtain ⟨f, hfdef⟩ :
    ∃ f : Fin 5 → ℕ, f = fun i : Fin 5 => (x.extractLsb' (64 * i.toNat) 64).toNat := ⟨_, rfl⟩
  have hf : ∀ i : Fin 5, readLimb? p i (m.splice p x) = some (f i) := by
    rw [hfdef]; exact fun i => limbSpliceReadback _ _ _ hp i
  have hvec : (![f 0, f 1, f 2, f 3, f 4] : Fin 5 → ℕ) = f := by
    funext i; fin_cases i <;> rfl
  rw [← hfdef]
  simp only [readFieldElem?, hf, Option.bind_eq_bind, Option.bind_some, Option.pure_def, hvec]

/-- A limb read passes over a splice that misses it: another block, or a
disjoint bit range of the same one. -/
theorem readLimb?_splice_of_disjoint {m : MemoryState} {p q : Pointer} {w : Nat} {x : BitVec w}
    (i : Fin 5)
    (h :
      q.id ≠ p.id ∨
        q.offsetInBits + w ≤ p.offsetInBits + 64 * i.toNat ∨
        p.offsetInBits + 64 * i.toNat + 64 ≤ q.offsetInBits) :
    readLimb? p i (m.splice q x) = readLimb? p i m := by
  by_cases hid : q.id = p.id
  case neg => simp only [readLimb?, live?_splice_ne hid]
  case pos =>
    cases hb : m.live? q.id with
    | none =>
      have : m.splice q x = m := by
        unfold MemoryState.splice
        unfold MemoryState.live? at hb
        split at hb <;> simp_all
      rw [this]
    | some
      blk =>
      have hdisj :
        q.offsetInBits + w ≤ p.offsetInBits + 64 * i.toNat ∨
          p.offsetInBits + 64 * i.toNat + 64 ≤ q.offsetInBits := by
        rcases h with h | h | h
        · exact absurd hid h
        · exact .inl h
        · exact .inr h
      have hlive :
        (m.splice q x).live? p.id =
          some { length := blk.length, bytes := spliceBits blk.bytes q.offsetInBits x } := by
        rw [← hid]; exact splicedLive m q blk hb x
      have hb' : m.live? p.id = some blk := hid ▸ hb
      simp only [readLimb?, hlive, hb', Option.bind_eq_bind, Option.bind_some]
      rw [extractLsb'_spliceBits_of_disjoint _ _ _ _ (by omega)]

/-- `Pointer.withOffset` in `offsetInBits` form, given the offset does not
wrap: the general shape behind `limbOffsetInBits`. -/
lemma withOffset_offsetInBits {p : Pointer} {off : BitVec 64}
    (h : p.offset.toNat + off.toNat < 2 ^ 64) :
    (p.withOffset off).offsetInBits = p.offsetInBits + 8 * off.toNat := by
  have hadd : (p.offset + off).toNat = p.offset.toNat + off.toNat := by
    rw [BitVec.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
  simp only [Pointer.withOffset, Pointer.offsetInBits, hadd]
  omega

/-- Limb `i` sits exactly `64 * i` bits into the block: the element fits, so
the offset cannot wrap. -/
lemma limbOffsetInBits {p : Pointer} (hp : p.offset.toNat + 5 * 8 ≤ 2 ^ 64) {k : ℕ}
    {off : BitVec 64} (hk : k ≤ 4) (hoff : off.toNat = 8 * k) :
    (p.withOffset off).offsetInBits = p.offsetInBits + 64 * k := by
  have hadd : (p.offset + off).toNat = p.offset.toNat + off.toNat := by
    rw [BitVec.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
  simp only [Pointer.withOffset, Pointer.offsetInBits, hadd, hoff]
  omega

/-- The five limbs behind a live block, as one opaque handle. -/
lemma exists_limbs {m : MemoryState} {p : Pointer} {blk : LiveBlock}
    (hblk : m[p.id]? = some (Block.live blk)) :
    ∃ l : Fin 5 → ℕ, ∀ i, readLimb? p i m = some (l i) :=
  ⟨fun i => (blk.bytes.extractLsb' (p.offsetInBits + 64 * i.toNat) 64).toNat, fun i => by
    simp [readLimb?, MemoryState.live?, hblk]⟩

/-- ... and what the block holds at limb `i`. The offset is a parameter, since
what a load leaves behind is only equal to `p.offsetInBits + 64 * i`, not
syntactically it. -/
lemma limbBits {m : MemoryState} {p : Pointer} {blk : LiveBlock} {l : Fin 5 → ℕ}
    (hblk : m[p.id]? = some (Block.live blk)) (hl : ∀ i, readLimb? p i m = some (l i)) (i : Fin 5)
    {off : ℕ} (hoff : off = p.offsetInBits + 64 * i.toNat) :
    blk.bytes.extractLsb' off 64 = BitVec.ofNat 64 (l i) := by
  subst hoff
  have h := hl i
  simp only [readLimb?, MemoryState.live?, hblk, Option.bind_eq_bind, Option.bind_some,
    Option.pure_def, Option.some.injEq] at h
  rw [← h, BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- The five limb stores a region ends in are the one 320-bit store the spec
makes. Proven pointwise: composing `splice_splice_append_equiv` four times says
the same thing, but leaves each step nested inside the next one's
structure-update, which does not unify in reasonable time. -/
theorem splice5_equiv {s : GlobalState} {p : Pointer} (a b c d e : BitVec 64)
    (hp : IsFieldElemPtr s.mem p) :
    ({ s with
          mem :=
            ((((s.mem.splice p a).splice (p.withOffset 8) b).splice (p.withOffset 16) c).splice
                  (p.withOffset 24) d).splice
              (p.withOffset 32) e } :
        GlobalState) ≈
      { s with mem := s.mem.splice p (e ++ d ++ c ++ b ++ a) } := by
  obtain ⟨blk, hblk, hlen⟩ := id hp.left
  simp [GlobalState.equiv_def]
  intro q
  by_cases h : p.id = q
  case neg =>
    -- an unrelated block: every splice here is at `p.id`, so none is visible.
    -- `getElem?_splice_ne` is stated over `m[_]?`, so it has to fire before
    -- `getElem?_eq` rewrites that into the underlying map lookup.
    simp only [MemoryState.live?]
    have h₄ : (p.withOffset 32#64).id ≠ q := by simp [Pointer.withOffset, h]
    have h₃ : (p.withOffset 24#64).id ≠ q := by simp [Pointer.withOffset, h]
    have h₂ : (p.withOffset 16#64).id ≠ q := by simp [Pointer.withOffset, h]
    have h₁ : (p.withOffset 8#64).id ≠ q := by simp [Pointer.withOffset, h]
    simp only [getElem?_splice_ne h₄, getElem?_splice_ne h₃, getElem?_splice_ne h₂,
      getElem?_splice_ne h₁, getElem?_splice_ne h]
  case pos =>
    simp only [MemoryState.live?]
    rw [← h]
    simp only [getElem?_splice_self (w := 320) (x := e ++ d ++ c ++ b ++ a) hblk]
    have o₁ : (p.withOffset 8#64).offsetInBits = p.offsetInBits + 64 := by
      simpa using limbOffsetInBits hp.right (k := 1) (off := 8#64) (by omega) (by simp)
    have o₂ : (p.withOffset 16#64).offsetInBits = p.offsetInBits + 128 := by
      simpa using limbOffsetInBits hp.right (k := 2) (off := 16#64) (by omega) (by simp)
    have o₃ : (p.withOffset 24#64).offsetInBits = p.offsetInBits + 192 := by
      simpa using limbOffsetInBits hp.right (k := 3) (off := 24#64) (by omega) (by simp)
    have o₄ : (p.withOffset 32#64).offsetInBits = p.offsetInBits + 256 := by
      simpa using limbOffsetInBits hp.right (k := 4) (off := 32#64) (by omega) (by simp)
    -- peel the five stores off the right-hand state, innermost first: each sees
    -- the block the previous one left. `getElem?_splice_self` states its index
    -- as `p.id`, which for a gep destination is `p.id` only after unfolding.
    have hid : ∀ off : BitVec 64, (p.withOffset off).id = p.id := fun _ => rfl
    have k₀ := getElem?_splice_self (x := a) hblk
    have k₁ := getElem?_splice_self (p := p.withOffset 8#64) (x := b) k₀
    rw [hid] at k₁
    have k₂ := getElem?_splice_self (p := p.withOffset 16#64) (x := c) k₁
    rw [hid] at k₂
    have k₃ := getElem?_splice_self (p := p.withOffset 24#64) (x := d) k₂
    rw [hid] at k₃
    have k₄ := getElem?_splice_self (p := p.withOffset 32#64) (x := e) k₃
    rw [hid] at k₄
    rw [k₄, o₁, o₂, o₃, o₄]
    simp only [Option.some.injEq, LiveBlock.mk.injEq, true_and, spliceBits_append]
    rw [show (e ++ d ++ c ++ b ++ a : BitVec (64 + 64 + 64 + 64 + 64)) = e ++ (d ++ (c ++ (b ++ a)))
        from by simp only [BitVec.append_assoc, BitVec.cast_eq]]

/-- `₀`-style index for the per-limb names the tactics below generate. -/
def subscript (i : Nat) : String :=
  (toString i).map fun c => Char.ofNat (c.toNat - '0'.toNat + '₀'.toNat)

open Lean Elab Tactic in
/-- `peel_gep_limb i, p, hp, s, x` steps the next instruction, which must be a
`getelementptr` off `p` by the constant `i`, and replaces the pointer it yields
by `x<i> := p.withOffset (8 * i)` -- substituted into the goal, so the stepper's
`v<n>`/`hv<n>` for the gep are gone afterwards. Leaves `hx<i> : Fits s.mem x<i>
_` beside it.

Assumes a five-limb field element at `p`, i.e. `hp : Fits s.mem p (5 * 64)`;
the remaining size is `(5 - i) * 64`. -/
elab "peel_gep_limb " i:num ", " p:term ", " hp:term ", " st:term ", " nm:ident : tactic => do
  let num := i.getNat
  -- `withOffset` counts bytes, `Fits` counts bits
  let offBytes := Syntax.mkNumLit (toString (num * 8))
  let remainingBits := Syntax.mkNumLit (toString ((5 - num) * 64))
  let n ← nextStepIndex (← getMainGoal)
  let nLit := Syntax.mkNumLit (toString n)
  let vBase := mkIdent (Name.mkSimple "v")
  let v := mkIdent (Name.mkSimple ("v" ++ toString n))
  let hv := mkIdent (Name.mkSimple ("hv" ++ toString n))
  let s := subscript num
  -- `nm` is the stem: the gep's result is `nm<i>`, its `Fits` is `hnm<i>`
  let base := nm.getId.eraseMacroScopes.toString
  let ptr := mkIdent (Name.mkSimple (base ++ s))
  let hptr := mkIdent (Name.mkSimple ("h" ++ base ++ s))
  evalTactic (← `(tactic| denote_step_all $vBase $nLit))
  evalTactic (← `(tactic| denote_eval $vBase $nLit $nLit))
  evalTactic (← `(tactic| let $ptr := ($p).withOffset (($offBytes) : BitVec 64)))
  evalTactic (← `(tactic| have $hptr:ident : Fits ($st).mem $ptr ($remainingBits) := by
        simpa [$ptr:ident] using remainingFits ($st).mem $p $hp ($offBytes) (by simp)))
  evalTactic (← `(tactic| have vValue : $v = .value $ptr := by
        simp [$hv:ident, gep, gepConst, ptradd, $ptr:ident, Pointer.withOffset, Ctxt.Valuation.singleton,
          LLVM.add, LLVM.mul, LLVM.const?, LLVM.add?, LLVM.mul?, simp_sllvm]))
  evalTactic (← `(tactic| subst vValue))
  evalTactic (← `(tactic| clear $hv))

open Lean Elab Tactic in
/-- `peel_limb i, p<i>, hp<i>, blk, hblk` peels the load at `p<i>`, naming its
value `limb<i>` with defining equation `hlimb<i>`.

`peel_load` needs a block hypothesis for the pointer being loaded, not for the
base pointer -- the `load` carries the whole pointer, offset included -- so this
first destructs `hp<i>` into `blk<i>`/`hblk<i>`/`hlen<i>`, stemmed from the two
names passed in, which also gives the no-trap bound directly. That block is then
identified with `blk` -- the caller's block for the base pointer, the one `hblk`
addresses -- and substituted away, so only one block name survives.

A trailing ident is the stem for the value the load produces: `x` names it
`x<i>` with equation `hx<i>`. The five-argument form below uses `limb`, so two
operands can be peeled side by side without their limbs colliding.

Expects the state `s` in scope, under that name. -/
elab "peel_limb " i:num ", " ptr:ident ", " hptr:term ", " baseblk:ident ", " basehblk:ident ", "
  nm:ident : tactic => do
  let s := subscript i.getNat
  let blk := mkIdent (Name.mkSimple (baseblk.getId.eraseMacroScopes.toString ++ s))
  let hblk := mkIdent (Name.mkSimple (basehblk.getId.eraseMacroScopes.toString ++ s))
  let hlen := mkIdent (Name.mkSimple ("hlen" ++ s))
  let base := nm.getId.eraseMacroScopes.toString
  let limb := mkIdent (Name.mkSimple (base ++ s))
  let hlimb := mkIdent (Name.mkSimple ("h" ++ base ++ s))
  let st := mkIdent (Name.mkSimple "s")
  -- byte offset of limb `i`, and the bits still left after it
  evalTactic (← `(tactic| obtain ⟨$blk, $hblk, $hlen⟩ := id $hptr))
  evalTactic (← `(tactic| peel_load (.bitvec (.concrete 64)), $blk, $ptr, $hblk, $st))
  evalTactic
      (←
        `(tactic|
            set $limb:ident := (($blk).bytes.extractLsb' ($ptr).offsetInBits 64) with $hlimb:ident))
  -- `$ptr` is a `let`-bound pointer for i > 0 and must be in the simp set to
  -- zeta-unfold; at limb 0 it is the plain fvar `p`, which simp would reject.
  if i.getNat == 0 then
    evalTactic
        (←
          `(tactic|
              have hblkeq : $baseblk = $blk := by
                simpa [Pointer.withOffset, $basehblk:ident] using $hblk))
  else
    evalTactic
        (←
          `(tactic|
              have hblkeq : $baseblk = $blk := by
                simpa [$ptr:ident, Pointer.withOffset, $basehblk:ident] using $hblk))
  evalTactic (← `(tactic| subst hblkeq))
  evalTactic (← `(tactic| clear $hblk $hlen))

/-- `peel_limb` with the default stem, naming the load's value `limb<i>`.

The stem has to be a separate syntax rather than an optional trailing group:
an optional group never matches here, it silently comes back `none` while the
tokens are consumed anyway. -/
macro "peel_limb " i:num ", " ptr:ident ", " hptr:term ", " baseblk:ident ", "
    basehblk:ident : tactic =>
  `(tactic| peel_limb $i, $ptr, $hptr, $baseblk, $basehblk, limb)

/-! Staged here while the proof is in progress; both belong in
`Ref/Proof/MemoryOperations.lean` once it is finished. -/

/-- The 32-byte buffer read is the 256-bit scalar read. -/
theorem readBuf?_eq_readWord? (p : Pointer) (m : MemoryState) : readBuf? p m = readWord? p 256 m :=
  rfl

theorem readBuf?_splice {m : MemoryState} {p : Pointer} (x : BitVec 256) (hp : Fits m p (32 * 8)) :
    readBuf? p (m.splice p x) = some x :=
  readWord?_splice_self x hp

/-- ... and the same across a callee's return, in `isByteBufPtr_of_equiv`'s
shape and for the same reason. -/
theorem readBuf_of_equiv {w s : GlobalState} {m : MemoryState} {q : Pointer}
    (he : w ≈ ({ s with mem := m } : GlobalState)) {h : IsByteBufPtr w.mem q}
    {h' : IsByteBufPtr m q} : readBuf h = readBuf h' :=
  readBuf_of_live?_eq (live?_of_equiv_mem he q.id)

theorem readBuf_splice {m : MemoryState} {p : Pointer} (x : BitVec 256) (hp : IsByteBufPtr m p) :
    readBuf (m := m.splice p x) (isByteBufPtr_splice hp) = x := by
  simp only [readBuf, readBuf?_splice x hp.left, Option.get_some]

/-- The remaining room at byte `k` of a 32-byte buffer. `peel_gep_byte` proves
this inline with `simpa`, which is the same arithmetic once per store; proved
here it is one application each. Staged; belongs beside `byteOffsetInBits`. -/
lemma byteFits {m : MemoryState} {p : Pointer} (hp : Fits m p (32 * 8)) {k : Nat} {off : BitVec 64}
    (hk : k ≤ 31) (hoff : off.toNat = k) : Fits m (p.withOffset off) (256 - k * 8) := by
  simpa [hoff] using
    remainingFits m p hp off
      (by
        rw [hoff]; omega)

open Lean Elab Tactic in
/-- `peel_gep_byte i, p, hp, s, x` is `peel_gep_limb` at byte granularity: the
gep is off `p` by the constant `i` with `elem_type = i8`, and the pointer it
yields becomes `x<i> := p.withOffset i`.

Assumes a 32-byte buffer at `p`, i.e. `hp : Fits s.mem p (32 * 8)`; the
remaining room comes from `byteFits` rather than an inline `simpa`, and the
pointer's value from a `simp only`. Inline, those two were most of the cost of
a long store chain. -/
elab "peel_gep_byte " i:num ", " p:term ", " hp:term ", " st:term ", " nm:ident : tactic => do
  let num := i.getNat
  let offBytes := Syntax.mkNumLit (toString num)
  let n ← nextStepIndex (← getMainGoal)
  let nLit := Syntax.mkNumLit (toString n)
  let vBase := mkIdent (Name.mkSimple "v")
  let v := mkIdent (Name.mkSimple ("v" ++ toString n))
  let hv := mkIdent (Name.mkSimple ("hv" ++ toString n))
  let base := nm.getId.eraseMacroScopes.toString
  let ptr := mkIdent (Name.mkSimple (base ++ subscript num))
  let hptr := mkIdent (Name.mkSimple ("h" ++ base ++ subscript num))
  evalTactic (← `(tactic| denote_step_all $vBase $nLit))
  evalTactic (← `(tactic| denote_eval $vBase $nLit $nLit))
  evalTactic (← `(tactic| let $ptr := ($p).withOffset (($offBytes) : BitVec 64)))
  evalTactic (← `(tactic| have $hptr:ident : Fits ($st).mem $ptr (256 - $offBytes * 8) :=
    byteFits $hp (k := $offBytes) (off := (($offBytes) : BitVec 64)) (by omega) (by simp)))
  evalTactic (← `(tactic| have vValue : $v = .value $ptr := by
        simp only [$hv:ident, gep, gepConst, ptradd, $ptr:ident, Pointer.withOffset,
          Ctxt.Valuation.singleton, LLVM.add, LLVM.mul, LLVM.const?, LLVM.add?,
          LLVM.mul?, simp_sllvm, BitVec.ofInt_ofNat, BitVec.ofNat_eq_ofNat,
          Nat.cast_one, Nat.cast_zero, Nat.cast_ofNat, one_mul, mul_one,
          add_zero, zero_add, BitVec.mul_one, BitVec.add_zero]))
  evalTactic (← `(tactic| subst vValue))
  evalTactic (← `(tactic| clear $hv))

/-- A limb is a 64-bit read, so it survives the round trip through `BitVec 64`
the specs' `packLimbs` witness takes. -/
theorem readLimb_lt {m : MemoryState} {p : Pointer} (i : Fin 5) (h : IsFieldElemPtr m p) :
    readLimb i h < 2 ^ 64 := by
  have hlt : ∀ l, readLimb? p i m = some l → l < 2 ^ 64 := by
    simp only [readLimb?, Option.bind_eq_bind]
    cases m.live? p.id <;> simp
    omega
  exact hlt _ (Option.some_get _).symm

/-- The total field-element read, limbwise. -/
theorem readFieldElem_eq_decode {m : MemoryState} {p : Pointer} (h : IsFieldElemPtr m p) :
    readFieldElem h = decodeFieldElem (fun i => readLimb i h) := by
  refine readFieldElem_eq_of ?_
  have hl : ∀ i, readLimb? p i m = some (readLimb i h) := fun i => (Option.some_get _).symm
  simp only [readFieldElem?, hl, Option.bind_eq_bind, Option.bind_some, Option.pure_def]
  congr 1

/-- All-zero limbs read as `0`. -/
theorem readFieldElem_of_zeroLimbs {m : MemoryState} {p : Pointer} (h : IsFieldElemPtr m p)
    (hz : ZeroLimbs p m) : readFieldElem h = 0 := by
  have hl : ∀ i, readLimb i h = 0 := fun i => by simp only [readLimb, hz i, Option.get_some]
  simp [readFieldElem_eq_decode h, decodeFieldElem, hl]

/-- A copy of `q`'s limbs spliced at `p` is all-zero only if `q`'s are. -/
theorem zeroLimbs_of_splice_readLimb {m m' : MemoryState} {p q : Pointer} (hp : Fits m p (5 * 64))
    (hq : IsFieldElemPtr m' q)
    (hz : ZeroLimbs p (m.splice p (packLimbs fun i => (readLimb i hq : BitVec 64)))) :
    ZeroLimbs q m' := fun i => by
  have h := hz i
  rw [limbReadbackPack _ _ _ hp i, Option.some.injEq] at h
  simp only [BitVec.natCast_eq_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (readLimb_lt i hq)] at h
  rw [← h]; exact (Option.some_get _).symm

/-- A limb, read as a 64-bit word at the pointer a `getelementptr` produced:
same block, `k` limbs along. This is the bridge between the walk's loads, which
are `readWord?` at the gep'd pointer, and the spec, which is `readLimb` at the
base. -/
theorem readLimb_eq_of_readWord? {m : MemoryState} {p q : Pointer} {k : Fin 5} {v : BitVec 64}
    (hp : IsFieldElemPtr m p) (hid : q.id = p.id)
    (hoff : q.offsetInBits = p.offsetInBits + 64 * k.toNat) (hv : readWord? q 64 m = some v) :
    ((readLimb k hp : ℕ) : BitVec 64) = v := by
  have hread : readLimb? p k m = some v.toNat := by
    simp only [readWord?, hid, hoff] at hv
    cases hb : m.live? p.id with
    | none =>
      rw [hb] at hv; simp at hv
    | some blk =>
      rw [hb] at hv
      simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq] at hv
      simp only [readLimb?, hb, Option.bind_eq_bind, Option.bind_some, Option.pure_def, hv]
  simp [readLimb, hread]

@[simp]
theorem withOffset_id (p : Pointer) (o : BitVec 64) : (p.withOffset o).id = p.id :=
  rfl

/-- Splicing a zero-width value changes nothing. -/
theorem spliceBits_zero {n : Nat} (bytes : BitVec n) (off : Nat) (x : BitVec 0) :
    spliceBits bytes off x = bytes := by
  have hx : x = 0#0 := by
    apply BitVec.eq_of_toNat_eq
    have := x.isLt
    omega
  subst hx
  simp [spliceBits]

theorem spliceBits_cast {n w v : Nat} (bytes : BitVec n) (off : Nat) (h : w = v) (x : BitVec w) :
    spliceBits bytes off (BitVec.cast h x) = spliceBits bytes off x := by
  subst h; rfl

/-- The memory after writing `b 0 … b (n-1)` at `p`, `p+1`, …, `p+(n-1)`. -/
def spliceBytes (m : MemoryState) (p : Pointer) (b : Nat → BitVec 8) : Nat → MemoryState
  | 0 => m
  | k + 1 => (spliceBytes m p b k).splice (p.withOffset (BitVec.ofNat 64 k)) (b k)

/-- Those bytes as one word, little-endian: byte `k` occupies bits `8*k`. -/
def packBytes (b : Nat → BitVec 8) : (n : Nat) → BitVec (8 * n)
  | 0 => 0#0
  | k + 1 => BitVec.cast (by omega) (b k ++ packBytes b k)

/-- `n` adjacent byte writes are one `8*n`-bit write. -/
theorem live?_spliceBytes {m : MemoryState} {p : Pointer} {blk : LiveBlock}
    (hb : m.live? p.id = some blk) (b : Nat → BitVec 8)
    (hoff : ∀ k, (p.withOffset (BitVec.ofNat 64 k)).offsetInBits = p.offsetInBits + 8 * k) :
    ∀ n,
      (spliceBytes m p b n).live? p.id =
        some ⟨blk.length, spliceBits blk.bytes p.offsetInBits (packBytes b n)⟩
  | 0 => by rw [spliceBytes, hb, packBytes, spliceBits_zero]
  | n + 1 => by
    have ih := live?_spliceBytes hb b hoff n
    rw [spliceBytes]
    -- the write is through an offset pointer, which addresses the same block;
    -- `rw` needs that in matching form, not merely definitionally
    show
      ((spliceBytes m p b n).splice (p.withOffset (BitVec.ofNat 64 n)) (b n)).live?
          (p.withOffset (BitVec.ofNat 64 n)).id =
        _
    rw [splicedLive _ (p.withOffset (BitVec.ofNat 64 n)) _ ih (b n), hoff n, packBytes,
      spliceBits_cast, spliceBits_append]

/-- The byte offset of byte `k`, when the buffer's end cannot wrap. -/
lemma byteOffsetInBits {p : Pointer} (hp : p.offset.toNat + 32 ≤ 2 ^ 64) {k : ℕ} {off : BitVec 64}
    (hk : k ≤ 31) (hoff : off.toNat = k) :
    (p.withOffset off).offsetInBits = p.offsetInBits + 8 * k := by
  have hadd : (p.offset + off).toNat = p.offset.toNat + off.toNat := by
    rw [BitVec.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
  simp only [Pointer.withOffset, Pointer.offsetInBits, hadd, hoff]
  omega

open Lean Elab Tactic in
/-- `peel_buf_bytes p, hp, blk, hblk, buf, hoff, hbyte` runs the byte loads a
32-byte deserialisation opens with: for `k = 31` down to `4`, the `getelementptr`
to `arg1[k]` and the load, then one rewrite of all twenty-eight loaded values to
`buf`'s bytes. Bytes `0`-`3` are left alone -- the compiler folds them into one
32-bit load.

`hoff` and `hbyte` are the two per-buffer facts the rewrite needs: the byte's
offset in bits, and what the block holds there. Each byte is followed by its
`zext`/`shl` pair, and `arg1[31]` by the `and` that masks its top bit, so the
stepper is advanced past those too.

The rewrite is deferred to one `simp only` at the end deliberately. Rewriting
byte by byte re-checks the whole `StateT.run` goal twenty-eight times, which
costs about a second each; one traversal pays that once. -/
elab "peel_buf_bytes " p:ident ", " hp:ident ", " blk:ident ", " hblk:ident ", "
    buf:ident ", " hoff:ident ", " hbyte:ident : tactic => do
  let vBase := mkIdent (Name.mkSimple "v")
  let st := mkIdent (Name.mkSimple "s")
  let mut eqs : Array Term := #[]
  let mut ptrs : Array Term := #[]
  for k' in [4:32] do
    let k := 35 - k'                       -- 31, 30, …, 4
    let kLit := Syntax.mkNumLit (toString k)
    let ptr := mkIdent (Name.mkSimple ("p" ++ subscript k))
    let hptr := mkIdent (Name.mkSimple ("hp" ++ subscript k))
    let hblkK := mkIdent (Name.mkSimple ("hblk" ++ subscript k))
    let hlenK := mkIdent (Name.mkSimple ("hlen" ++ subscript k))
    evalTactic (← `(tactic| peel_gep_byte $kLit, $p, ($hp).left, $st, p))
    -- every byte lands in the block `p` already addresses, so the load's two
    -- obligations come from `hblk`/`hoff` rather than from destructuring a fresh
    -- `Fits` -- `obtain` re-checks the whole goal, these do not
    evalTactic (← `(tactic| have $hblkK:ident : ($st).mem[($ptr).id]? = some (.live $blk) := $hblk))
    evalTactic (← `(tactic| have $hlenK:ident :
      ($ptr).offsetInBits + 8 ≤ ($blk).lengthInBits := by
        rw [$hoff:ident $kLit ($kLit : BitVec 64) (by omega) (by simp)]; omega))
    evalTactic (← `(tactic| peel_load (.bitvec (.concrete 8)), $blk, $ptr, $hblkK, $st))
    -- kept as a hypothesis, not just used and dropped: the loaded values flow
    -- into `hv<i>`, which this rewrite never reaches, so the caller needs these
    -- again to put the byte terms and the buffer in the same vocabulary
    let hbyteK := mkIdent (Name.mkSimple ("hbyte" ++ subscript k))
    -- stated over `p.withOffset k`, not the let-bound `p<k>`: the goal carries the
    -- zeta-expanded form and `simp only` will not unfold a let-bound fvar to match
    evalTactic (← `(tactic| have $hbyteK:ident :
      ($blk).bytes.extractLsb' (($p).withOffset ($kLit : BitVec 64)).offsetInBits 8
      = ($buf).extractLsb' (8 * $kLit) 8 :=
        $hbyte $kLit _ (by omega) ($hoff $kLit ($kLit : BitVec 64) (by omega) (by simp))))
    eqs := eqs.push (← `($hbyteK:ident))
    ptrs := ptrs.push (← `($ptr:ident))
    -- `arg1[31]` is masked before it is widened, so it has one more pure
    -- instruction after the load than the rest
    let extra := if k == 31 then 2 else 1
    let target := Syntax.mkNumLit (toString ((← nextStepIndex (← getMainGoal)) + extra))
    evalTactic (← `(tactic| denote_step_all $vBase $target))
  -- the pointer lets are unfolded in the same pass: here the goal still carries
  -- `p<k>`, while the equations are stated over the expanded `p.withOffset k`
  -- that the hypotheses use later
  evalTactic (← `(tactic| simp only [$[$ptrs:term],*, $[$eqs:term],*]))

open Lean Elab Tactic in
/-- `store_limbs x, p, hp, s` runs the five limb stores a region ends in: `x i`
at `p + 8 * i`, each behind its own `getelementptr`. Leaves the states as
`s<i>`, the gep'd pointers as `p<i>` -- stemmed from the two names passed in --
and `f<i> : Fits s<i>.mem p (5 * 64)`, since a store changes no block's size. -/
elab "store_limbs " x:term ", " p:ident ", " hp:term ", " st:ident : tactic => do
  let pbase := p.getId.eraseMacroScopes.toString
  let sbase := st.getId.eraseMacroScopes.toString
  evalTactic (← `(tactic| peel_store ($x 0), $p, $hp, $st))
  for i in [1:5] do
    let prevState := if i == 1 then st else mkIdent (Name.mkSimple (sbase ++ subscript (i - 1)))
    let prevPtr := if i == 1 then p else mkIdent (Name.mkSimple (pbase ++ subscript (i - 1)))
    let prevFits : Term :=
      if i == 1 then hp else mkIdent (Name.mkSimple ("f" ++ subscript (i - 1)))
    let state := mkIdent (Name.mkSimple (sbase ++ subscript i))
    let hstate := mkIdent (Name.mkSimple ("h" ++ sbase ++ subscript i))
    let fits := mkIdent (Name.mkSimple ("f" ++ subscript i))
    let ptr := mkIdent (Name.mkSimple (pbase ++ subscript i))
    let hptr := mkIdent (Name.mkSimple ("h" ++ pbase ++ subscript i))
    let iLit := Syntax.mkNumLit (toString i)
    let prevLit := Syntax.mkNumLit (toString (i - 1))
    evalTactic (← `(tactic| set $state:ident : GlobalState :=
      { $prevState with mem := ($prevState).mem.splice $prevPtr ($x $prevLit) }
      with $hstate:ident))
    evalTactic (← `(tactic| have $fits:ident : Fits ($state).mem $p (5 * 64) :=
      fits_splice $prevFits))
    evalTactic (← `(tactic| peel_gep_limb $iLit, $p, $fits, $state, $p))
    evalTactic (← `(tactic| peel_store ($x $iLit), $ptr, $hptr, $state))

/-- `skip_lifetime` steps the next instruction, which must be a lifetime
marker. It moves neither state nor valuation, so it takes no arguments. -/
macro "skip_lifetime" : tactic => `(tactic| rw [BlockCom.run_bind_denote_lifetime])

end Firedancer.Ref
