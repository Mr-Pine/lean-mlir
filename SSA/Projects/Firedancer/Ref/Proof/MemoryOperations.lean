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
    ({ s with mem := (s.mem.splice p x).splice p y } : GlobalState)
      ≈ { s with mem := s.mem.splice p y } := by
  refine ⟨rfl, fun q => ?_⟩
  by_cases hq : p.id = q
  · subst hq
    cases hb : s.mem.live? p.id with
    | none => rw [splicedDead (splicedDead hb), splicedDead hb]
    | some b =>
      rw [splicedLive _ _ _ (splicedLive _ _ _ hb x), splicedLive _ _ _ hb,
        spliceBits_spliceBits_self]
  · rw [live?_splice_ne hq, live?_splice_ne hq, live?_splice_ne hq]

@[simp_sllvm]
theorem fits_equiv {s s' : GlobalState} {p : Pointer} {n: Nat}
    (hs: s ≈ s') (h : Fits s.mem p n) : Fits s'.mem p n := by
  obtain ⟨block, hblk, hlen⟩ := h
  simp only [GlobalState.equiv_def] at hs
  have block_equiv := hs.right p.id
  simp only [MemoryState.live?, hblk] at block_equiv
  -- `live?` is a `match`, so `block_equiv` is one too; splitting it names the
  -- branch and hands over the scrutinee's equation, which is the lookup wanted.
  replace block_equiv : s'.mem[p.id]? = some (Block.live block) := by
    split at block_equiv <;> simp_all
  exact ⟨block, block_equiv, hlen⟩

lemma extractLimb (q b c d e : BitVec 64) (i : Fin 5) :
    (e ++ d ++ c ++ b ++ q).extractLsb' (64 * i.toNat) 64 = ![q, b, c, d, e] i := by
  fin_cases i <;> simp <;> bv_decide

lemma limbReadback (m : MemoryState) (p : Pointer) (a b c d e : BitVec 64)
    (hp : Fits m p 320) (i : Fin 5) :
    readLimb? p i (m.splice p (e ++ d ++ c ++ b ++ a))
      = .some (![a, b, c, d, e] i).toNat := by
  obtain ⟨blk, hblk, hfits⟩ := hp
  have hb : m.live? p.id = .some blk := by simp [MemoryState.live?, hblk]
  have hi : i.toNat < 5 := i.isLt
  simp only [readLimb?, splicedLive m p blk hb _, Option.bind_eq_bind, Option.bind_some,
    Option.pure_def]
  rw [extractLsb'_spliceBits_of_subrange _ _ _ _ (by omega) (by omega) hfits,
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
  rw [extractLsb'_spliceBits_of_subrange _ _ _ _ (by omega) (by omega) hfits,
    Nat.add_sub_cancel_left]

/-- Limb `i` sits exactly `64 * i` bits into the block: the element fits, so
the offset cannot wrap. -/
lemma limbOffsetInBits {p : Pointer} (hp : p.offset.toNat + 5 * 8 ≤ 2 ^ 64)
    {k : ℕ} {off : BitVec 64} (hk : k ≤ 4) (hoff : off.toNat = 8 * k) :
    (p.withOffset off).offsetInBits = p.offsetInBits + 64 * k := by
  have hadd : (p.offset + off).toNat = p.offset.toNat + off.toNat := by
    rw [BitVec.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
  simp only [Pointer.withOffset, Pointer.offsetInBits, hadd, hoff]
  omega

/-- The five limbs behind a live block, as one opaque handle. -/
lemma exists_limbs {m : MemoryState} {p : Pointer} {blk : LiveBlock}
    (hblk : m[p.id]? = some (Block.live blk)) :
    ∃ l : Fin 5 → ℕ, ∀ i, readLimb? p i m = some (l i) :=
  ⟨fun i => (blk.bytes.extractLsb' (p.offsetInBits + 64 * i.toNat) 64).toNat,
    fun i => by simp [readLimb?, MemoryState.live?, hblk]⟩

/-- ... and what the block holds at limb `i`. The offset is a parameter, since
what a load leaves behind is only equal to `p.offsetInBits + 64 * i`, not
syntactically it. -/
lemma limbBits {m : MemoryState} {p : Pointer} {blk : LiveBlock} {l : Fin 5 → ℕ}
    (hblk : m[p.id]? = some (Block.live blk)) (hl : ∀ i, readLimb? p i m = some (l i))
    (i : Fin 5) {off : ℕ} (hoff : off = p.offsetInBits + 64 * i.toNat) :
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
    ({ s with mem := ((((s.mem.splice p a).splice (p.withOffset 8) b).splice
        (p.withOffset 16) c).splice (p.withOffset 24) d).splice (p.withOffset 32) e }
      : GlobalState)
      ≈ { s with mem := s.mem.splice p (e ++ d ++ c ++ b ++ a) } := by
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
    rw [show (e ++ d ++ c ++ b ++ a : BitVec (64 + 64 + 64 + 64 + 64))
        = e ++ (d ++ (c ++ (b ++ a))) from by simp only [BitVec.append_assoc, BitVec.cast_eq]]

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
        simpa using remainingFits ($st).mem $p $hp ($offBytes) (by simp)))
  evalTactic (← `(tactic| have vValue : $v = .value $ptr := by
        simp [$hv:ident, gep, ptradd, $ptr:ident, Pointer.withOffset, Ctxt.Valuation.singleton,
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
elab "peel_limb " i:num ", " ptr:ident ", " hptr:term ", " baseblk:ident ", "
    basehblk:ident ", " nm:ident : tactic => do
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
  evalTactic (← `(tactic| set $limb:ident := (($blk).bytes.extractLsb' ($ptr).offsetInBits 64) with $hlimb:ident))
  -- `$ptr` is a `let`-bound pointer for i > 0 and must be in the simp set to
  -- zeta-unfold; at limb 0 it is the plain fvar `p`, which simp would reject.
  if i.getNat == 0 then
    evalTactic (← `(tactic| have hblkeq : $baseblk = $blk := by
        simpa [Pointer.withOffset, $basehblk:ident] using $hblk))
  else
    evalTactic (← `(tactic| have hblkeq : $baseblk = $blk := by
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
macro "skip_lifetime" : tactic =>
  `(tactic| rw [BlockCom.run_bind_denote_lifetime])

end Firedancer.Ref
