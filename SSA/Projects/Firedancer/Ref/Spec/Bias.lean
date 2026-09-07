/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.Firedancer.Ref.Spec.F25519

/-!
# The bias limbs

`fiat_25519_sub` and `fiat_25519_opp` both start from `2 · p` written
limbwise -- `sub` adds it to the minuend before subtracting, `opp` uses it as
the minuend -- so the two agree limb by limb:

    bias = ⟨0xfffffffffffda, 0xffffffffffffe, 0xffffffffffffe,
            0xffffffffffffe, 0xffffffffffffe⟩

That is what makes `sub` safe on an `opp` result. `opp` leaves limb `i` at
most `bias i`, and `sub` subtracts limb `i` from `bias i + minuend i`, so
nothing underflows. The *uniform* bound `LimbBounds h 0xffffffffffffe` is too
weak to see it: it allows limb 0 to be 36 above `sub`'s `0xfffffffffffda`, and
then the limb really would wrap. Hence a per-limb bound.
-/

namespace Firedancer.Ref
open LeanMLIR SLLVM

def biasLimb : Fin 5 → ℕ :=
  ![0xfffffffffffda, 0xffffffffffffe, 0xffffffffffffe, 0xffffffffffffe, 0xffffffffffffe]

@[simp] theorem biasLimb_zero : biasLimb 0 = 0xfffffffffffda := rfl
@[simp] theorem biasLimb_one : biasLimb 1 = 0xffffffffffffe := rfl
@[simp] theorem biasLimb_two : biasLimb 2 = 0xffffffffffffe := rfl
@[simp] theorem biasLimb_three : biasLimb 3 = 0xffffffffffffe := rfl
@[simp] theorem biasLimb_four : biasLimb 4 = 0xffffffffffffe := rfl

/-- The tight bound is below every bias limb, so a carried element is one. -/
theorem tight_le_biasLimb (i : Fin 5) : (0x8000000000000 : ℕ) ≤ biasLimb i := by
  fin_cases i <;> norm_num [biasLimb]

/-- ... and every bias limb is below the uniform bound the `opp` spec used to
state, so the weaker fact is still available. -/
theorem biasLimb_le (i : Fin 5) : biasLimb i ≤ 0xffffffffffffe := by
  fin_cases i <;> norm_num [biasLimb]

/-- The value a limb vector denotes, before reduction.

Kept as a *definition* rather than written out: it is a hypothesis of
`fiat_25519_to_bytes_conforms`, so it sits in the context for the whole of that
walk, and spelled out it would hand every later `omega` a constraint with
`2 ^ 204` coefficients. Folded, `omega` sees one atom and ignores it. -/
def limbSum {m : MemoryState} {q : Pointer} (h : IsFieldElemPtr m q) : ℕ :=
  readLimb 0 h + 2 ^ 51 * readLimb 1 h + 2 ^ 102 * readLimb 2 h + 2 ^ 153 * readLimb 3 h
    + 2 ^ 204 * readLimb 4 h

/-- ... unfolded where the canonicalisation actually needs the digits. -/
theorem limbSum_eq {m : MemoryState} {q : Pointer} (h : IsFieldElemPtr m q) :
    limbSum h = readLimb 0 h + 2 ^ 51 * readLimb 1 h + 2 ^ 102 * readLimb 2 h
      + 2 ^ 153 * readLimb 3 h + 2 ^ 204 * readLimb 4 h := rfl

/-- A carried element is below `2 · p`, so the tight bound implies the sum
bound `fiat_25519_to_bytes` needs. -/
theorem limbSum_lt_of_limbBounds {m : MemoryState} {q : Pointer} {h : IsFieldElemPtr m q}
    (hb : LimbBounds h) : limbSum h < 2 ^ 256 - 38 := by
  have h0 := hb 0; have h1 := hb 1; have h2 := hb 2; have h3 := hb 3; have h4 := hb 4
  simp only [limbSum]
  omega

/-- Both halves of `fiat_25519_to_bytes`'s precondition look only at the block
the pointer addresses, so both survive a step that left it alone. -/
theorem limbSum_of_live?_eq {m m' : MemoryState} {q : Pointer}
    (hl : m'.live? q.id = m.live? q.id) {h : IsFieldElemPtr m q} {h' : IsFieldElemPtr m' q} :
    limbSum h' = limbSum h := by
  simp only [limbSum, readLimb, readLimb?, hl]

/-- Limb `i` at most `biasLimb i`: what `fiat_25519_opp` leaves, and the most
`fiat_25519_sub` can take as subtrahend. -/
abbrev BiasBounds {m : MemoryState} {q : Pointer} (h : IsFieldElemPtr m q) : Prop :=
  ∀ i, readLimb i h ≤ biasLimb i

/-- The `readLimb?`-shaped form, as the conformance lemmas take their bounds. -/
abbrev BiasBounds? (q : Pointer) (m : MemoryState) : Prop :=
  ∀ (i : Fin 5) (l : ℕ), readLimb? q i m = some l → l ≤ biasLimb i

theorem biasBounds_readLimb? {m : MemoryState} {q : Pointer} (h : IsFieldElemPtr m q)
    (hb : BiasBounds h) : BiasBounds? q m := by
  intro i l hl
  have : l = readLimb i h := by
    simp only [readLimb, Option.get_of_eq_some _ hl]
  exact this ▸ hb i

theorem biasBounds_of_readLimb? {m : MemoryState} {q : Pointer} (h : IsFieldElemPtr m q)
    (hb : BiasBounds? q m) : BiasBounds h :=
  fun i => hb i _ (Option.some_get _).symm

/-- A carried element meets the bias bound. -/
theorem LimbBounds.bias {m : MemoryState} {q : Pointer} {h : IsFieldElemPtr m q}
    (hb : LimbBounds h) : BiasBounds h :=
  fun i => (hb i).trans (tight_le_biasLimb i)

/-- ... in the `readLimb?` form. -/
theorem biasBounds?_of_limbBounds {m : MemoryState} {q : Pointer}
    (hb : ∀ (i : Fin 5) (l : ℕ), readLimb? q i m = some l → l ≤ 0x8000000000000) :
    BiasBounds? q m :=
  fun i l hl => (hb i l hl).trans (tight_le_biasLimb i)

/-- The bias bound implies the uniform one the `opp`/`neg` specs used. -/
theorem biasBounds?_le {m : MemoryState} {q : Pointer} (hb : BiasBounds? q m) :
    ∀ (i : Fin 5) (l : ℕ), readLimb? q i m = some l → l ≤ 0xffffffffffffe :=
  fun i l hl => (hb i l hl).trans (biasLimb_le i)

/-- ... and the per-limb bound likewise. -/
theorem biasBounds_of_live?_eq {m m' : MemoryState} {q : Pointer}
    (hl : m'.live? q.id = m.live? q.id) {h : IsFieldElemPtr m q} {h' : IsFieldElemPtr m' q}
    (hb : BiasBounds h) : BiasBounds h' :=
  biasBounds_of_readLimb? h' fun i l hli =>
    biasBounds_readLimb? h hb i l (by simpa only [readLimb?, hl] using hli)

/-- The limb sum *is* the field element, before reduction. -/
theorem readFieldElem_eq_limbSum {m : MemoryState} {q : Pointer} (h : IsFieldElemPtr m q) :
    readFieldElem h = ((limbSum h : ℕ) : ZMod p) := by
  obtain ⟨l, hl⟩ : ∃ l : Fin 5 → ℕ, ∀ i, readLimb? q i m = some (l i) :=
    ⟨fun i => (readLimb? q i m).get (readLimb?_isSome i h), fun i => (Option.some_get _).symm⟩
  have hr : ∀ i, readLimb i h = l i := fun i => by simp only [readLimb, hl i, Option.get_some]
  have hfe : readFieldElem h = decodeFieldElem ![l 0, l 1, l 2, l 3, l 4] := by
    simp only [readFieldElem, readFieldElem?, hl, Option.pure_def, Option.bind_eq_bind,
      Option.bind_some, Option.get_some]
  rw [hfe, limbSum]
  simp only [hr, decodeFieldElem, Fin.isValue, Fin.toNat]
  push_cast
  norm_num
  ring

theorem limbSum_le_of_biasBounds {m : MemoryState} {q : Pointer} {h : IsFieldElemPtr m q}
    (hb : BiasBounds h) : limbSum h ≤ 2 ^ 256 - 38 := by
  have h0 : readLimb 0 h ≤ 4503599627370458 := hb 0
  have h1 : readLimb 1 h ≤ 4503599627370494 := hb 1
  have h2 : readLimb 2 h ≤ 4503599627370494 := hb 2
  have h3 : readLimb 3 h ≤ 4503599627370494 := hb 3
  have h4 : readLimb 4 h ≤ 4503599627370494 := hb 4
  simp only [limbSum]
  omega

theorem limbSum_lt_of_biasBounds {m : MemoryState} {q : Pointer} {h : IsFieldElemPtr m q}
    (hb : BiasBounds h) (hne : readFieldElem h ≠ 0) : limbSum h < 2 ^ 256 - 38 := by
  rcases lt_or_eq_of_le (limbSum_le_of_biasBounds hb) with h' | h'
  · exact h'
  · exact absurd (by rw [readFieldElem_eq_limbSum, h']; decide) hne


/-- ... and a bias-bounded element is a loose one, which is the bound
`fiat_25519_carry_mul` / `carry_square` take. -/
theorem BiasBounds.loose {m : MemoryState} {q : Pointer} {h : IsFieldElemPtr m q}
    (hb : BiasBounds h) : LimbBounds.Loose h :=
  fun i => le_trans (hb i) (le_trans (biasLimb_le i) (by norm_num))

end Firedancer.Ref
