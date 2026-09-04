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

end Firedancer.Ref
