import SSA.Projects.Firedancer.Limbs
import SSA.Projects.Firedancer.Ed25519
import Mathlib.Tactic.Ring
import Mathlib.Tactic.IntervalCases

/-!
# The `fd_r43x6_t` representation

A GF(2^255-19) element as six radix-`2^43` limbs in lanes 0-5 of an AVX-512
vector; lanes 6 and 7 are ignored. This file fixes `LimbRepresentations` at
`limbWidth = 64`, `baseBits = 43`, `limbCount = 6`, and adds the vocabulary of
the representation table in `fd_r43x6.h`.

Both levels of `LimbRepresentations` are in use. The multiply-like operations
never leave the vector, so they are stated with `decode'` and the bounds. The
serial carry macros begin with `fd_r43x6_extract_limbs` and are scalar `long`
code from there, with intermediates far outside the range of a limb, so they
are stated over limb functions.
-/

namespace R43x6

abbrev limbWidth :=
  64

abbrev baseBits :=
  43

abbrev limbCount :=
  6

/-! ## Limbs by index -/

/-- The value six radix-`2^43` limbs represent: `ℕ` limbs for the
multiply-like column sums, `ℤ` limbs for the signed carry chains. -/
def decodeLimbs {R : Type*} [CommSemiring R] (l : Fin limbCount → R) : R :=
  LimbRepresentations.decodeFn baseBits l

/-- `decodeLimbs` with the weights as literals, which is the form `omega` and
`ring` need. -/
@[simp]
theorem decodeLimbs_eq {R : Type*} [CommSemiring R] (l : Fin limbCount → R) :
    decodeLimbs l =
      l 0 + 2 ^ 43 * l 1 + 2 ^ 86 * l 2 + 2 ^ 129 * l 3 + 2 ^ 172 * l 4 + 2 ^ 215 * l 5 := by
  simp [decodeLimbs, LimbRepresentations.decodeFn, Fin.sum_univ_six]
  ring

/-- The limb function with the given six limbs. The carry macros return their
results in this form. -/
def limbs6 {R : Type*} (a b c d e f : R) : Fin limbCount → R := fun i =>
  match (i : ℕ) with
  | 0 => a
  | 1 => b
  | 2 => c
  | 3 => d
  | 4 => e
  | _ => f

/-- `limbs6` at each index. Unfolding `limbs6` instead leaves a `match` on `(i : ℕ)` that no
longer reduces at a literal `Fin`, and `omega` then sees the whole chain as opaque. -/
@[simp]
theorem limbs6_zero {R : Type*} (a b c d e f : R) : limbs6 a b c d e f 0 = a :=
  rfl

@[simp]
theorem limbs6_one {R : Type*} (a b c d e f : R) : limbs6 a b c d e f 1 = b :=
  rfl

@[simp]
theorem limbs6_two {R : Type*} (a b c d e f : R) : limbs6 a b c d e f 2 = c :=
  rfl

@[simp]
theorem limbs6_three {R : Type*} (a b c d e f : R) : limbs6 a b c d e f 3 = d :=
  rfl

@[simp]
theorem limbs6_four {R : Type*} (a b c d e f : R) : limbs6 a b c d e f 4 = e :=
  rfl

@[simp]
theorem limbs6_five {R : Type*} (a b c d e f : R) : limbs6 a b c d e f 5 = f :=
  rfl

/-- ... and at the `Fin.mk` indices `fin_cases` produces. -/
@[simp]
theorem limbs6_mk_zero {R : Type*} (a b c d e f : R) (h) : limbs6 a b c d e f ⟨0, h⟩ = a :=
  rfl

@[simp]
theorem limbs6_mk_one {R : Type*} (a b c d e f : R) (h) : limbs6 a b c d e f ⟨1, h⟩ = b :=
  rfl

@[simp]
theorem limbs6_mk_two {R : Type*} (a b c d e f : R) (h) : limbs6 a b c d e f ⟨2, h⟩ = c :=
  rfl

@[simp]
theorem limbs6_mk_three {R : Type*} (a b c d e f : R) (h) : limbs6 a b c d e f ⟨3, h⟩ = d :=
  rfl

@[simp]
theorem limbs6_mk_four {R : Type*} (a b c d e f : R) (h) : limbs6 a b c d e f ⟨4, h⟩ = e :=
  rfl

@[simp]
theorem limbs6_mk_five {R : Type*} (a b c d e f : R) (h) : limbs6 a b c d e f ⟨5, h⟩ = f :=
  rfl

@[simp]
theorem decodeLimbs_limbs6 {R : Type*} [CommSemiring R] (a b c d e f : R) :
    decodeLimbs (limbs6 a b c d e f) =
      a + 2 ^ 43 * b + 2 ^ 86 * c + 2 ^ 129 * d + 2 ^ 172 * e + 2 ^ 215 * f := by
  simp [limbs6_zero, limbs6_one, limbs6_two, limbs6_three, limbs6_four, limbs6_five]

/-- The range of a C `long`, `[-2^63, 2^63)`. Every intermediate of the serial
carry macros has to stay inside it: the emitted code marks the arithmetic
`nsw`, so an overflow denotes as poison rather than as a wrong value. -/
def FitsLong (v : ℤ) : Prop :=
  -2 ^ 63 ≤ v ∧ v < 2 ^ 63

/-- `ashr` by `n` is floor division by `2^n`, which is what `>>>` already
means on `ℤ`. Every proof about the carry macros opens by rewriting with this,
because `omega` handles division by a literal but not `>>>`. -/
theorem shiftRight_eq (a : ℤ) (n : ℕ) : a >>> n = a / 2 ^ n := by
  rw [Int.shiftRight_eq_div_pow]; push_cast; ring

/-! ## Limbs in a vector -/

/-- `fd_r43x6_extract_limbs`: lanes 0-5 as signed limbs. -/
def extractLimbs (x : Vector (BitVec 64) 8) : Fin limbCount → ℤ := fun i =>
  LimbRepresentations.toInts x (i.castLE (by decide))

/-- The value an `fd_r43x6_t` represents. -/
def decode' (x : LimbRepresentations.Limbs 64 8) : ℤ :=
  LimbRepresentations.decode limbWidth baseBits limbCount (x.take limbCount)

/-- Reading the first six lanes as limbs is `extractLimbs`. -/
theorem toInts_take (x : Vector (BitVec 64) 8) (i : Fin limbCount) :
    LimbRepresentations.toInts (x.take limbCount) i = extractLimbs x i := by
  simp only [LimbRepresentations.toInts, extractLimbs, Fin.val_castLE]
  congr 1
  rw [Vector.getElem_take]

/-- The extracted limbs decode to the value of the vector. Every statement a
macro makes about limbs reaches the vector through this. -/
@[simp]
theorem decodeLimbs_extractLimbs (x : Vector (BitVec 64) 8) :
    decodeLimbs (extractLimbs x) = decode' x := by
  simp only [decode', LimbRepresentations.decode, decodeLimbs]
  congr 1
  funext i
  rw [toInts_take]

/-- `decode'` written out: the low six lanes with radix-`2^43` weights. -/
theorem decode'_eq (x : Vector (BitVec 64) 8) :
    decode' x =
      x[0].toInt + 2 ^ 43 * x[1].toInt + 2 ^ 86 * x[2].toInt + 2 ^ 129 * x[3].toInt +
        2 ^ 172 * x[4].toInt +
        2 ^ 215 * x[5].toInt := by
  rw [← decodeLimbs_extractLimbs, decodeLimbs_eq]; rfl

/-! ## The representation classes of the `fd_r43x6.h` table

A bound on a vector is a bound on its limbs read as integers. `unn` and `snn`
are the header's names for limbs in `[0, 2^nn)` and in `(-2^nn, 2^nn)`.

`nearly reduced` and `reduced` bound the packed value as well as the limbs,
and the packed bound is the part that does the work: it is why the conditional
subtract in `fd_r43x6_mod_nearly_reduced_limbs` is a single subtraction, and
why a reduced representation is unique. -/

abbrev BoundedUpper {l : Nat} (u : Int) (x : Vector (BitVec 64) l) : Prop :=
  LimbRepresentations.BoundedUpper u (LimbRepresentations.toInts x)

abbrev BoundedLower {l : Nat} (lo : Int) (x : Vector (BitVec 64) l) : Prop :=
  LimbRepresentations.BoundedLower lo (LimbRepresentations.toInts x)

abbrev UNN {l : Nat} (nn : Nat) (x : Vector (BitVec 64) l) :=
  BoundedUpper (2 ^ nn - 1) x ∧ BoundedLower 0 x

abbrev SNN {l : Nat} (nn : Nat) (x : Vector (BitVec 64) l) :=
  BoundedUpper (2 ^ nn - 1) x ∧ BoundedLower (-(2 ^ nn - 1)) x

abbrev U44 {l} :=
  @UNN l 44

abbrev U45 {l} :=
  @UNN l 45

abbrev U46 {l} :=
  @UNN l 46

abbrev U47 {l} :=
  @UNN l 47

abbrev U61 {l} :=
  @UNN l 61

abbrev U62 {l} :=
  @UNN l 62

abbrev U63 {l} :=
  @UNN l 63

abbrev S62 {l} :=
  @SNN l 62

abbrev Unreduced {l} :=
  @U47 l

/-- `unpacked`: limbs 0-4 in `[0,2^43)`, limb 5 in `[0,2^41)`, with no bound on
the value. What `fd_r43x6_unpack` returns and what `fd_r43x6_pack` accepts. -/
def Unpacked (x : Vector (BitVec 64) 8) : Prop :=
  (∀ i : Fin limbCount, (i : ℕ) < 5 → 0 ≤ extractLimbs x i ∧ extractLimbs x i < 2 ^ 43) ∧
    (0 ≤ extractLimbs x 5 ∧ extractLimbs x 5 < 2 ^ 41)

def NearlyReduced (x : Vector (BitVec 64) 8) : Prop :=
  (∀ i : Fin limbCount, (i : ℕ) < 5 → 0 ≤ extractLimbs x i ∧ extractLimbs x i < 2 ^ 43) ∧
    (0 ≤ extractLimbs x 5 ∧ extractLimbs x 5 < 2 ^ 41) ∧ decode' x < 2 * (p : ℤ)

def Reduced (x : Vector (BitVec 64) 8) : Prop :=
  (∀ i : Fin limbCount, (i : ℕ) < 5 → 0 ≤ extractLimbs x i ∧ extractLimbs x i < 2 ^ 43) ∧
    (0 ≤ extractLimbs x 5 ∧ extractLimbs x 5 < 2 ^ 40) ∧ decode' x < (p : ℤ)

/-- `reduced ⊆ nearly reduced`, as the header's table says. -/
theorem Reduced.nearlyReduced {x : Vector (BitVec 64) 8} (h : Reduced x) : NearlyReduced x := by
  obtain ⟨h04, ⟨h50, h51⟩, hs⟩ := h
  exact
    ⟨h04, ⟨h50, by omega⟩, by
      have := p_pos; omega⟩

/-- `nearly reduced ⊆ unpacked`, as the header's table says. -/
theorem NearlyReduced.unpacked {x : Vector (BitVec 64) 8} (h : NearlyReduced x) : Unpacked x :=
  ⟨h.1, h.2.1⟩

/-- A two-sided bound on the six limb lanes, as a bound on `extractLimbs`.
How an `snn` or `unn` contract on an `fd_r43x6_t` reaches the macros, which
see limbs rather than lanes. -/
theorem extractLimbs_bounds {u lo : ℤ} {x : Vector (BitVec 64) 8}
    (h : BoundedUpper u (x.take limbCount) ∧ BoundedLower lo (x.take limbCount))
    (i : Fin limbCount) : lo ≤ extractLimbs x i ∧ extractLimbs x i ≤ u := by
  obtain ⟨hu, hl⟩ := h
  have hu' := hu i
  have hl' := hl i
  rw [toInts_take] at hu' hl'
  exact ⟨hl', hu'⟩

/-! ## From limb bounds to the value

The carry macros return bounds on limbs; these three turn such a bound into a
statement about the value the limbs decode to. They take the bounds as
hypotheses rather than a representation class, because the limbs a macro
returns need not be in any class of the table. -/

/-- Non-negative limbs decode to a non-negative value. -/
theorem decodeLimbs_nonneg {l : Fin limbCount → ℤ}
    (h04 : ∀ i : Fin limbCount, (i : ℕ) < 5 → 0 ≤ l i) (h5 : 0 ≤ l 5) : 0 ≤ decodeLimbs l := by
  have := h04 0 (by decide); have := h04 1 (by decide); have := h04 2 (by decide)
  have := h04 3 (by decide); have := h04 4 (by decide)
  simp only [decodeLimbs_eq]; omega

/-- Limbs 0-4 below `2^43` and limb 5 below `2^40 + 2^21 - 1` decode to less
than `2p`. Those are the bounds `fd_r43x6_biased_carry_propagate_limbs`
returns at `b = 2^20`; the largest value they admit is
`2^255 + 2^236 - 2^215 - 1`, against `2p = 2^256 - 38`. -/
theorem decodeLimbs_lt_two_p {l : Fin limbCount → ℤ}
    (h04 : ∀ i : Fin limbCount, (i : ℕ) < 5 → 0 ≤ l i ∧ l i < 2 ^ 43) (h50 : 0 ≤ l 5)
    (h51 : l 5 < 2 ^ 40 + 2 ^ 21 - 1) : decodeLimbs l < 2 * (p : ℤ) := by
  have := h04 0 (by decide); have := h04 1 (by decide); have := h04 2 (by decide)
  have := h04 3 (by decide); have := h04 4 (by decide)
  simp only [decodeLimbs_eq, p_int]; omega

/-- On limbs in the `reduced` widths, the value is zero exactly when every
limb is zero -- which is what `!!(l0|l1|l2|l3|l4|l5)` reads. The bounds are
needed: a redundant representation can have non-zero limbs and decode to zero.
Limb 5 needs no bound, since limbs 0-4 cannot reach `2^215` between them. -/
theorem decodeLimbs_eq_zero_iff {l : Fin limbCount → ℤ}
    (h04 : ∀ i : Fin limbCount, (i : ℕ) < 5 → 0 ≤ l i ∧ l i < 2 ^ 43) :
    decodeLimbs l = 0 ↔ (l 0 = 0 ∧ l 1 = 0 ∧ l 2 = 0 ∧ l 3 = 0 ∧ l 4 = 0 ∧ l 5 = 0) := by
  have := h04 0 (by decide); have := h04 1 (by decide); have := h04 2 (by decide)
  have := h04 3 (by decide); have := h04 4 (by decide)
  simp only [decodeLimbs_eq]; omega

end R43x6
