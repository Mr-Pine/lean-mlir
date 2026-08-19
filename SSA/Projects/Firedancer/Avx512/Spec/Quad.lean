/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.Firedancer.Avx512.Spec.Common

/-!
# The `FD_R43X6_QUAD` layout

`fd_r43x6_quad_mul_fast` and `fd_r43x6_quad_sqr_fast` operate on a
`FD_R43X6_QUAD`: *four* field elements held transposed across three 8-lane
vectors. Writing the four elements `X`, `Y`, `Z`, `T` (the names
`fd_r43x6_inl.h` uses, after the four coordinates of a curve point) and `Vk`
for limb `k` of element `V`:

    a = x03 = [ X0 Y0 Z0 T0 | X3 Y3 Z3 T3 ]
    b = x14 = [ X1 Y1 Z1 T1 | X4 Y4 Z4 T4 ]
    c = x25 = [ X2 Y2 Z2 T2 | X5 Y5 Z5 T5 ]

So *lane* `j < 4` selects the element and the *vector plus half* selects the
limb: element `j` has limbs `(a[j], b[j], c[j], a[j+4], b[j+4], c[j+4])`.

Unlike the scalar `fd_r43x6_t`, a QUAD has no ignored lanes — all eight lanes
of all three vectors carry limbs. That is why the quad kernels need no
"lanes 6 and 7 are zero" hypothesis: every product the implementation forms
stays inside one lane `j`, so the four multiplications never mix.

`quadLimb` reads an element out of that layout and `quadVec` writes the
predicted results back into it. Between them, `quadLimb_quadVec` says the
round trip is the identity, which is what lets the quad specifications reuse
the scalar `Spec/fd_r43x6_mul_fast.lean` and `Spec/fd_r43x6_sqr_fast.lean`
column sums unchanged: a quad kernel is exactly four scalar kernels.
-/

namespace Firedancer.Avx512
open LeanMLIR SLLVM
open InstCombine (LLVM)

/-- Lane `i` of an 8-lane vector as a natural, junk (`0`) out of range. The
`limbNat` of `Spec/Common.lean` reads only the six limb lanes of a scalar
`fd_r43x6_t`; a QUAD uses all eight. -/
def vlane (v : Vector (BitVec 64) 8) : ℕ → ℕ
  | 0 => v[0].toNat
  | 1 => v[1].toNat
  | 2 => v[2].toNat
  | 3 => v[3].toNat
  | 4 => v[4].toNat
  | 5 => v[5].toNat
  | 6 => v[6].toNat
  | 7 => v[7].toNat
  | _ => 0

/-- The limb function of the field element in lane `j` of the QUAD `(a,b,c)`,
in the `ℕ → ℕ` form `pack` and the column sums take. -/
def quadLimb (a b c : Vector (BitVec 64) 8) (j : ℕ) : ℕ → ℕ
  | 0 => vlane a j
  | 1 => vlane b j
  | 2 => vlane c j
  | 3 => vlane a (j + 4)
  | 4 => vlane b (j + 4)
  | 5 => vlane c (j + 4)
  | _ => 0

/-- One output vector of a quad kernel: given the four elements' limbs
`l j k`, the vector holding limb `m` of each element in lanes 0-3 and limb `n`
in lanes 4-7. The three results are `quadVec l 0 3`, `quadVec l 1 4` and
`quadVec l 2 5`. -/
def quadVec (l : ℕ → ℕ → ℕ) (m n : ℕ) : Vector (BitVec 64) 8 :=
  #v[BitVec.ofNat 64 (l 0 m), BitVec.ofNat 64 (l 1 m),
     BitVec.ofNat 64 (l 2 m), BitVec.ofNat 64 (l 3 m),
     BitVec.ofNat 64 (l 0 n), BitVec.ofNat 64 (l 1 n),
     BitVec.ofNat 64 (l 2 n), BitVec.ofNat 64 (l 3 n)]

/-! ## Round trip

Reading the three predicted output vectors back through the QUAD layout
recovers the limbs that were written, provided none is truncated by the
64-bit lane. -/

/-- Each lane of `quadVec` is the `BitVec.ofNat` of the limb it was built
from. -/
theorem vlane_quadVec (l : ℕ → ℕ → ℕ) (m n : ℕ) (j : ℕ) (hj : j < 4) :
    vlane (quadVec l m n) j = (BitVec.ofNat 64 (l j m)).toNat
      ∧ vlane (quadVec l m n) (j + 4) = (BitVec.ofNat 64 (l j n)).toNat := by
  interval_cases j <;> exact ⟨rfl, rfl⟩

/-- **Round trip.** The QUAD assembled from the three predicted vectors reads
back as the limbs it was built from, as long as every limb fits a lane. -/
theorem quadLimb_quadVec (l : ℕ → ℕ → ℕ) (j : ℕ) (hj : j < 4) (k : ℕ) (hk : k < 6)
    (hb : ∀ i < 4, ∀ k' < 6, l i k' < 2 ^ 64) :
    quadLimb (quadVec l 0 3) (quadVec l 1 4) (quadVec l 2 5) j k = l j k := by
  have red : ∀ i < 4, ∀ k' < 6, (BitVec.ofNat 64 (l i k')).toNat = l i k' := by
    intro i hi k' hk'
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by simpa using hb i hi k' hk')
  interval_cases k
  · exact (vlane_quadVec l 0 3 j hj).1.trans (red j hj 0 (by omega))
  · exact (vlane_quadVec l 1 4 j hj).1.trans (red j hj 1 (by omega))
  · exact (vlane_quadVec l 2 5 j hj).1.trans (red j hj 2 (by omega))
  · exact (vlane_quadVec l 0 3 j hj).2.trans (red j hj 3 (by omega))
  · exact (vlane_quadVec l 1 4 j hj).2.trans (red j hj 4 (by omega))
  · exact (vlane_quadVec l 2 5 j hj).2.trans (red j hj 5 (by omega))

/-! ## The concatenated result

The extraction probe returns the kernel's three result vectors as one 24-lane
value (see `Mlir/fd_r43x6_quad_*.lean`), so the specification predicts that
shape too. `sliceNM` projects a third back out; each is definitionally the
vector it was built from, so the eight-lane lemmas above still apply to it. -/

/-- The three QUAD vectors as one 24-lane value: lanes 0-7 `z03`, 8-15 `z14`,
16-23 `z25`. -/
def quadCat (a b c : Vector (BitVec 64) 8) : Vector (BitVec 64) 24 :=
  #v[a[0], a[1], a[2], a[3], a[4], a[5], a[6], a[7],
     b[0], b[1], b[2], b[3], b[4], b[5], b[6], b[7],
     c[0], c[1], c[2], c[3], c[4], c[5], c[6], c[7]]

/-- The complete result of a quad kernel predicted from the four elements'
limbs `l j k`. -/
def quadVec24 (l : ℕ → ℕ → ℕ) : Vector (BitVec 64) 24 :=
  quadCat (quadVec l 0 3) (quadVec l 1 4) (quadVec l 2 5)

/-- `quadVec24` as one literal vector.

Unfolding `quadCat` on top of `quadVec` leaves twenty-four nested `getElem`s
for `simp` to chase, which is slow enough to exhaust a default heartbeat
budget on its own. Rewriting with this instead lands on the literal in one
step. -/
theorem quadVec24_eq (l : ℕ → ℕ → ℕ) :
    quadVec24 l =
      #v[BitVec.ofNat 64 (l 0 0), BitVec.ofNat 64 (l 1 0), BitVec.ofNat 64 (l 2 0), BitVec.ofNat 64 (l 3 0),
     BitVec.ofNat 64 (l 0 3), BitVec.ofNat 64 (l 1 3), BitVec.ofNat 64 (l 2 3), BitVec.ofNat 64 (l 3 3),
     BitVec.ofNat 64 (l 0 1), BitVec.ofNat 64 (l 1 1), BitVec.ofNat 64 (l 2 1), BitVec.ofNat 64 (l 3 1),
     BitVec.ofNat 64 (l 0 4), BitVec.ofNat 64 (l 1 4), BitVec.ofNat 64 (l 2 4), BitVec.ofNat 64 (l 3 4),
     BitVec.ofNat 64 (l 0 2), BitVec.ofNat 64 (l 1 2), BitVec.ofNat 64 (l 2 2), BitVec.ofNat 64 (l 3 2),
     BitVec.ofNat 64 (l 0 5), BitVec.ofNat 64 (l 1 5), BitVec.ofNat 64 (l 2 5), BitVec.ofNat 64 (l 3 5)] := by
  apply Vector.ext; intro i hi; interval_cases i <;> rfl

/-- The `z03` third of a concatenated result. -/
def slice03 (v : Vector (BitVec 64) 24) : Vector (BitVec 64) 8 :=
  #v[v[0], v[1], v[2], v[3], v[4], v[5], v[6], v[7]]
/-- The `z14` third of a concatenated result. -/
def slice14 (v : Vector (BitVec 64) 24) : Vector (BitVec 64) 8 :=
  #v[v[8], v[9], v[10], v[11], v[12], v[13], v[14], v[15]]
/-- The `z25` third of a concatenated result. -/
def slice25 (v : Vector (BitVec 64) 24) : Vector (BitVec 64) 8 :=
  #v[v[16], v[17], v[18], v[19], v[20], v[21], v[22], v[23]]

@[simp] theorem slice03_quadCat (a b c : Vector (BitVec 64) 8) :
    slice03 (quadCat a b c) = a := by
  apply Vector.ext; intro i hi; interval_cases i <;> rfl
@[simp] theorem slice14_quadCat (a b c : Vector (BitVec 64) 8) :
    slice14 (quadCat a b c) = b := by
  apply Vector.ext; intro i hi; interval_cases i <;> rfl
@[simp] theorem slice25_quadCat (a b c : Vector (BitVec 64) 8) :
    slice25 (quadCat a b c) = c := by
  apply Vector.ext; intro i hi; interval_cases i <;> rfl

/-- Reading a QUAD element back out of a concatenated result. -/
theorem quadLimb_slice_quadVec24 (l : ℕ → ℕ → ℕ) (j : ℕ) (hj : j < 4)
    (k : ℕ) (hk : k < 6) (hb : ∀ i < 4, ∀ k' < 6, l i k' < 2 ^ 64) :
    quadLimb (slice03 (quadVec24 l)) (slice14 (quadVec24 l)) (slice25 (quadVec24 l)) j k
      = l j k := by
  rw [quadVec24, slice03_quadCat, slice14_quadCat, slice25_quadCat]
  exact quadLimb_quadVec l j hj k hk hb

/-! ## Bounds

Input side: a `UNN n` hypothesis on the three vectors bounds every limb of
every element. Output side: a ceiling on the ℕ-level limbs gives the two-sided
`BitVec.toInt` bounds `R43x6.UNN` is stated with. -/

/-- Every limb of every element of a `UNN n` QUAD is below `2^n`. -/
theorem quadLimb_lt (a b c : Vector (BitVec 64) 8) (n : ℕ) (hn : n ≤ 62)
    (ha : R43x6.UNN n a) (hb : R43x6.UNN n b) (hc : R43x6.UNN n c)
    (j : ℕ) (hj : j < 4) (k : ℕ) (hk : k < 6) :
    quadLimb a b c j k < 2 ^ n := by
  have la : ∀ i (hi : i < 8), (a[i]'hi).toNat < 2 ^ n := unn_toNat a n hn ha
  have lb : ∀ i (hi : i < 8), (b[i]'hi).toNat < 2 ^ n := unn_toNat b n hn hb
  have lc : ∀ i (hi : i < 8), (c[i]'hi).toNat < 2 ^ n := unn_toNat c n hn hc
  interval_cases k <;> interval_cases j <;>
    simp only [quadLimb, vlane] <;>
    first
      | exact la _ (by omega) | exact lb _ (by omega) | exact lc _ (by omega)

/-- Two-sided lane bounds on `quadVec` from a ceiling `N` on the ℕ-level
limbs. The quad analogue of `limbVec_bounds`; unlike that one there are no
zero lanes, since all eight lanes carry limbs. -/
theorem quadVec_bounds (l : ℕ → ℕ → ℕ) (m n N : ℕ) (hN : N ≤ 2 ^ 63)
    (hb : ∀ j < 4, l j m < N ∧ l j n < N) :
    R43x6.BoundedUpper ((N : Int) - 1) (quadVec l m n)
      ∧ R43x6.BoundedLower 0 (quadVec l m n) := by
  have key : ∀ (v : ℕ), v < N →
      (0 : Int) ≤ (BitVec.ofNat 64 v).toInt
        ∧ (BitVec.ofNat 64 v).toInt ≤ (N : Int) - 1 :=
    fun v hv => lane_toInt_bound hN hv
  refine ⟨fun i hi => ?_, fun i hi => ?_⟩ <;> interval_cases i
  · exact (key _ (hb 0 (by omega)).1).2
  · exact (key _ (hb 1 (by omega)).1).2
  · exact (key _ (hb 2 (by omega)).1).2
  · exact (key _ (hb 3 (by omega)).1).2
  · exact (key _ (hb 0 (by omega)).2).2
  · exact (key _ (hb 1 (by omega)).2).2
  · exact (key _ (hb 2 (by omega)).2).2
  · exact (key _ (hb 3 (by omega)).2).2
  · exact (key _ (hb 0 (by omega)).1).1
  · exact (key _ (hb 1 (by omega)).1).1
  · exact (key _ (hb 2 (by omega)).1).1
  · exact (key _ (hb 3 (by omega)).1).1
  · exact (key _ (hb 0 (by omega)).2).1
  · exact (key _ (hb 1 (by omega)).2).1
  · exact (key _ (hb 2 (by omega)).2).1
  · exact (key _ (hb 3 (by omega)).2).1

end Firedancer.Avx512
