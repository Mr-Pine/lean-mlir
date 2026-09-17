/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SSA.Projects.Firedancer.Avx512.Spec.Common
public import SSA.Projects.Firedancer.Curve

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

@[expose] public section

namespace Firedancer.Avx512

open LeanMLIR SLLVM
open InstCombine (LLVM)

/-- Lane `i` of an 8-lane vector as a natural, junk (`0`) out of range. The
`limbNat` of `Spec/Common.lean` reads only the six limb lanes of a scalar
`fd_r43x6_t`; a QUAD uses all eight. -/
def vlane (v : Vector (BitVec 64) 8) : Fin 8 → ℕ
  | 0 => v[0].toNat
  | 1 => v[1].toNat
  | 2 => v[2].toNat
  | 3 => v[3].toNat
  | 4 => v[4].toNat
  | 5 => v[5].toNat
  | 6 => v[6].toNat
  | 7 => v[7].toNat

def laneFunc {n : Nat} (v : Vector (BitVec 64) n) : Fin n → ℕ :=
  (fun (i : Fin n) => v[i].toNat)

/-- The limb function of the field element in lane `j` of the QUAD `(a,b,c)`,
in the `ℕ → ℕ` form `decodeNat` and the column sums take. -/
def quadLimb (a b c : Vector (BitVec 64) 8) (j : Fin 4) : Fin 6 → ℕ
  | 0 => vlane a (j.castAdd 4)
  | 1 => vlane b (j.castAdd 4)
  | 2 => vlane c (j.castAdd 4)
  | 3 => vlane a (j.addNat 4)
  | 4 => vlane b (j.addNat 4)
  | 5 => vlane c (j.addNat 4)

/-! ## The QUAD, un-transposed -/

/-- One element of the QUAD `(a, b, c)`, as its six limbs in order: the
un-transposed reading of lane `j`. -/
def quadElemVec (a b c : Vector (BitVec 64) 8) (j : Fin 4) : Vector (BitVec 64) 6 :=
  #v[a[j.val], b[j.val], c[j.val], a[j.val + 4], b[j.val + 4], c[j.val + 4]]

/-- A curve point as `fd_r43x6_ge.h` holds it in a QUAD: one six-limb vector
per coordinate. -/
@[ext]
structure PointVectors where
  X : Vector (BitVec 64) 6
  Y : Vector (BitVec 64) 6
  Z : Vector (BitVec 64) 6
  T : Vector (BitVec 64) 6

/-- A `FD_R43X6_QUAD` as a value: its three transposed vectors, named by the
limb pairs they carry. -/
@[ext]
structure Quad where
  v03 : Vector (BitVec 64) 8
  v14 : Vector (BitVec 64) 8
  v25 : Vector (BitVec 64) 8

/-- All three vectors of a QUAD are `u46`. -/
abbrev Quad.U46 (q : Quad) : Prop :=
  R43x6.U46 q.v03 ∧ R43x6.U46 q.v14 ∧ R43x6.U46 q.v25

def Quad.vector (q : Quad) (i : Fin 4) :=
  quadElemVec q.v03 q.v14 q.v25 i

def Quad.vectorFunc (q : Quad) :=
  laneFunc ∘ q.vector

/-- Reading an element vector's lanes is the limb function of its lane. -/
theorem laneFunc_vector (q : Quad) (j : Fin 4) :
    laneFunc (q.vector j) = quadLimb q.v03 q.v14 q.v25 j := by
  funext k
  fin_cases j <;> fin_cases k <;> rfl

/-! ## The point a QUAD represents -/

/-- The four coordinate vectors of a QUAD: lanes 0-3 are `X`, `Y`, `Z`, `T`,
the element order of `fd_r43x6_ge.h`. -/
def Quad.PointVecs (x : Quad) : PointVectors where
  X := x.vector 0
  Y := x.vector 1
  Z := x.vector 2
  T := x.vector 3

/-- The field element held in the low six lanes of a vector of at least six:
the limbs at `0..5`, decoded in `GF(2^255 - 19)`. On a QUAD element vector it
is `quadElem`, definitionally. -/
def decodeVec {n : ℕ} (hn : 6 ≤ n) (v : Vector (BitVec 64) n) : ZMod p :=
  ((decodeNat (fun i : Fin 6 => (v[i.val]'(lt_of_lt_of_le i.isLt hn)).toNat) : ℕ) : ZMod p)

/-- The field element in lane `j` of a QUAD: its six limbs decoded in
`GF(2^255 - 19)`. -/
def quadElem (x : Quad) (j : Fin 4) : ZMod p :=
  ((decodeNat (x.vectorFunc j) : ℕ) : ZMod p)

/-- The curve point four coordinate vectors hold. -/
def PointVectors.toPoint (P : PointVectors) : Ed25519.Point :=
  ⟨decodeVec (le_refl _) P.X, decodeVec (le_refl _) P.Y, decodeVec (le_refl _) P.Z,
    decodeVec (le_refl _) P.T⟩

/-- The curve point a QUAD holds: lanes 0-3 are `X`, `Y`, `Z`, `T`; coordinate
`j` is `quadElem x j`, definitionally. -/
def Quad.toPoint (x : Quad) : Ed25519.Point :=
  x.PointVecs.toPoint

/-- Encode four element vectors into the transposed QUAD layout: limb `k` of
element `j` goes to lane `j` (for `k < 3`) or `j + 4` (for `k ≥ 3`) of the
`k mod 3`-th third. The inverse of `Quad.PointVecs`. -/
def encodeQuad (x y z t : Vector (BitVec 64) 6) : Quad where
  v03 := #v[x[0], y[0], z[0], t[0], x[3], y[3], z[3], t[3]]
  v14 := #v[x[1], y[1], z[1], t[1], x[4], y[4], z[4], t[4]]
  v25 := #v[x[2], y[2], z[2], t[2], x[5], y[5], z[5], t[5]]

/-- A point's QUAD encoding. -/
def PointVectors.toQuad (P : PointVectors) : Quad :=
  encodeQuad P.X P.Y P.Z P.T

/-- **Round trip, vectors first**: the encoding's coordinate vectors are the
four that were encoded. -/
theorem PointVecs_encodeQuad (x y z t : Vector (BitVec 64) 6) :
    (encodeQuad x y z t).PointVecs = ⟨x, y, z, t⟩ := by
  refine PointVectors.ext ?_ ?_ ?_ ?_ <;>
    · apply Vector.ext
      intro i hi
      interval_cases i <;> rfl

/-- **Round trip, QUAD first**: encoding a QUAD's coordinate vectors rebuilds
it. -/
theorem toQuad_PointVecs (x : Quad) : x.PointVecs.toQuad = x := by
  refine Quad.ext ?_ ?_ ?_ <;>
    · apply Vector.ext
      intro i hi
      interval_cases i <;> rfl

abbrev QuadFunc :=
  Fin 4 → Fin 6 → ℕ

/-- One output vector of a quad kernel: given the four elements' limbs
`l j k`, the vector holding limb `m` of each element in lanes 0-3 and limb `n`
in lanes 4-7. The three results are `quadVec l 0 3`, `quadVec l 1 4` and
`quadVec l 2 5`. -/
def quadVec (l : QuadFunc) (m n : Fin 6) : Vector (BitVec 64) 8 :=
  #v[BitVec.ofNat 64 (l 0 m), BitVec.ofNat 64 (l 1 m), BitVec.ofNat 64 (l 2 m),
    BitVec.ofNat 64 (l 3 m), BitVec.ofNat 64 (l 0 n), BitVec.ofNat 64 (l 1 n),
    BitVec.ofNat 64 (l 2 n), BitVec.ofNat 64 (l 3 n)]

/-! ## Round trip

Reading the three predicted output vectors back through the QUAD layout
recovers the limbs that were written, provided none is truncated by the
64-bit lane. -/

/-- Each lane of `quadVec` is the `BitVec.ofNat` of the limb it was built
from. -/
theorem vlane_quadVec (l : QuadFunc) (m n : Fin 6) (j : Fin 4) :
    vlane (quadVec l m n) (j.castAdd 4) = (BitVec.ofNat 64 (l j m)).toNat ∧
      vlane (quadVec l m n) (j.addNat 4) = (BitVec.ofNat 64 (l j n)).toNat := by
  fin_cases j <;> exact ⟨rfl, rfl⟩

/-- **Round trip.** The QUAD assembled from the three predicted vectors reads
back as the limbs it was built from, as long as every limb fits a lane. -/
theorem quadLimb_quadVec (l : QuadFunc) (j : Fin 4) (k : Fin 6)
    (hb : ∀ (i : Fin 4), ∀ (k' : Fin 6), l i k' < 2 ^ 64) :
    quadLimb (quadVec l 0 3) (quadVec l 1 4) (quadVec l 2 5) j k = l j k := by
  have red : ∀ (i : Fin 4), ∀ (k' : Fin 6), (BitVec.ofNat 64 (l i k')).toNat = l i k' := by
    intro i k'
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by simpa using hb i k')
  fin_cases k
  · exact (vlane_quadVec l 0 3 j).1.trans (red j 0)
  · exact (vlane_quadVec l 1 4 j).1.trans (red j 1)
  · exact (vlane_quadVec l 2 5 j).1.trans (red j 2)
  · exact (vlane_quadVec l 0 3 j).2.trans (red j 3)
  · exact (vlane_quadVec l 1 4 j).2.trans (red j 4)
  · exact (vlane_quadVec l 2 5 j).2.trans (red j 5)

/-! ## Bounds

Input side: a `UNN n` hypothesis on the three vectors bounds every limb of
every element. Output side: a ceiling on the ℕ-level limbs gives the two-sided
`BitVec.toInt` bounds `R43x6.UNN` is stated with. -/

/-- Every limb of every element of a `UNN n` QUAD is below `2^n`. -/
theorem quadLimb_lt (x : Quad) (n : ℕ) (hn : n ≤ 62) (hx03 : R43x6.UNN n x.v03)
    (hx14 : R43x6.UNN n x.v14) (hx25 : R43x6.UNN n x.v25) (j : Fin 4) (k : Fin 6) :
    quadLimb x.v03 x.v14 x.v25 j k < 2 ^ n := by
  have la : ∀ i (hi : i < 8), (x.v03[i]'hi).toNat < 2 ^ n := fun i hi =>
    unn_toNat x.v03 n hn hx03 ⟨i, hi⟩
  have lb : ∀ i (hi : i < 8), (x.v14[i]'hi).toNat < 2 ^ n := fun i hi =>
    unn_toNat x.v14 n hn hx14 ⟨i, hi⟩
  have lc : ∀ i (hi : i < 8), (x.v25[i]'hi).toNat < 2 ^ n := fun i hi =>
    unn_toNat x.v25 n hn hx25 ⟨i, hi⟩
  fin_cases k <;> fin_cases j <;> simp [quadLimb, vlane] <;>
    first
    | exact la _ (by omega)
    | exact lb _ (by omega)
    | exact lc _ (by omega)

/-- Two-sided lane bounds on `quadVec` from a ceiling `N` on the ℕ-level
limbs. The quad analogue of `limbVec_bounds`; unlike that one there are no
zero lanes, since all eight lanes carry limbs. -/
theorem quadVec_bounds (l : QuadFunc) (m n : Fin 6) (N : ℕ) (hN : N ≤ 2 ^ 63)
    (hb : ∀ (j : Fin 4), l j m < N ∧ l j n < N) :
    R43x6.BoundedUpper ((N : Int) - 1) (quadVec l m n) ∧ R43x6.BoundedLower 0 (quadVec l m n) := by
  have key :
    ∀ (v : ℕ),
      v < N → (0 : Int) ≤ (BitVec.ofNat 64 v).toInt ∧ (BitVec.ofNat 64 v).toInt ≤ (N : Int) - 1 :=
    fun v hv => lane_toInt_bound hN hv
  refine ⟨fun i => ?_, fun i => ?_⟩ <;> simp only [LimbRepresentations.toInts, quadVec] <;>
    fin_cases i
  · exact (key _ (hb 0).1).2
  · exact (key _ (hb 1).1).2
  · exact (key _ (hb 2).1).2
  · exact (key _ (hb 3).1).2
  · exact (key _ (hb 0).2).2
  · exact (key _ (hb 1).2).2
  · exact (key _ (hb 2).2).2
  · exact (key _ (hb 3).2).2
  · exact (key _ (hb 0).1).1
  · exact (key _ (hb 1).1).1
  · exact (key _ (hb 2).1).1
  · exact (key _ (hb 3).1).1
  · exact (key _ (hb 0).2).1
  · exact (key _ (hb 1).2).1
  · exact (key _ (hb 2).2).1
  · exact (key _ (hb 3).2).1

/-! ## Memory -/

/-- `p` addresses a whole QUAD: three 8-lane vectors, `3 * 8 * 64` bits = 192
bytes. (Not `4 * 5 * 64` -- that is the *ref* point's four five-limb
coordinates, a 160-byte object with a different layout.) -/
abbrev IsQuadPtr (m : MemoryState) (p : Pointer) : Prop :=
  Fits m p (3 * 8 * 64) ∧ p.offset.toNat + (3 * 8 * 8) ≤ 2 ^ 64

def readQuad? (p : Pointer) (m : MemoryState) : Option Quad := do
  let readVec (i : Fin 3) := do
    let liveBlock ← m.live? p.id
    let vec : Vector _ 8 :=
      Vector.ofFn
        (fun j =>
          liveBlock.bytes.extractLsb' (p.offsetInBits + i.toNat * (64 * 8) + 64 * j.toNat) 64)
    return vec
  let v1 ← readVec 0
  let v2 ← readVec 1
  let v3 ← readVec 2
  return ⟨v1, v2, v3⟩

theorem readQuad?_isSome {m : MemoryState} {p : Pointer} (h : IsQuadPtr m p) :
    (readQuad? p m).isSome := by
  obtain ⟨⟨block, hblk, -⟩, -⟩ := h
  have hlive : m.live? p.id = some block := by simp only [MemoryState.live?, hblk]
  -- The three reads are `extractLsb'`, which is total, so liveness of the
  -- block is all that makes this `some`; `IsQuadPtr`'s size bound is not used.
  simp [readQuad?, hlive]

def readQuad {p : Pointer} {m : MemoryState} (h : IsQuadPtr m p) : Quad :=
  (readQuad? p m).get (readQuad?_isSome h)

/-- The 512 bits an `fd_r43x6_t` occupies in memory: lane `j` at bits
`[64j, 64j + 64)`, which is what a whole-vector store writes. -/
def vecBV (v : Vector (BitVec 64) 8) : BitVec 512 :=
  LLVM.Ty.flattenBV (.vector 8 (.bitvec (.concrete 64))) (v.map PoisonOr.value)

/-- A fully-defined `fd_r43x6_t` flattens to `vecBV`: every lane holds a value,
so a whole-vector store of it does not raise poison. (The same fact as
`Avx512.flatten_map_value`, stated where `vecBV` lives so the store peel does
not have to reach into the proof layer for it.) -/
theorem flatten_vecBV (v : Vector (BitVec 64) 8) :
    LLVM.Ty.flatten (.vector 8 (.bitvec (.concrete 64))) (v.map PoisonOr.value) =
      .value (vecBV v) := by
  rw [LLVM.Ty.flatten, if_pos]
  · rfl
  · intro i
    show LLVM.Ty.ofBitvec ((v.map PoisonOr.value)[i.val]) ≠ .poison
    rw [Vector.getElem_map]
    exact PoisonOr.value_ne_poison _

/-- The 1536 bits a QUAD occupies in memory: the three vectors at the offsets
`readQuad?` reads them back at -- `v03` lowest, then `v14`, then `v25`. -/
def Quad.BV (q : Quad) : BitVec (3 * 8 * 64) :=
  BitVec.packLanes (we := 512) (n := 3) #v[vecBV q.v03, vecBV q.v14, vecBV q.v25]

end Firedancer.Avx512
