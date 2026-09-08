/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.Firedancer.Avx512.Spec.Vec
import SSA.Projects.Firedancer.Avx512.Spec.Field.fd_r43x6_sqr_fast
import SSA.Projects.Firedancer.Avx512.Spec.Field.fd_r43x6_mul_fast
import SSA.Projects.Firedancer.Avx512.Proof.Common

/-!
# `fd_r43x6_fold_unsigned`

The four-instruction tail of every `fd_r43x6` multiply and square --
`FD_R43X6_MUL_INL`, `FD_R43X6_SQR_INL`, `FD_R43X6_MUL2_INL` and the loop body
of `fd_r43x6_repsqr_mul2` all end in it, so it is modelled once here rather
than at each call site:

    _l = wwl_and ( z, wwl( _m43,_m43,_m43,_m43,_m43,_m40, 0,0 ) )
    _h = wwl_permute( wwl( 5,0,1,2,3,4, 6,7 ),
                      wwl_shru_vector( z, wwl( 43,43,43,43,43,40, 0,0 ) ) )
    z' = wwl_madd52lo( _l, wwl( 19,1,1,1,1,1, 0,0 ), _h )

Each limb keeps its low 43 bits (40 for limb 5) and passes what is above them
to the next limb up; limb 5's overflow wraps to limb 0 scaled by `19`, since
`2^255 ≡ 19 (mod p)`. Unlike `fd_r43x6_biased_carry_propagate_limbs` this is
one *parallel* step over unsigned limbs -- no chain, no bias, no `ashr` -- so
it does not fully carry: it only brings `u62`-ish limbs back to `u44`, which
is exactly the input contract of the next multiply.

Nothing here mentions the program. The four instructions are reduced to
`foldVec` at each call site by the lane tactics of `Proof/Common.lean`, and
these two theorems are what that reduction is then combined with:
`vecValue_foldVec` (the element is unchanged) and `foldVec_u44` (the limbs the
`fd_r43x6.h` table promises).
-/

namespace Firedancer.Avx512
open InstCombine (LLVM)

/-! ## The ℕ-level model -/

/-- **`fd_r43x6_fold_unsigned`** on limbs: limb `k` keeps its low `43` bits
(`40` for limb 5) and takes the bits above `43` of limb `k-1`; limb 0 takes
limb 5's, scaled by `19 = 2^255 mod p`. -/
def foldLimb (x : Fin 6 → ℕ) : Fin 6 → ℕ
  | 0 => x 0 % 2 ^ 43 + 19 * (x 5 / 2 ^ 40)
  | 1 => x 1 % 2 ^ 43 + x 0 / 2 ^ 43
  | 2 => x 2 % 2 ^ 43 + x 1 / 2 ^ 43
  | 3 => x 3 % 2 ^ 43 + x 2 / 2 ^ 43
  | 4 => x 4 % 2 ^ 43 + x 3 / 2 ^ 43
  | 5 => x 5 % 2 ^ 40 + x 4 / 2 ^ 43

/-! ### Ring correctness

The value changes by exactly `p` per unit of limb 5's overflow: what the fold
moves out of limb 5 has weight `2^255` and comes back at weight `19`. -/

/-- **The fold changes the packed value by exactly limb 5's overflow times
`p`.** The exact identity behind the congruence below. -/
theorem decodeNat_foldLimb_add (x : Fin 6 → ℕ) :
    decodeNat (foldLimb x) + p * (x 5 / 2 ^ 40) = decodeNat x := by
  have d0 := Nat.div_add_mod (x 0) (2 ^ 43)
  have d1 := Nat.div_add_mod (x 1) (2 ^ 43)
  have d2 := Nat.div_add_mod (x 2) (2 ^ 43)
  have d3 := Nat.div_add_mod (x 3) (2 ^ 43)
  have d4 := Nat.div_add_mod (x 4) (2 ^ 43)
  have d5 := Nat.div_add_mod (x 5) (2 ^ 40)
  simp only [decodeNat_eq, foldLimb, p]
  omega

/-- **Ring correctness**, as a congruence. -/
theorem decodeNat_foldLimb_modEq (x : Fin 6 → ℕ) :
    decodeNat (foldLimb x) ≡ decodeNat x [MOD p] := by
  show _ % _ = _ % _
  conv_rhs => rw [← decodeNat_foldLimb_add x]
  rw [Nat.add_mul_mod_self_left]

/-- **Ring correctness**, in `ZMod p`. -/
theorem decodeNat_foldLimb_zmod (x : Fin 6 → ℕ) :
    ((decodeNat (foldLimb x) : ℕ) : ZMod p) = ((decodeNat x : ℕ) : ZMod p) :=
  (ZMod.natCast_eq_natCast_iff _ _ _).mpr (decodeNat_foldLimb_modEq x)

/-! ### Bounds

`u44` out of anything a multiply can produce. The slack is wide: limb 0, the
worst case, is under `2^43 + 19·2^23`, and `19·2^23 < 2^28`. -/

/-- **The `u44` the `fd_r43x6.h` table promises.** The hypothesis is what a
lane below `2^63` gives -- `u61`, `u62` and `u63` outputs all satisfy it. -/
theorem foldLimb_lt {x : Fin 6 → ℕ} (h : ∀ i, x i < 2 ^ 63) (k : Fin 6) :
    foldLimb x k < 2 ^ 44 := by
  have q0 : x 0 / 2 ^ 43 < 2 ^ 20 := Nat.div_lt_of_lt_mul (by have := h 0; omega)
  have q1 : x 1 / 2 ^ 43 < 2 ^ 20 := Nat.div_lt_of_lt_mul (by have := h 1; omega)
  have q2 : x 2 / 2 ^ 43 < 2 ^ 20 := Nat.div_lt_of_lt_mul (by have := h 2; omega)
  have q3 : x 3 / 2 ^ 43 < 2 ^ 20 := Nat.div_lt_of_lt_mul (by have := h 3; omega)
  have q4 : x 4 / 2 ^ 43 < 2 ^ 20 := Nat.div_lt_of_lt_mul (by have := h 4; omega)
  have q5 : x 5 / 2 ^ 40 < 2 ^ 23 := Nat.div_lt_of_lt_mul (by have := h 5; omega)
  have m0 : x 0 % 2 ^ 43 < 2 ^ 43 := Nat.mod_lt _ (by norm_num)
  have m1 : x 1 % 2 ^ 43 < 2 ^ 43 := Nat.mod_lt _ (by norm_num)
  have m2 : x 2 % 2 ^ 43 < 2 ^ 43 := Nat.mod_lt _ (by norm_num)
  have m3 : x 3 % 2 ^ 43 < 2 ^ 43 := Nat.mod_lt _ (by norm_num)
  have m4 : x 4 % 2 ^ 43 < 2 ^ 43 := Nat.mod_lt _ (by norm_num)
  have m5 : x 5 % 2 ^ 40 < 2 ^ 40 := Nat.mod_lt _ (by norm_num)
  fin_cases k <;> simp only [foldLimb] <;> omega

/-! ## The lanes

`foldVec` is the model as a result vector: six limbs and two zero lanes, the
same `limbVec` shape `sqrVec` and `mulVec` use. -/

/-- The vector `fd_r43x6_fold_unsigned` returns. -/
def foldVec (z : Vector (BitVec 64) 8) : Vector (BitVec 64) 8 :=
  limbVec (foldLimb (limbNat z))

/-- The limb hypothesis of the two theorems below, from the `unn` class of the
vector the fold is applied to: `u62` in, and `u63` in, are both below `2^63`.
-/
theorem limbNat_lt_two_pow_63 {z : Vector (BitVec 64) 8} {n : ℕ} (hn : n ≤ 62)
    (hz : R43x6.UNN n z) (i : Fin 6) : limbNat z i < 2 ^ 63 :=
  lt_of_lt_of_le (limbNat_lt z n hn hz i) (Nat.pow_le_pow_right (by norm_num) (by omega))

/-- **Reading a result vector's lanes back gives its limbs.** Stated for any
`limbVec`, not just the fold's: `sqrVec` and `mulVec` are the same shape, so
each of them reaches `vecValue` through this. -/
theorem limbNat_limbVec {l : Fin 6 → ℕ} (h : ∀ k, l k < 2 ^ 64) :
    limbNat (limbVec l) = l := by
  funext i
  fin_cases i <;>
    simp only [limbVec, limbNat, Vector.getElem_mk, List.getElem_toArray,
      List.getElem_cons_zero, List.getElem_cons_succ, BitVec.toNat_ofNat] <;>
    exact Nat.mod_eq_of_lt (h _)

/-- `vecValue` through `decodeNat`, the form every `fd_r43x6` result is
specified in. -/
theorem vecValue_eq_decodeNat (v : Vector (BitVec 64) 8) :
    vecValue v = ((decodeNat (limbNat v) : ℕ) : ZMod p) := by
  simp only [vecValue, decodeVec]
  congr 2
  funext i
  fin_cases i <;> rfl

/-- The element a result vector holds is its limbs' `decodeNat`. -/
theorem vecValue_limbVec {l : Fin 6 → ℕ} (h : ∀ k, l k < 2 ^ 64) :
    vecValue (limbVec l) = ((decodeNat l : ℕ) : ZMod p) := by
  rw [vecValue_eq_decodeNat, limbNat_limbVec h]

/-- **The element is unchanged.** -/
theorem vecValue_foldVec {z : Vector (BitVec 64) 8}
    (h : ∀ i : Fin 6, limbNat z i < 2 ^ 63) :
    vecValue (foldVec z) = vecValue z := by
  rw [foldVec, vecValue_limbVec fun k => lt_trans (foldLimb_lt h k) (by norm_num),
    vecValue_eq_decodeNat]
  exact decodeNat_foldLimb_zmod (limbNat z)

/-- **The limbs are `u44`.** -/
theorem foldVec_u44 {z : Vector (BitVec 64) 8}
    (h : ∀ i : Fin 6, limbNat z i < 2 ^ 63) : R43x6.U44 (foldVec z) := by
  have := limbVec_bounds (foldLimb (limbNat z)) (2 ^ 44) (by norm_num) (foldLimb_lt h)
  exact_mod_cast this

/-- A `unn` contract on the six limb lanes extends to all eight, the form the
kernels' denotation theorems take it in: lanes 6 and 7 are zero, and `0` is in
every `unn` range. -/
theorem UNN_of_take {n : ℕ} {v : Vector (BitVec 64) 8}
    (h : R43x6.UNN n (v.take R43x6.limbCount)) (h6 : v[6] = 0) (h7 : v[7] = 0) :
    R43x6.UNN n v := by
  have hz : ((0 : BitVec 64)).toInt = 0 := rfl
  have h1 : (1 : ℤ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
  refine ⟨fun i => ?_, fun i => ?_⟩ <;> fin_cases i <;>
    simp only [LimbRepresentations.toInts] <;>
    first
      | exact (R43x6.extractLimbs_bounds h 0).2
      | exact (R43x6.extractLimbs_bounds h 1).2
      | exact (R43x6.extractLimbs_bounds h 2).2
      | exact (R43x6.extractLimbs_bounds h 3).2
      | exact (R43x6.extractLimbs_bounds h 4).2
      | exact (R43x6.extractLimbs_bounds h 5).2
      | exact (R43x6.extractLimbs_bounds h 0).1
      | exact (R43x6.extractLimbs_bounds h 1).1
      | exact (R43x6.extractLimbs_bounds h 2).1
      | exact (R43x6.extractLimbs_bounds h 3).1
      | exact (R43x6.extractLimbs_bounds h 4).1
      | exact (R43x6.extractLimbs_bounds h 5).1
      | (rw [h6]; omega)
      | (rw [h7]; omega)

/-- `u44 ⊆ u47`: the fold's output is the input contract of the next
`fd_r43x6_sqr_fast`/`mul_fast`, which is what lets a chain of them stay in
contract without a bound ever being re-derived. -/
theorem u47_of_u44 {l : Nat} {x : Vector (BitVec 64) l} (h : R43x6.U44 x) :
    R43x6.U47 x :=
  ⟨fun i => le_trans (h.1 i) (by norm_num), h.2⟩

/-- A `UNN` on all eight lanes restricts to the six limb lanes, the form the
`fd_r43x6` specs state their contracts in. -/
theorem UNN_take {n : ℕ} {v : Vector (BitVec 64) 8} (h : R43x6.UNN n v) :
    R43x6.UNN n (v.take R43x6.limbCount) :=
  ⟨fun i => by rw [R43x6.toInts_take]; exact h.1 _,
   fun i => by rw [R43x6.toInts_take]; exact h.2 _⟩

/-- The fold zeroes lane 6: the mask and the multiplier both have `0` there. -/
@[simp] theorem foldVec_getElem_six (z : Vector (BitVec 64) 8) : (foldVec z)[6] = 0 := rfl

/-- The fold zeroes lane 7, which is what the next `fd_r43x6_sqr_fast` needs. -/
@[simp] theorem foldVec_getElem_seven (z : Vector (BitVec 64) 8) : (foldVec z)[7] = 0 := rfl

/-! ## `FD_R43X6_SQR_INL` and `FD_R43X6_MUL_INL`

A kernel followed by the fold. Every call site of either needs the same pair
of facts of the composite -- the element it computes and the `u44` limbs it
leaves -- so the composition is done once here.

`fd_r43x6_sqr_fast` also wants its input's lanes 6 and 7 zero; that is a fact
about the *program*, not about the model, so it stays at the call site, where
`foldVec_getElem_six`/`_seven` discharge it for a folded operand. -/

/-- The limbs of a `unn` vector as naturals, from the `.take limbCount`
contract the `fd_r43x6` specs state rather than from an eight-lane `UNN`. -/
theorem limbNat_lt_of_take {x : Vector (BitVec 64) 8} {n : ℕ} (hn : n ≤ 62)
    (hx : R43x6.UNN n (x.take R43x6.limbCount)) (i : Fin 6) : limbNat x i < 2 ^ n := by
  obtain ⟨hl, hu⟩ := R43x6.extractLimbs_bounds hx i
  simp only [R43x6.extractLimbs, LimbRepresentations.toInts, Fin.val_castLE] at hl hu
  have : limbNat x i = (x[(i : ℕ)]'(by omega)).toNat := by fin_cases i <;> rfl
  rw [this]
  exact toNat_lt_of_bounds (Nat.pow_le_pow_right (by omega) hn) (by push_cast; omega) hl

/-! ### Squaring -/

/-- The squaring's own limbs are below `2 ^ 63`, so the fold applies to them. -/
theorem limbNat_sqrVec_lt {x : Vector (BitVec 64) 8} (hx : ∀ i, limbNat x i < 2 ^ 47)
    (i : Fin 6) : limbNat (sqrVec x) i < 2 ^ 63 := by
  rw [sqrVec, limbNat_limbVec fun k => lt_trans (sqLimb_lt_u47 _ hx k) (by norm_num)]
  exact lt_trans (sqLimb_lt_u47 _ hx i) (by norm_num)

/-- The element `fd_r43x6_sqr_fast` computes, before the fold. -/
theorem vecValue_sqrVec {x : Vector (BitVec 64) 8} (hx : ∀ i, limbNat x i < 2 ^ 47) :
    vecValue (sqrVec x) = vecValue x ^ 2 := by
  rw [sqrVec, vecValue_limbVec fun k => lt_trans (sqLimb_lt_u47 _ hx k) (by norm_num),
    vecValue_eq_decodeNat]
  exact decodeLimbs_sqLimb_zmod (limbNat x)

/-- **`FD_R43X6_SQR_INL` computes the square.** -/
theorem vecValue_foldVec_sqrVec {x : Vector (BitVec 64) 8}
    (hx : ∀ i, limbNat x i < 2 ^ 47) :
    vecValue (foldVec (sqrVec x)) = vecValue x ^ 2 :=
  (vecValue_foldVec (limbNat_sqrVec_lt hx)).trans (vecValue_sqrVec hx)

/-- **`FD_R43X6_SQR_INL` returns `u44` limbs** -- the input contract of the
next squaring or multiply. -/
theorem foldVec_sqrVec_u44 {x : Vector (BitVec 64) 8} (hx : ∀ i, limbNat x i < 2 ^ 47) :
    R43x6.U44 (foldVec (sqrVec x)) :=
  foldVec_u44 (limbNat_sqrVec_lt hx)

/-! ### Multiplying -/

/-- The product's own limbs are below `2 ^ 63`, so the fold applies to them. -/
theorem limbNat_mulVec_lt {x y : Vector (BitVec 64) 8} (hx : ∀ i, limbNat x i < 2 ^ 47)
    (hy : ∀ i, limbNat y i < 2 ^ 47) (i : Fin 6) : limbNat (mulVec x y) i < 2 ^ 63 := by
  rw [mulVec, limbNat_limbVec fun k => lt_trans (limb_lt_u47 _ _ hx hy k) (by norm_num)]
  exact limb_lt_u47 _ _ hx hy i

/-- The element `fd_r43x6_mul_fast` computes, before the fold. -/
theorem vecValue_mulVec {x y : Vector (BitVec 64) 8} (hx : ∀ i, limbNat x i < 2 ^ 47)
    (hy : ∀ i, limbNat y i < 2 ^ 47) :
    vecValue (mulVec x y) = vecValue x * vecValue y := by
  rw [mulVec, vecValue_limbVec fun k => lt_trans (limb_lt_u47 _ _ hx hy k) (by norm_num),
    vecValue_eq_decodeNat, vecValue_eq_decodeNat]
  exact decodeLimbs_limb_zmod (limbNat x) (limbNat y)

/-- **`FD_R43X6_MUL_INL` computes the product.** -/
theorem vecValue_foldVec_mulVec {x y : Vector (BitVec 64) 8}
    (hx : ∀ i, limbNat x i < 2 ^ 47) (hy : ∀ i, limbNat y i < 2 ^ 47) :
    vecValue (foldVec (mulVec x y)) = vecValue x * vecValue y :=
  (vecValue_foldVec (limbNat_mulVec_lt hx hy)).trans (vecValue_mulVec hx hy)

/-- **`FD_R43X6_MUL_INL` returns `u44` limbs.** -/
theorem foldVec_mulVec_u44 {x y : Vector (BitVec 64) 8} (hx : ∀ i, limbNat x i < 2 ^ 47)
    (hy : ∀ i, limbNat y i < 2 ^ 47) : R43x6.U44 (foldVec (mulVec x y)) :=
  foldVec_u44 (limbNat_mulVec_lt hx hy)

/-! ## The four instructions

`fd_r43x6_fold_unsigned` as the lane tactics leave it: the `and`, the
`lshr`, the `wwl_permute` shuffle and the `vpmadd52lo`, in the shape
`denote_eval` produces at a call site. One `rw` with this turns all four into
`foldVec`.

Lanes 6 and 7 need no hypothesis: the mask and the multiplier are `0` there,
so whatever the input holds in them, `0 + lo52 (0 * _) = 0` comes back. -/

/-- `wwl_and` against the `_m43` mask lane, at the ℕ level. -/
private theorem and_mask43 (x : BitVec 64) :
    x &&& 8796093022207#64 = BitVec.ofNat 64 (x.toNat % 2 ^ 43) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat]
  rw [show (8796093022207 : ℕ) % 2 ^ 64 = 2 ^ 43 - 1 from by norm_num,
    Nat.and_two_pow_sub_one_eq_mod]
  omega

/-- `wwl_and` against the `_m40` mask lane, at the ℕ level. -/
private theorem and_mask40 (x : BitVec 64) :
    x &&& 1099511627775#64 = BitVec.ofNat 64 (x.toNat % 2 ^ 40) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat]
  rw [show (1099511627775 : ℕ) % 2 ^ 64 = 2 ^ 40 - 1 from by norm_num,
    Nat.and_two_pow_sub_one_eq_mod]
  omega

set_option maxHeartbeats 1000000 in
/-- **Denotation of `fd_r43x6_fold_unsigned`.** `pv` is the `llvm.poison` the
shuffle takes as its dead second operand; every mask index is below 8, so no
lane of it is read. -/
theorem denote_foldVec (z : Vector (BitVec 64) 8)
    (hz : ∀ i : Fin 6, limbNat z i < 2 ^ 63) (pv : Vector (LLVM.IntW 64) 8) :
    LLVM.Ty.vpmadd52 false
        (Vector.ofFn fun i : Fin 8 => InstCombine.binaryDenote .and
          (z.map PoisonOr.value)[i.val]
          (toBitVecValue 64 #v[8796093022207, 8796093022207, 8796093022207, 8796093022207,
            8796093022207, 1099511627775, 0, 0])[i.val])
        (toBitVecValue 64 #v[19, 1, 1, 1, 1, 1, 0, 0])
        (LLVM.Ty.shufflevector (e := .bitvec (.concrete 64)) (l := 8) [5, 0, 1, 2, 3, 4, 6, 7]
          (Vector.ofFn fun i : Fin 8 => InstCombine.binaryDenote .lshr
            (z.map PoisonOr.value)[i.val]
            (toBitVecValue 64 #v[43, 43, 43, 43, 43, 40, 0, 0])[i.val]) pv)
      = (foldVec z).map PoisonOr.value := by
  have h0 := hz 0; have h1 := hz 1; have h2 := hz 2
  have h3 := hz 3; have h4 := hz 4; have h5 := hz 5
  simp only [limbNat] at h0 h1 h2 h3 h4 h5
  apply Vector.ext
  intro i hi
  interval_cases i <;>
    simp [LLVM.Ty.vpmadd52, LLVM.Ty.vpmadd52Lane, LLVM.Ty.shufflevector,
      InstCombine.binaryDenote, LLVM.and, LLVM.and?, LLVM.lshr, LLVM.lshr?,
      toBitVecValue, foldVec, limbVec, foldLimb, limbNat,
      and_mask43, and_mask40, Nat.shiftRight_eq_div_pow, ← BitVec.ofNat_add] <;>
    congr 1 <;> omega

/-! ## `fd_r43x6_fold_signed`

The other fold: `fd_r43x6_approx_carry_propagate` conjugated by a bias,

    fold_signed x = approx_carry_propagate (x - _b) + _b

with `_b = wwl( 19·2^23, 2^20, 2^20, 2^20, 2^20, 2^20, 0, 0 )`. Subtracting it
first is what keeps the carry propagate from overflowing on a *signed* input,
and adding it back leaves the element alone.

The carry pattern is `foldLimb`'s -- each limb keeps its low 43 bits (40 for
limb 5) and passes the rest up, limb 5's wrapping to limb 0 scaled by `19` --
but over `ℤ`, with `Int.emod`/`Int.ediv`. That is exactly what the `and`
against a mask and the *arithmetic* `wwl_shr_vector` do to a two's-complement
lane, which is the one place the two folds differ: the unsigned one shifts
logically, `wwl_shru_vector`, and so can stay in `ℕ`. -/

/-- The bias `_b`. -/
def biasLimb : Fin 6 → ℤ
  | 0 => 19 * 2 ^ 23
  | _ => 2 ^ 20

/-- **`fd_r43x6_approx_carry_propagate`** on signed limbs. -/
def acpLimb (x : Fin 6 → ℤ) : Fin 6 → ℤ
  | 0 => x 0 % 2 ^ 43 + 19 * (x 5 / 2 ^ 40)
  | 1 => x 1 % 2 ^ 43 + x 0 / 2 ^ 43
  | 2 => x 2 % 2 ^ 43 + x 1 / 2 ^ 43
  | 3 => x 3 % 2 ^ 43 + x 2 / 2 ^ 43
  | 4 => x 4 % 2 ^ 43 + x 3 / 2 ^ 43
  | 5 => x 5 % 2 ^ 40 + x 4 / 2 ^ 43

/-- **`fd_r43x6_fold_signed`** on limbs. -/
def foldSignedLimb (x : Fin 6 → ℤ) : Fin 6 → ℤ :=
  fun k => acpLimb (fun j => x j - biasLimb j) k + biasLimb k

/-- **The carry propagate changes the packed value by exactly limb 5's
overflow times `p`** -- `decodeNat_foldLimb_add` over `ℤ`. -/
theorem decodeNat_acpLimb_add (x : Fin 6 → ℤ) :
    decodeNat (acpLimb x) + (p : ℤ) * (x 5 / 2 ^ 40) = decodeNat x := by
  have d0 := Int.ediv_add_emod (x 0) (2 ^ 43)
  have d1 := Int.ediv_add_emod (x 1) (2 ^ 43)
  have d2 := Int.ediv_add_emod (x 2) (2 ^ 43)
  have d3 := Int.ediv_add_emod (x 3) (2 ^ 43)
  have d4 := Int.ediv_add_emod (x 4) (2 ^ 43)
  have d5 := Int.ediv_add_emod (x 5) (2 ^ 40)
  simp only [decodeNat_eq, acpLimb, p]
  push_cast
  omega

/-- `decodeNat` is additive, which is all the bias conjugation needs. -/
theorem decodeNat_sub (x y : Fin 6 → ℤ) :
    decodeNat (fun k => x k - y k) = decodeNat x - decodeNat y := by
  simp only [decodeNat_eq]; ring

theorem decodeNat_add (x y : Fin 6 → ℤ) :
    decodeNat (fun k => x k + y k) = decodeNat x + decodeNat y := by
  simp only [decodeNat_eq]; ring

/-- **Ring correctness of the signed fold**, in `ZMod p`: the bias cancels and
the carry propagate moves a multiple of `p`. -/
theorem decodeNat_foldSignedLimb_zmod (x : Fin 6 → ℤ) :
    ((decodeNat (foldSignedLimb x) : ℤ) : ZMod p) = ((decodeNat x : ℤ) : ZMod p) := by
  have hb := decodeNat_acpLimb_add (fun j => x j - biasLimb j)
  have hsplit : decodeNat (foldSignedLimb x)
      = decodeNat (acpLimb fun j => x j - biasLimb j) + decodeNat biasLimb :=
    decodeNat_add _ _
  have hx : decodeNat (fun j => x j - biasLimb j) = decodeNat x - decodeNat biasLimb :=
    decodeNat_sub _ _
  have : decodeNat (foldSignedLimb x)
      = decodeNat x - (p : ℤ) * ((fun j => x j - biasLimb j) 5 / 2 ^ 40) := by
    rw [hx] at hb
    rw [hsplit]
    linarith
  rw [this]
  push_cast
  simp [ZMod.natCast_self]

/-! ## The tactic

Every call site of the fold does the same two lines: name the vector the four
instructions denote to, and prove it by `denote_foldVec`. The hypothesis name
follows `denote_step_reduce`'s convention, so the value's name is the
hypothesis's with the `h` dropped. -/

open Lean Elab Tactic in
/-- `fold_unsigned hv, z, hz` rewrites the `denote_step_reduce` hypothesis for
the four `fd_r43x6_fold_unsigned` instructions into `hv : v = foldVec z`.

`hz : ∀ i : Fin 6, limbNat z i < 2 ^ 63` is the bound the fold needs of what it
is folding; at a call site it is `limbNat_sqr_lt` or `limbNat_mul_lt`.

    fold_unsigned hv7, (sqrVec a), (limbNat_sqr_lt ha.u47)

`hv7` must be named for its value `v7`, which is what `denote_step_reduce`
produces. -/
elab "fold_unsigned " hv:ident ", " z:term ", " hz:term : tactic => do
  let n := hv.getId.eraseMacroScopes.toString
  unless n.startsWith "h" do
    throwError "fold_unsigned: expected a hypothesis named `h<value>`, got `{n}`"
  let v := mkIdent (Name.mkSimple (n.drop 1).toString)
  evalTactic (← `(tactic|
    replace $hv:ident : $v = (foldVec $z).map PoisonOr.value := by
      rw [$hv:ident]; exact denote_foldVec $z $hz _))

end Firedancer.Avx512
