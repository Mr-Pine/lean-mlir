/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.Firedancer.Avx512.Spec.Vec
import SSA.Projects.Firedancer.Avx512.Spec.Field.fd_r43x6_sqr_fast
import SSA.Projects.Firedancer.Avx512.Spec.Field.fd_r43x6_mul_fast
import SSA.Projects.Firedancer.Avx512.Proof.Common
import SSA.Projects.Firedancer.Proof.Overflow
import SSA.Projects.Firedancer.MLIR.DenoteStep
import SSA.Projects.Firedancer.Avx512.Proof.Long

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

/-! ## `fd_r43x6_fold_signed`, as the eight instructions denote

The signed fold has no `denote_foldVec`-shaped statement: eight instructions
nested is a term no call site could read, and `subst`ing them into one would
put it in the walk's goal. It is stated instead over the eight `denote_eval`
hypotheses, which is the shape a walk already has, and each is rewritten in
place. -/

/-! ### Lane pushes -/

theorem denote_vec_add (a b : Vector (BitVec 64) 8) :
    (Vector.ofFn fun i : Fin 8 => InstCombine.binaryDenote .add
        (a.map PoisonOr.value)[i.val] (b.map PoisonOr.value)[i.val])
      = (Vector.ofFn fun i : Fin 8 => a[i.val] + b[i.val]).map PoisonOr.value := by
  apply Vector.ext
  intro i hi
  simp [InstCombine.binaryDenote, LLVM.add, LLVM.add?]

theorem denote_vec_sub (a b : Vector (BitVec 64) 8) :
    (Vector.ofFn fun i : Fin 8 => InstCombine.binaryDenote .sub
        (a.map PoisonOr.value)[i.val] (b.map PoisonOr.value)[i.val])
      = (Vector.ofFn fun i : Fin 8 => a[i.val] - b[i.val]).map PoisonOr.value := by
  apply Vector.ext
  intro i hi
  simp [InstCombine.binaryDenote, LLVM.sub, LLVM.sub?]

theorem denote_vec_and_const (a : Vector (BitVec 64) 8) (c : Vector Nat 8) :
    (Vector.ofFn fun i : Fin 8 => InstCombine.binaryDenote .and
        (a.map PoisonOr.value)[i.val] (toBitVecValue 64 c)[i.val])
      = (Vector.ofFn fun i : Fin 8 => a[i.val] &&& BitVec.ofNat 64 c[i.val]).map
          PoisonOr.value := by
  apply Vector.ext
  intro i hi
  simp [InstCombine.binaryDenote, LLVM.and, LLVM.and?, toBitVecValue]

/-- The two operands of a vector `add` swap: the `b` twin of a fold emits its
mask and its carries in the other order. -/
theorem denote_vec_add_comm (a b : Vector (LLVM.IntW 64) 8) :
    (Vector.ofFn fun i : Fin 8 => InstCombine.binaryDenote .add a[i.val] b[i.val])
      = (Vector.ofFn fun i : Fin 8 => InstCombine.binaryDenote .add b[i.val] a[i.val]) := by
  apply Vector.ext
  intro i hi
  simp only [Vector.getElem_ofFn, InstCombine.binaryDenote, LLVM.add]
  rcases a[i] with ⟨_ | x⟩ <;> rcases b[i] with ⟨_ | y⟩ <;>
    simp [LLVM.add?, BitVec.add_comm]

theorem denote_vec_add_const (a : Vector (BitVec 64) 8) (c : Vector Nat 8) :
    (Vector.ofFn fun i : Fin 8 => InstCombine.binaryDenote .add
        (a.map PoisonOr.value)[i.val] (toBitVecValue 64 c)[i.val])
      = (Vector.ofFn fun i : Fin 8 => a[i.val] + BitVec.ofNat 64 c[i.val]).map
          PoisonOr.value := by
  apply Vector.ext
  intro i hi
  simp [InstCombine.binaryDenote, LLVM.add, LLVM.add?, toBitVecValue]

theorem denote_vec_ashr_const (a : Vector (BitVec 64) 8) (c : Vector Nat 8)
    (hc : ∀ i : Fin 8, c[i.val] < 64) :
    (Vector.ofFn fun i : Fin 8 => InstCombine.binaryDenote .ashr
        (a.map PoisonOr.value)[i.val] (toBitVecValue 64 c)[i.val])
      = (Vector.ofFn fun i : Fin 8 => a[i.val].sshiftRight c[i.val]).map PoisonOr.value := by
  apply Vector.ext
  intro i hi
  have h : c[i] < 64 := hc ⟨i, hi⟩
  simp only [Vector.getElem_ofFn, Vector.getElem_map, InstCombine.binaryDenote, toBitVecValue,
    LLVM.ashr, PoisonOr.value_bind, Bool.false_eq_true, false_and, if_false, LLVM.ashr?]
  rw [if_neg (by rw [ge_iff_le, BitVec.le_def]; simp; omega),
    BitVec.sshiftRight'_ofNat_eq_sshiftRight, Nat.mod_eq_of_lt (by omega)]

theorem denote_vec_rotate (a : Vector (BitVec 64) 8) :
    LLVM.Ty.vpermi2var (a.map PoisonOr.value) (toBitVecValue 64 #v[5, 0, 1, 2, 3, 4, 8, 8])
        (toBitVecValue 64 #v[0, 0, 0, 0, 0, 0, 0, 0])
      = (#v[a[5], a[0], a[1], a[2], a[3], a[4], 0, 0] : Vector (BitVec 64) 8).map
          PoisonOr.value := by
  apply Vector.ext
  intro i hi
  interval_cases i <;>
    simp [LLVM.Ty.vpermi2var, LLVM.Ty.vpermi2varLane, toBitVecValue]

/-! ### The ℤ bridges -/

def limbVecInt (l : Fin 6 → ℤ) : Vector (BitVec 64) 8 :=
  #v[BitVec.ofInt 64 (l 0), BitVec.ofInt 64 (l 1), BitVec.ofInt 64 (l 2),
     BitVec.ofInt 64 (l 3), BitVec.ofInt 64 (l 4), BitVec.ofInt 64 (l 5), 0, 0]

def acpBiasVec (z : Vector (BitVec 64) 8) : Vector (BitVec 64) 8 :=
  limbVecInt fun k => acpLimb (R43x6.extractLimbs z) k + biasLimb k

theorem and_mask43_int (x : BitVec 64) :
    x &&& 8796093022207#64 = BitVec.ofInt 64 (x.toInt % 2 ^ 43) := by
  conv_lhs => rw [← ofInt_toInt x,
    show (8796093022207#64) = BitVec.ofInt 64 (2 ^ 43 - 1) from by decide]
  exact and_mask_bv _ (by omega)

theorem and_mask40_int (x : BitVec 64) :
    x &&& 1099511627775#64 = BitVec.ofInt 64 (x.toInt % 2 ^ 40) := by
  conv_lhs => rw [← ofInt_toInt x,
    show (1099511627775#64) = BitVec.ofInt 64 (2 ^ 40 - 1) from by decide]
  exact and_mask_bv _ (by omega)

theorem sshiftRight_ofInt (x : BitVec 64) (n : ℕ) :
    x.sshiftRight n = BitVec.ofInt 64 (x.toInt >>> n) := by
  conv_lhs => rw [← ofInt_toInt (x.sshiftRight n)]
  rw [BitVec.toInt_sshiftRight]

private theorem and_ones64 (x : BitVec 64) : x &&& 18446744073709551615#64 = x := by
  bv_decide

private theorem fin6_one : ((1 : Fin 6) : ℕ) = 1 := rfl
private theorem fin6_two : ((2 : Fin 6) : ℕ) = 2 := rfl
private theorem fin6_three : ((3 : Fin 6) : ℕ) = 3 := rfl
private theorem fin6_four : ((4 : Fin 6) : ℕ) = 4 := rfl
private theorem fin6_five : ((5 : Fin 6) : ℕ) = 5 := rfl

private theorem ofNat18 : (18#64 : BitVec 64) = BitVec.ofInt 64 18 := rfl
private theorem ofNatBias0 : (159383552#64 : BitVec 64) = BitVec.ofInt 64 (19 * 2 ^ 23) := rfl
private theorem ofNatBias : (1048576#64 : BitVec 64) = BitVec.ofInt 64 (2 ^ 20) := rfl

/-! ### The eight instructions -/

/-- The carry propagate *before* the bias goes back on: what `%84` holds, and
what a `fd_r43x6_sub_fast` against `u` reads rather than `u` itself -- the
compiler folds `u`'s bias-add into the subtraction's constant. -/
def acpVec (z : Vector (BitVec 64) 8) : Vector (BitVec 64) 8 :=
  limbVecInt (acpLimb (R43x6.extractLimbs z))

theorem denote_acpVec {z : Vector (BitVec 64) 8}
    {a78 a79 a80 a81 a82 a83 a84 : Vector (LLVM.IntW 64) 8}
    (h78 : a78 = Vector.ofFn fun i : Fin 8 => InstCombine.binaryDenote .and
      (z.map PoisonOr.value)[i.val]
      (toBitVecValue 64 #v[8796093022207, 8796093022207, 8796093022207, 8796093022207,
        8796093022207, 1099511627775, 0, 0])[i.val])
    (h79 : a79 = Vector.ofFn fun i : Fin 8 => InstCombine.binaryDenote .ashr
      (z.map PoisonOr.value)[i.val] (toBitVecValue 64 #v[43, 43, 43, 43, 43, 40, 0, 0])[i.val])
    (h80 : a80 = LLVM.Ty.vpermi2var a79 (toBitVecValue 64 #v[5, 0, 1, 2, 3, 4, 8, 8])
      (toBitVecValue 64 #v[0, 0, 0, 0, 0, 0, 0, 0]))
    (h81 : a81 = Vector.ofFn fun i : Fin 8 => InstCombine.binaryDenote .mul
      a80[i.val] (toBitVecValue 64 #v[18, 18, 18, 18, 18, 18, 18, 18])[i.val])
    (h82 : a82 = Vector.ofFn fun i : Fin 8 => InstCombine.binaryDenote .and
      a81[i.val] (toBitVecValue 64 #v[18446744073709551615, 0, 0, 0, 0, 0, 0, 0])[i.val])
    (h83 : a83 = Vector.ofFn fun i : Fin 8 => InstCombine.binaryDenote .add a80[i.val] a78[i.val])
    (h84 : a84 = Vector.ofFn fun i : Fin 8 => InstCombine.binaryDenote .add a83[i.val] a82[i.val]) :
    a84 = (acpVec z).map PoisonOr.value := by
  rw [denote_vec_and_const] at h78
  rw [denote_vec_ashr_const _ _ (by decide)] at h79
  rw [h79, denote_vec_rotate] at h80
  subst h78 h80 h81 h82 h83 h84
  apply Vector.ext
  intro i hi
  interval_cases i <;>
    simp only [Vector.getElem_ofFn, Vector.getElem_map, Vector.getElem_mk, List.getElem_toArray,
      List.getElem_cons_zero, List.getElem_cons_succ, InstCombine.binaryDenote,
      LLVM.mul, LLVM.and, LLVM.add, toBitVecValue, PoisonOr.value_bind,
      LLVM.mul?, LLVM.and?, LLVM.add?, Bool.false_eq_true, false_and, if_false,
      acpVec, limbVecInt, acpLimb, R43x6.extractLimbs,
      LimbRepresentations.toInts, and_mask43_int, and_mask40_int, sshiftRight_ofInt,
      and_ones64, BitVec.and_zero, ofNat18,
      BitVec.add_zero, BitVec.zero_add, Fin.isValue, Fin.val_zero, Fin.val_mk, Fin.val_ofNat,
      Nat.reduceMod, fin6_one, fin6_two, fin6_three, fin6_four, fin6_five,
      ← BitVec.ofInt_mul, ← BitVec.ofInt_add, R43x6.shiftRight_eq, Fin.val_castLE] <;>
    congr 2 <;>
    ring

theorem denote_acpBiasVec {z : Vector (BitVec 64) 8}
    {a78 a79 a80 a81 a82 a83 a84 a85 : Vector (LLVM.IntW 64) 8}
    (h78 : a78 = Vector.ofFn fun i : Fin 8 => InstCombine.binaryDenote .and
      (z.map PoisonOr.value)[i.val]
      (toBitVecValue 64 #v[8796093022207, 8796093022207, 8796093022207, 8796093022207,
        8796093022207, 1099511627775, 0, 0])[i.val])
    (h79 : a79 = Vector.ofFn fun i : Fin 8 => InstCombine.binaryDenote .ashr
      (z.map PoisonOr.value)[i.val] (toBitVecValue 64 #v[43, 43, 43, 43, 43, 40, 0, 0])[i.val])
    (h80 : a80 = LLVM.Ty.vpermi2var a79 (toBitVecValue 64 #v[5, 0, 1, 2, 3, 4, 8, 8])
      (toBitVecValue 64 #v[0, 0, 0, 0, 0, 0, 0, 0]))
    (h81 : a81 = Vector.ofFn fun i : Fin 8 => InstCombine.binaryDenote .mul
      a80[i.val] (toBitVecValue 64 #v[18, 18, 18, 18, 18, 18, 18, 18])[i.val])
    (h82 : a82 = Vector.ofFn fun i : Fin 8 => InstCombine.binaryDenote .and
      a81[i.val] (toBitVecValue 64 #v[18446744073709551615, 0, 0, 0, 0, 0, 0, 0])[i.val])
    (h83 : a83 = Vector.ofFn fun i : Fin 8 => InstCombine.binaryDenote .add a80[i.val] a78[i.val])
    (h84 : a84 = Vector.ofFn fun i : Fin 8 => InstCombine.binaryDenote .add a83[i.val] a82[i.val])
    (h85 : a85 = Vector.ofFn fun i : Fin 8 => InstCombine.binaryDenote .add a84[i.val]
      (toBitVecValue 64 #v[159383552, 1048576, 1048576, 1048576, 1048576, 1048576, 0, 0])[i.val]) :
    a85 = (acpBiasVec z).map PoisonOr.value := by
  rw [denote_vec_and_const] at h78
  rw [denote_vec_ashr_const _ _ (by decide)] at h79
  rw [h79, denote_vec_rotate] at h80
  subst h78 h80 h81 h82 h83 h84 h85
  apply Vector.ext
  intro i hi
  interval_cases i <;>
    simp only [Vector.getElem_ofFn, Vector.getElem_map, Vector.getElem_mk, List.getElem_toArray,
      List.getElem_cons_zero, List.getElem_cons_succ, InstCombine.binaryDenote,
      LLVM.mul, LLVM.and, LLVM.add, toBitVecValue, PoisonOr.value_bind,
      LLVM.mul?, LLVM.and?, LLVM.add?, Bool.false_eq_true, false_and, if_false,
      acpBiasVec, limbVecInt, acpLimb, biasLimb, R43x6.extractLimbs,
      LimbRepresentations.toInts, and_mask43_int, and_mask40_int, sshiftRight_ofInt,
      and_ones64, BitVec.and_zero, ofNat18, ofNatBias0, ofNatBias,
      BitVec.add_zero, BitVec.zero_add, Fin.isValue, Fin.val_zero, Fin.val_mk, Fin.val_ofNat,
      Nat.reduceMod, fin6_one, fin6_two, fin6_three, fin6_four, fin6_five,
      ← BitVec.ofInt_mul, ← BitVec.ofInt_add, R43x6.shiftRight_eq, Fin.val_castLE] <;>
    congr 2 <;>
    ring


/-! ### The same eight, as `fd_r43x6_neg` emits them

The bias goes on first rather than last, and its `add` carries `nsw nuw`. The
sum is the same one -- `ring` does not care about the order -- but the
hypotheses have to match the block syntactically, and the flags have to be
discharged: the left operand is a masked lane, so below `2 ^ 44`, and the bias
is below `2 ^ 28`. -/

/-- **`fd_r43x6_neg`'s bias add does not overflow, signed.** By the time the
lane script reaches it, `and_mask43_int` has turned the masked operand into
`BitVec.ofInt 64 (·.toInt % 2 ^ 43)`, so the bound comes from `Int.emod`
rather than from the mask. -/
private theorem saddOverflow_emod_eq_false {a m b : ℤ} (hm : 0 < m) (hm44 : m ≤ 2 ^ 44)
    (hb0 : 0 ≤ b) (hb : b < 2 ^ 44) :
    (BitVec.ofInt 64 (a % m)).saddOverflow (BitVec.ofInt 64 b) = false := by
  have h0 : 0 ≤ a % m := Int.emod_nonneg a (by omega)
  have h1 : a % m < m := Int.emod_lt_of_pos a hm
  have hfa : R43x6.FitsLong (a % m) := by simp only [R43x6.FitsLong]; omega
  have hfb : R43x6.FitsLong b := by simp only [R43x6.FitsLong]; omega
  simp only [BitVec.saddOverflow, toInt_ofInt hfa, toInt_ofInt hfb, Bool.or_eq_false_iff,
    decide_eq_false_iff_not, not_le, not_lt]
  omega

/-- ... nor unsigned. -/
private theorem uaddOverflow_emod_eq_false {a m b : ℤ} (hm : 0 < m) (hm44 : m ≤ 2 ^ 44)
    (hb0 : 0 ≤ b) (hb : b < 2 ^ 44) :
    (BitVec.ofInt 64 (a % m)).uaddOverflow (BitVec.ofInt 64 b) = false := by
  have h0 : 0 ≤ a % m := Int.emod_nonneg a (by omega)
  have h1 : a % m < m := Int.emod_lt_of_pos a hm
  have hfa : R43x6.FitsLong (a % m) := by simp only [R43x6.FitsLong]; omega
  have hfb : R43x6.FitsLong b := by simp only [R43x6.FitsLong]; omega
  have ha := toNat_ofInt hfa h0
  have hbb := toNat_ofInt hfb hb0
  simp only [BitVec.uaddOverflow, ha, hbb, decide_eq_false_iff_not, not_le]
  omega

/-- The three `(mask, bias)` pairs the fold actually has, as unconditional
rewrites: `simp` will not discharge the general lemma's four numeral side
conditions on its own, and there are only three shapes. -/
private theorem sadd_43_19 (a : ℤ) :
    (BitVec.ofInt 64 (a % 8796093022208)).saddOverflow 159383552#64 = false := by
  rw [show (159383552#64 : BitVec 64) = BitVec.ofInt 64 159383552 from rfl]
  exact saddOverflow_emod_eq_false (by norm_num) (by norm_num) (by norm_num) (by norm_num)

private theorem sadd_43_20 (a : ℤ) :
    (BitVec.ofInt 64 (a % 8796093022208)).saddOverflow 1048576#64 = false := by
  rw [show (1048576#64 : BitVec 64) = BitVec.ofInt 64 1048576 from rfl]
  exact saddOverflow_emod_eq_false (by norm_num) (by norm_num) (by norm_num) (by norm_num)

private theorem sadd_40_20 (a : ℤ) :
    (BitVec.ofInt 64 (a % 1099511627776)).saddOverflow 1048576#64 = false := by
  rw [show (1048576#64 : BitVec 64) = BitVec.ofInt 64 1048576 from rfl]
  exact saddOverflow_emod_eq_false (by norm_num) (by norm_num) (by norm_num) (by norm_num)

private theorem uadd_43_19 (a : ℤ) :
    (BitVec.ofInt 64 (a % 8796093022208)).uaddOverflow 159383552#64 = false := by
  rw [show (159383552#64 : BitVec 64) = BitVec.ofInt 64 159383552 from rfl]
  exact uaddOverflow_emod_eq_false (by norm_num) (by norm_num) (by norm_num) (by norm_num)

private theorem uadd_43_20 (a : ℤ) :
    (BitVec.ofInt 64 (a % 8796093022208)).uaddOverflow 1048576#64 = false := by
  rw [show (1048576#64 : BitVec 64) = BitVec.ofInt 64 1048576 from rfl]
  exact uaddOverflow_emod_eq_false (by norm_num) (by norm_num) (by norm_num) (by norm_num)

private theorem uadd_40_20 (a : ℤ) :
    (BitVec.ofInt 64 (a % 1099511627776)).uaddOverflow 1048576#64 = false := by
  rw [show (1048576#64 : BitVec 64) = BitVec.ofInt 64 1048576 from rfl]
  exact uaddOverflow_emod_eq_false (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- `denote_vec_add_const`'s counterpart at a *constant minus a vector*, which
is how `fd_r43x6_neg` starts. -/
theorem denote_vec_sub_const (c : Vector Nat 8) (a : Vector (BitVec 64) 8) :
    (Vector.ofFn fun i : Fin 8 => InstCombine.binaryDenote .sub
        (toBitVecValue 64 c)[i.val] (a.map PoisonOr.value)[i.val])
      = (Vector.ofFn fun i : Fin 8 => BitVec.ofNat 64 c[i.val] - a[i.val]).map
          PoisonOr.value := by
  apply Vector.ext
  intro i hi
  simp [InstCombine.binaryDenote, LLVM.sub, LLVM.sub?, toBitVecValue]


set_option maxHeartbeats 1000000 in
/-- **`fd_r43x6_fold_signed`, as `fd_r43x6_neg` emits it.**
`denote_acpBiasVec` with two differences the block forces: the three `add`s
come in the other order -- bias, then the rotated carries, then the lane-0
wrap, which `ring` does not care about but `rw` does -- and the bias `add`
carries `nsw nuw`, which `add_nswnuw_and` discharges inside the lane
computation. -/
theorem denote_acpBiasVec_biasFirst {z : Vector (BitVec 64) 8}
    {a226 a227 a228 a229 a230 a231 a232 a233 : Vector (LLVM.IntW 64) 8}
    (h226 : a226 = Vector.ofFn fun i : Fin 8 => InstCombine.binaryDenote .and
      (z.map PoisonOr.value)[i.val]
      (toBitVecValue 64 #v[8796093022207, 8796093022207, 8796093022207, 8796093022207,
        8796093022207, 1099511627775, 0, 0])[i.val])
    (h227 : a227 = Vector.ofFn fun i : Fin 8 => InstCombine.binaryDenote .ashr
      (z.map PoisonOr.value)[i.val] (toBitVecValue 64 #v[43, 43, 43, 43, 43, 40, 0, 0])[i.val])
    (h228 : a228 = LLVM.Ty.vpermi2var a227 (toBitVecValue 64 #v[5, 0, 1, 2, 3, 4, 8, 8])
      (toBitVecValue 64 #v[0, 0, 0, 0, 0, 0, 0, 0]))
    (h229 : a229 = Vector.ofFn fun i : Fin 8 => InstCombine.binaryDenote .mul
      a228[i.val] (toBitVecValue 64 #v[18, 18, 18, 18, 18, 18, 18, 18])[i.val])
    (h230 : a230 = Vector.ofFn fun i : Fin 8 => InstCombine.binaryDenote .and
      a229[i.val] (toBitVecValue 64 #v[18446744073709551615, 0, 0, 0, 0, 0, 0, 0])[i.val])
    (h231 : a231 = Vector.ofFn fun i : Fin 8 =>
      InstCombine.binaryDenote (.add { nsw := true, nuw := true }) a226[i.val]
      (toBitVecValue 64
        #v[159383552, 1048576, 1048576, 1048576, 1048576, 1048576, 0, 0])[i.val])
    (h232 : a232 = Vector.ofFn fun i : Fin 8 => InstCombine.binaryDenote .add
      a231[i.val] a228[i.val])
    (h233 : a233 = Vector.ofFn fun i : Fin 8 => InstCombine.binaryDenote .add
      a232[i.val] a230[i.val]) :
    a233 = (acpBiasVec z).map PoisonOr.value := by
  rw [denote_vec_and_const] at h226
  rw [denote_vec_ashr_const _ _ (by decide)] at h227
  rw [h227, denote_vec_rotate] at h228
  rw [h226] at h231
  subst h228 h229 h230 h231 h232 h233
  apply Vector.ext
  intro i hi
  interval_cases i <;>
    simp only [Vector.getElem_ofFn, Vector.getElem_map, Vector.getElem_mk, List.getElem_toArray,
      List.getElem_cons_zero, List.getElem_cons_succ, InstCombine.binaryDenote,
      LLVM.mul, LLVM.and, toBitVecValue, PoisonOr.value_bind,
      LLVM.add, LLVM.mul?, LLVM.and?, LLVM.add?,
      Bool.false_eq_true, false_and, if_false,
      acpBiasVec, limbVecInt, acpLimb, biasLimb, R43x6.extractLimbs,
      LimbRepresentations.toInts, and_mask43_int, and_mask40_int, sshiftRight_ofInt,
      and_ones64, BitVec.and_zero, ofNat18, ofNatBias0, ofNatBias,
      BitVec.add_zero, BitVec.zero_add, Fin.isValue, Fin.val_zero, Fin.val_mk, Fin.val_ofNat,
      Nat.reduceMod, fin6_one, fin6_two, fin6_three, fin6_four, fin6_five,
      ← BitVec.ofInt_mul, ← BitVec.ofInt_add, R43x6.shiftRight_eq, Fin.val_castLE] <;>
    -- a second pass: the `nsw nuw` guards only appear once `LLVM.add` has
    -- unfolded, and `simp` does not revisit what a rewrite in the same pass
    -- exposes
    (try simp only [true_and]) <;>
    -- `simp` will not rewrite inside an `ite`'s condition here, so the two
    -- guards are taken out by `if_neg` instead
    (try rw [if_neg (by simp [sadd_43_19, sadd_43_20, sadd_40_20] <;> decide),
             if_neg (by simp [uadd_43_19, uadd_43_20, uadd_40_20] <;> decide)]) <;>
    (try simp only [PoisonOr.value_bind, ← BitVec.ofInt_add]) <;>
    congr 2 <;>
    ring


/-! ## The tactic

Every call site of the fold does the same two lines: name the vector the four
instructions denote to, and prove it by `denote_foldVec`. The hypothesis name
follows `denote_step_reduce`'s convention, so the value's name is the
hypothesis's with the `h` dropped. -/

open Lean Elab Tactic in
/-- The `denote_foldVec` half: `hv`'s right-hand side, already the fold's four
instructions over their operands, becomes `foldVec z`.

The `exact` is fenced. `denote_foldVec` is stated over the *raw* denotation, so
a right-hand side a `simp` has reshaped -- or one still naming an operand --
matches nothing syntactically, and unification then falls back to `whnf` on two
very large terms rather than failing. The heartbeat bound turns that into an
error that says what is wrong. -/
private def foldUnsignedAt (hv : Ident) (z hz : Term) : TacticM Unit := do
  let n := hv.getId.eraseMacroScopes.toString
  unless n.startsWith "h" do
    throwError "fold_unsigned: expected a hypothesis named `h<value>`, got `{n}`"
  let v := mkIdent (Name.mkSimple (n.drop 1).toString)
  evalTactic (← `(tactic|
    replace $hv:ident : $v = (foldVec $z).map PoisonOr.value := by
      rw [$hv:ident]
      first
        | set_option maxHeartbeats 200000 in exact denote_foldVec $z $hz _
        | fail "fold_unsigned: the hypothesis is not the fold's four instructions in the \
            form `denote_foldVec` states them. A full `simp` -- `denote_step_reduce` \
            without `only`, say -- reshapes them, and an operand left unfolded matches \
            nothing; use `denote_eval` and `simp only [...]`."))

open Lean Elab Tactic Meta in
/-- The fold's three constants -- mask, shift, multiplier -- as they sit in the
local context: hypotheses `v<i> = toBitVecValue 64 #v[…]` whose value is one of
the three. Found by value rather than named, so a region that declared them
forty instructions before the fold does not have to pass them along. -/
private def foldConstantHyps : TacticM (Array Ident) := withMainContext do
  let terms : Array Term := #[
    ← `(toBitVecValue 64 #v[8796093022207, 8796093022207, 8796093022207, 8796093022207,
        8796093022207, 1099511627775, 0, 0]),
    ← `(toBitVecValue 64 #v[43, 43, 43, 43, 43, 40, 0, 0]),
    ← `(toBitVecValue 64 #v[19, 1, 1, 1, 1, 1, 0, 0])]
  let wanted ← terms.mapM fun t => do instantiateMVars (← Term.elabTerm t none)
  let names := #["mask", "limb widths", "multipliers"]
  let mut found : Array Ident := #[]
  let mut missing : Array String := #[]
  for k in [0 : wanted.size] do
    let mut hit : Option (Ident × Expr) := none
    for decl in ← getLCtx do
      if decl.isImplementationDetail then continue
      let some (_, lhs, rhs) := (← instantiateMVars decl.type).eq? | continue
      -- the left-hand side is a stepped value, or -- after `denote_seal` -- a
      -- read of the sealed valuation; only the constant on the right matters
      unless rhs.isAppOf ``toBitVecValue do continue
      if ← withoutModifyingState (isDefEq rhs wanted[k]!) then
        hit := some (mkIdent decl.userName, lhs)
        break
    match hit with
    | some (i, lhs) =>
      -- after `denote_seal` the constant sits behind a read of the sealed
      -- valuation: `W ⟨192, _⟩ = v6` alongside `v6 = toBitVecValue …`. Both
      -- are needed, the read first.
      if lhs.isFVar then
        for decl in ← getLCtx do
          if decl.isImplementationDetail then continue
          let some (_, _, rhs) := (← instantiateMVars decl.type).eq? | continue
          if rhs == lhs then
            found := found.push (mkIdent decl.userName)
            break
      found := found.push i
    | none => missing := missing.push names[k]!
  unless missing.isEmpty do
    throwError "fold_unsigned: nothing in scope holds the fold's {missing}. Each of the \
      three constants wants its `denote_step_reduce` hypothesis in the value form, \
      `replace hv6 : v6 = toBitVecValue 64 #v[…] := by denote_dense hv6`."
  return found

open Lean Elab Tactic in
/-- `fold_unsigned z, hz` runs the four `fd_r43x6_fold_unsigned` instructions
standing at the walk's position and states what they leave, as
`hv<i> : v<i> = (foldVec z).map PoisonOr.value`.

`hz : ∀ i : Fin 6, limbNat z i < 2 ^ 63` is the bound the fold needs of what it
is folding; at a call site it is `limbNat_sqr_lt` or `limbNat_mul_lt`.

    fold_unsigned (sqrVec ya), (limbNat_sqr_lt hyaU47)

The four indices are read off the goal, and the three constants are found in
the context by their values, so neither has to be named. The constants and the
first three instructions are folded into the last hypothesis by `simp only`: a
`subst` would put them in the *goal*, which on a region-sized walk is what the
naming exists to avoid, and a full `simp` reshapes the fold out of the form
`denote_foldVec` states. The first three are `denote_clear`ed once they are in.

`fold_unsigned hv, z, hz` is the older form, for a walk that has stepped and
reduced the four instructions itself; `hv` must be named for its value `v`. -/
elab "fold_unsigned " args:term,+ : tactic => do
  let args : Array Term := args.getElems
  match args.size with
  | 3 =>
    unless args[0]!.raw.isIdent do
      throwError "fold_unsigned: the three-argument form takes a hypothesis name first, \
        got `{args[0]!}`"
    foldUnsignedAt ⟨args[0]!.raw⟩ args[1]! args[2]!
  | 2 =>
    let z := args[0]!
    let hz := args[1]!
    let lo ← nextStepIndex (← getMainGoal)
    let hi := lo + 3
    let vBase := mkIdent `v
    let loLit := Syntax.mkNumLit (toString lo)
    let hiLit := Syntax.mkNumLit (toString hi)
    evalTactic (← `(tactic| denote_step_all $vBase $hiLit:num))
    evalTactic (← `(tactic| denote_eval $vBase $loLit:num $hiLit:num))
    let target := mkIdent (Name.mkSimple s!"hv{hi}")
    let steps : Array Ident :=
      (Array.range 3).map fun k => mkIdent (Name.mkSimple s!"hv{lo + k}")
    let lemmas : Array Term := ((← foldConstantHyps) ++ steps).map fun i => (i : Term)
    evalTactic (← `(tactic| simp only [$[$lemmas:term],*] at $target:ident))
    -- the first three are spent once they are folded in
    evalTactic (← `(tactic| denote_clear $vBase $loLit:num
      $(Syntax.mkNumLit (toString (lo + 2))):num))
    foldUnsignedAt target z hz
  | n => throwError "fold_unsigned: expected `z, hz` or `hv, z, hz`, got {n} arguments"

end Firedancer.Avx512
