import SSA.Projects.Firedancer.Avx512.Mlir.fd_r43x6_sqr_fast
import SSA.Projects.Firedancer.Avx512.Denote.fd_r43x6_sqr_fast
import SSA.Projects.Firedancer.Avx512.R43x6
import SSA.Projects.Firedancer.MLIR.DenoteStep
import SSA.Projects.Firedancer.MLIR.Poison
import SSA.Projects.Firedancer.Ed25519
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.IntervalCases

/-!
# `fd_r43x6_sqr_fast` squares its input in `ZMod p`

Denoting the lifted SLLVM program and decoding the six output limbs yields the
square of the decoded input in `GF(2^255 - 19)`.

The proof composes three layers:

* `denote_fd_r43x6_sqr_fast` (`Avx512/Denote/`): the denotation is the lane
  expression `sqrFastResult`;
* `pack_sqLimb_zmod`: ring correctness of the ℕ-level limbs `sqLimb`;
* `sqrFastResult_eq`: each output lane is `BitVec.ofNat 64` of `sqLimb`.

`fd_r43x6_sqr_fast` is *not* `fd_r43x6_mul_fast x x`: doubling of the
off-diagonal partial products happens *before* the multiplications rather than
after. The products formed are therefore `x i * x i` on the diagonal and
`(2 * x i) * x j` for `i < j` — twenty-one, against the thirty-six of a general
multiply.

## Hypotheses

Both are required, and both are the contract stated in `fd_r43x6.h` ("x is an
unreduced fd_r43x6_t (i.e. in u47).  Assumes lanes 6 and 7 of x are zero"):

* `hx : Unreduced x`. At `2^50` limbs the output limbs exceed `2^63` and
  `BitVec.toInt` reads them as negative.
* `h7 : x[7] = 0`. Lane 7 is a don't-care slot of the `wwl_permute` masks, so
  its square reaches output lanes 1-4. On `x = ⟨0,…,0,1⟩` the program returns
  `⟨0,306,0,2,0,0,0,0⟩`, decoding to `306·2^43 + 2·2^129` rather than `0`.

`h6` belongs to that contract but is unused: `x[6]` occurs in no output lane.
-/

namespace Firedancer.Avx512
open LeanMLIR SLLVM
open InstCombine (LLVM)

/-! ## The ℕ-level specification

Every product formed by the implementation is split by the `vpmadd52lo`/`hi`
pair into

    pl a b = (a·b) % 2^52          -- vpmadd52luq
    ph a b = (a·b) / 2^52 * 2^9    -- vpmadd52huq, prescaled by 2^9

so that `pl a b + 2^43·(ph a b) = a·b` (note `2^52 = 2^43·2^9`). Grouping by
scale factor `2^43k` gives twelve column sums, and the fold uses
`2^258 ≡ 152 (mod p)` to produce the six output limbs

    sqLimb k = sqCol k + 152·sqCol (k+6),   k = 0,…,5.
-/

/-- Low 52 bits of a limb product, as `vpmadd52luq` computes them. -/
def pl (a b : ℕ) : ℕ := a * b % 2^52

/-- High bits of a limb product, prescaled by `2^9` (the `wwl_shl(…, 9)`
applied to every `vpmadd52huq` result), so that `pl a b + 2^43 * ph a b = a*b`. -/
def ph (a b : ℕ) : ℕ := a * b / 2^52 * 2^9

theorem pl_add_shift_ph (a b : ℕ) : pl a b + 2^43 * ph a b = a * b := by
  simp only [pl, ph]
  omega

theorem pl_lt (a b : ℕ) : pl a b < 2^52 :=
  Nat.mod_lt _ (by norm_num)

/-- Decode limbs into the natural number they represent: `Σ_{k<6} l k · 2^(43k)`. -/
def pack (l : ℕ → ℕ) : ℕ :=
  l 0 + 2^43 * l 1 + 2^86 * l 2 + 2^129 * l 3 + 2^172 * l 4 + 2^215 * l 5

/-- The column sums of the squaring: `sqCol x k` is the coefficient of
`2^(43k)` before folding, read off the lanes of `sqrFastResult`. For `k < 6`
this is the `za` half of lane `k`, and `sqCol (k+6)` is the `zb` half. -/
def sqCol (x : ℕ → ℕ) : ℕ → ℕ
  | 0 => pl (x 0) (x 0)
  | 1 => pl (2 * x 0) (x 1)
      + ph (x 0) (x 0)
  | 2 => pl (x 1) (x 1) + pl (2 * x 0) (x 2)
      + ph (2 * x 0) (x 1)
  | 3 => pl (2 * x 1) (x 2) + pl (2 * x 0) (x 3)
      + ph (x 1) (x 1) + ph (2 * x 0) (x 2)
  | 4 => pl (2 * x 1) (x 3) + pl (2 * x 0) (x 4) + pl (x 2) (x 2)
      + ph (2 * x 1) (x 2) + ph (2 * x 0) (x 3)
  | 5 => pl (2 * x 1) (x 4) + pl (2 * x 0) (x 5) + pl (2 * x 2) (x 3)
      + ph (2 * x 1) (x 3) + ph (2 * x 0) (x 4) + ph (x 2) (x 2)
  | 6 => pl (2 * x 1) (x 5) + pl (x 3) (x 3) + pl (2 * x 2) (x 4)
      + ph (2 * x 1) (x 4) + ph (2 * x 0) (x 5) + ph (2 * x 2) (x 3)
  | 7 => pl (2 * x 3) (x 4) + pl (2 * x 2) (x 5)
      + ph (2 * x 1) (x 5) + ph (x 3) (x 3) + ph (2 * x 2) (x 4)
  | 8 => pl (2 * x 3) (x 5) + pl (x 4) (x 4)
      + ph (2 * x 3) (x 4) + ph (2 * x 2) (x 5)
  | 9 => pl (2 * x 4) (x 5)
      + ph (2 * x 3) (x 5) + ph (x 4) (x 4)
  | 10 => pl (x 5) (x 5)
      + ph (2 * x 4) (x 5)
  | 11 => ph (x 5) (x 5)
  | _ => 0

/-- The output limbs of `fd_r43x6_sqr_fast`: the low six columns, plus the
high six folded in with weight `152 = 2^258 mod p`. -/
def sqLimb (x : ℕ → ℕ) (k : ℕ) : ℕ :=
  sqCol x k + 152 * sqCol x (k + 6)

/-! ## Ring correctness -/

set_option exponentiation.threshold 600 in
/-- The twelve columns decode to the full square: each of the twenty-one
products appears exactly once, at the weight `2^(43(i+j))` of its column. -/
theorem sqCols_sq (x : ℕ → ℕ) :
    (pack x) ^ 2 =
      sqCol x 0 + 2^43 * sqCol x 1 + 2^86 * sqCol x 2 + 2^129 * sqCol x 3
      + 2^172 * sqCol x 4 + 2^215 * sqCol x 5 + 2^258 * sqCol x 6
      + 2^301 * sqCol x 7 + 2^344 * sqCol x 8 + 2^387 * sqCol x 9
      + 2^430 * sqCol x 10 + 2^473 * sqCol x 11 := by
  simp only [pack, sqCol]
  -- The twenty-one products formed by the implementation.
  have d0 := pl_add_shift_ph (x 0) (x 0)
  have d1 := pl_add_shift_ph (x 1) (x 1)
  have d2 := pl_add_shift_ph (x 2) (x 2)
  have d3 := pl_add_shift_ph (x 3) (x 3)
  have d4 := pl_add_shift_ph (x 4) (x 4)
  have d5 := pl_add_shift_ph (x 5) (x 5)
  have h01 := pl_add_shift_ph (2 * x 0) (x 1)
  have h02 := pl_add_shift_ph (2 * x 0) (x 2)
  have h03 := pl_add_shift_ph (2 * x 0) (x 3)
  have h04 := pl_add_shift_ph (2 * x 0) (x 4)
  have h05 := pl_add_shift_ph (2 * x 0) (x 5)
  have h12 := pl_add_shift_ph (2 * x 1) (x 2)
  have h13 := pl_add_shift_ph (2 * x 1) (x 3)
  have h14 := pl_add_shift_ph (2 * x 1) (x 4)
  have h15 := pl_add_shift_ph (2 * x 1) (x 5)
  have h23 := pl_add_shift_ph (2 * x 2) (x 3)
  have h24 := pl_add_shift_ph (2 * x 2) (x 4)
  have h25 := pl_add_shift_ph (2 * x 2) (x 5)
  have h34 := pl_add_shift_ph (2 * x 3) (x 4)
  have h35 := pl_add_shift_ph (2 * x 3) (x 5)
  have h45 := pl_add_shift_ph (2 * x 4) (x 5)
  calc (x 0 + 2^43 * x 1 + 2^86 * x 2 + 2^129 * x 3 + 2^172 * x 4 + 2^215 * x 5) ^ 2
      = (x 0 * x 0)
        + 2^43 * ((2 * x 0) * x 1)
        + 2^86 * (x 1 * x 1 + (2 * x 0) * x 2)
        + 2^129 * ((2 * x 1) * x 2 + (2 * x 0) * x 3)
        + 2^172 * ((2 * x 1) * x 3 + (2 * x 0) * x 4 + x 2 * x 2)
        + 2^215 * ((2 * x 1) * x 4 + (2 * x 0) * x 5 + (2 * x 2) * x 3)
        + 2^258 * ((2 * x 1) * x 5 + x 3 * x 3 + (2 * x 2) * x 4)
        + 2^301 * ((2 * x 3) * x 4 + (2 * x 2) * x 5)
        + 2^344 * ((2 * x 3) * x 5 + x 4 * x 4)
        + 2^387 * ((2 * x 4) * x 5)
        + 2^430 * (x 5 * x 5) := by ring
    _ = _ := by
        rw [← d0, ← d1, ← d2, ← d3, ← d4, ← d5,
            ← h01, ← h02, ← h03, ← h04, ← h05,
            ← h12, ← h13, ← h14, ← h15,
            ← h23, ← h24, ← h25,
            ← h34, ← h35, ← h45]
        ring

/-- **Ring correctness**: decoding the output limbs of `fd_r43x6_sqr_fast`
yields the square of the decoded input modulo `p = 2^255 - 19`. -/
theorem pack_sqLimb_modEq (x : ℕ → ℕ) :
    pack (sqLimb x) ≡ (pack x) ^ 2 [MOD p] := by
  -- The high columns contribute a multiple of `p`, since `2^258 - 152 = 8·p`.
  have hsplit : pack (sqLimb x)
      + p * (8 * (sqCol x 6 + 2^43 * sqCol x 7 + 2^86 * sqCol x 8
          + 2^129 * sqCol x 9 + 2^172 * sqCol x 10 + 2^215 * sqCol x 11))
      = (pack x) ^ 2 := by
    rw [sqCols_sq]
    simp only [pack, sqLimb, p]
    generalize sqCol x 0 = c0; generalize sqCol x 1 = c1
    generalize sqCol x 2 = c2; generalize sqCol x 3 = c3
    generalize sqCol x 4 = c4; generalize sqCol x 5 = c5
    generalize sqCol x 6 = c6; generalize sqCol x 7 = c7
    generalize sqCol x 8 = c8; generalize sqCol x 9 = c9
    generalize sqCol x 10 = c10; generalize sqCol x 11 = c11
    omega
  show _ % _ = _ % _
  conv_rhs => rw [← hsplit]
  rw [Nat.add_mul_mod_self_left]

/-- Ring correctness, stated in `ZMod p`. -/
theorem pack_sqLimb_zmod (x : ℕ → ℕ) :
    ((pack (sqLimb x) : ℕ) : ZMod p) = ((pack x : ℕ) : ZMod p) ^ 2 := by
  have h := pack_sqLimb_modEq x
  have := (ZMod.natCast_eq_natCast_iff _ _ _).mpr h
  simpa [Nat.cast_pow] using this

/-! ## Bounds

Counting `pl`s (`< 2^52`) and `ph`s (`< 2^52`) per column, the worst limb is
`sqLimb 0 < (2 + 152 * 12) · 2^51 = 1826 · 2^51`, against `2^63 = 4096 · 2^51`.
The margin is what lets the 64-bit lanes hold the result as a non-negative
`BitVec.toInt`. -/

/-- With a doubled left operand (`< 2^48`) and an unreduced right operand
(`< 2^47`), the high half is `< 2^52`. Doubling before multiplying is why the
bound is `2^52` and not the `2^51` a general multiply would give. -/
theorem ph_lt_two_pow_52 {a b : ℕ} (ha : a < 2^48) (hb : b < 2^47) :
    ph a b < 2^52 := by
  have hab : a * b < 2^95 := by
    calc a * b ≤ 2^48 * b := Nat.mul_le_mul_right _ (Nat.le_of_lt ha)
    _ < 2^48 * 2^47 := by omega
    _ = 2^95 := by norm_num
  simp only [ph]
  omega

set_option maxHeartbeats 1000000 in
/-- **Output bounds**: on unreduced inputs (limbs `< 2^47`), every output limb
of `fd_r43x6_sqr_fast` is `< 2^63`, so the 64-bit lanes neither overflow nor
become negative when read back with `BitVec.toInt`. -/
theorem sqLimb_lt_two_pow_63 (x : ℕ → ℕ) (hx : ∀ i < 6, x i < 2^47)
    (k : ℕ) (hk : k < 6) :
    sqLimb x k < 2^63 := by
  have hd : ∀ i < 6, 2 * x i < 2^48 := fun i hi => by have := hx i hi; omega
  have hpl : ∀ a b : ℕ, pl a b < 2^52 := fun a b => pl_lt a b
  have hph : ∀ i < 6, ∀ j < 6, ph (2 * x i) (x j) < 2^52 :=
    fun i hi j hj => ph_lt_two_pow_52 (hd i hi) (hx j hj)
  have hphd : ∀ i < 6, ph (x i) (x i) < 2^52 := fun i hi =>
    ph_lt_two_pow_52 (by have := hx i hi; omega) (hx i hi)
  interval_cases k <;>
  · simp only [sqLimb, sqCol]
    have := hpl (x 0) (x 0); have := hpl (x 1) (x 1); have := hpl (x 2) (x 2)
    have := hpl (x 3) (x 3); have := hpl (x 4) (x 4); have := hpl (x 5) (x 5)
    have := hpl (2 * x 0) (x 1); have := hpl (2 * x 0) (x 2)
    have := hpl (2 * x 0) (x 3); have := hpl (2 * x 0) (x 4)
    have := hpl (2 * x 0) (x 5); have := hpl (2 * x 1) (x 2)
    have := hpl (2 * x 1) (x 3); have := hpl (2 * x 1) (x 4)
    have := hpl (2 * x 1) (x 5); have := hpl (2 * x 2) (x 3)
    have := hpl (2 * x 2) (x 4); have := hpl (2 * x 2) (x 5)
    have := hpl (2 * x 3) (x 4); have := hpl (2 * x 3) (x 5)
    have := hpl (2 * x 4) (x 5)
    have h0 := hphd 0 (by omega); have h1 := hphd 1 (by omega)
    have h2 := hphd 2 (by omega); have h3 := hphd 3 (by omega)
    have h4 := hphd 4 (by omega); have h5 := hphd 5 (by omega)
    have := hph 0 (by omega) 1 (by omega); have := hph 0 (by omega) 2 (by omega)
    have := hph 0 (by omega) 3 (by omega); have := hph 0 (by omega) 4 (by omega)
    have := hph 0 (by omega) 5 (by omega); have := hph 1 (by omega) 2 (by omega)
    have := hph 1 (by omega) 3 (by omega); have := hph 1 (by omega) 4 (by omega)
    have := hph 1 (by omega) 5 (by omega); have := hph 2 (by omega) 3 (by omega)
    have := hph 2 (by omega) 4 (by omega); have := hph 2 (by omega) 5 (by omega)
    have := hph 3 (by omega) 4 (by omega); have := hph 3 (by omega) 5 (by omega)
    have := hph 4 (by omega) 5 (by omega)
    omega

/-! ## `BitVec`/ℕ transfer

A lane is built only from operations that wrap mod `2^64`, so each is a
`BitVec.ofNat` homomorphism. These lemmas push `ofNat` outward until a whole
lane is a single `ofNat`. Only `toNat_shl1` and `hi_eq` need bounds; the rest
hold unconditionally. -/

/-- `<<<` on `BitVec` is LeanMLIR's shift-by-`BitVec`, i.e. shift by `k.toNat`. -/
private theorem ofNat_shl (a : Nat) (k : BitVec 64) :
    (BitVec.ofNat 64 a) <<< k = BitVec.ofNat 64 (a * 2 ^ k.toNat) := by
  show (BitVec.ofNat 64 a) <<< k.toNat = _
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mod_mul_mod]

/-- The `<<< 7` of the `za + 152*zb` fold. -/
private theorem ofNat_shl7 (a : Nat) :
    (BitVec.ofNat 64 a) <<< (7 : BitVec 64) = BitVec.ofNat 64 (a * 128) := by
  rw [ofNat_shl, show (7 : BitVec 64).toNat = 7 from rfl]
  norm_num

/-! Numeric literals in a lane are `BitVec.ofNat`, but reach the goal as
`Nat.cast` or as `OfNat` and so do not match it syntactically. -/

private theorem natCast_bv (n : Nat) : ((n : Nat) : BitVec 64) = BitVec.ofNat 64 n := rfl

private theorem bv_zero : (0 : BitVec 64) = BitVec.ofNat 64 0 := rfl

/-- The `* 24` of the `za + 152*zb` fold (`152 = 128 + 24`). -/
private theorem ofNat_mul24 (a : Nat) :
    (BitVec.ofNat 64 a) * (24 : BitVec 64) = BitVec.ofNat 64 (a * 24) := by
  rw [show (24 : BitVec 64) = BitVec.ofNat 64 24 from rfl, ← BitVec.ofNat_mul]

/-- The pre-multiply doubling of the off-diagonal terms. -/
private theorem toNat_shl1 (a : BitVec 64) (ha : a.toNat < 2^47) :
    (a <<< (1 : BitVec 64)).toNat = 2 * a.toNat := by
  show (a <<< (1 : BitVec 64).toNat).toNat = _
  simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  omega

/-- `vpmadd52lo` is `pl`, unconditionally: both truncate mod `2^52`. -/
private theorem lo_eq (a b : BitVec 64) :
    mulLo52 a b = BitVec.ofNat 64 (pl a.toNat b.toNat) := by
  simp [mulLo52, pl, Nat.mod_mul_mod]

/-- `vpmadd52hi` followed by `wwl_shl(…,9)` is `ph`. Unlike `lo_eq` this needs
the operand bounds: otherwise the implicit truncation to 52 bits is lossy. -/
private theorem hi_eq (a b : BitVec 64) (ha : a.toNat < 2^52) (hb : b.toNat < 2^52) :
    mulHi52 a b <<< (9 : BitVec 64) = BitVec.ofNat 64 (ph a.toNat b.toNat) := by
  rw [mulHi52, ofNat_shl, ph, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb,
      show (9 : BitVec 64).toNat = 9 from rfl]

/-- A lane below `2^63` reads back as itself, rather than as a negative. -/
private theorem ofNat_toInt {n : Nat} (h : n < 2^63) :
    (BitVec.ofNat 64 n).toInt = (n : Int) := by
  have h64 : n < 2^64 := by omega
  have ht : (BitVec.ofNat 64 n).toNat = n := by rw [BitVec.toNat_ofNat]; omega
  rw [BitVec.toInt_eq_toNat_of_lt (by rw [ht]; omega), ht]

/-! The lane-7 products, which `h7` eliminates. -/

private theorem pl_zero : pl 0 0 = 0 := by simp [pl]

private theorem ph_zero : ph 0 0 = 0 := by simp [ph]

/-- An input limb is below `2^63`, so it too reads back as a natural. -/
private theorem toInt_of_lt {a : BitVec 64} (h : a.toNat < 2^47) :
    a.toInt = (a.toNat : Int) :=
  BitVec.toInt_eq_toNat_of_lt (by omega)

/-- `decode'` on a literal vector: the low six lanes with radix-`2^43` weights. -/
private theorem decode'_lit (a b c d e f g h : BitVec 64) :
    R43x6.decode' #v[a,b,c,d,e,f,g,h] = a.toInt + 2^43 * b.toInt + 2^86 * c.toInt
      + 2^129 * d.toInt + 2^172 * e.toInt + 2^215 * f.toInt := by
  simp [R43x6.decode', R43x6.decode, LimbRepresentations.decode,
    LimbRepresentations.placeValues, R43x6.limbCount, R43x6.baseBits, R43x6.limbWidth,
    show (Vector.range 6 : Vector Nat 6) = #v[0,1,2,3,4,5] from rfl, Vector.sum]
  ring

/-! ## The lanes -/

/-- The input limbs as naturals, in the `ℕ → ℕ` form `sqLimb` takes. -/
def limbNat (x : Vector (BitVec 64) 8) : ℕ → ℕ
  | 0 => x[0].toNat
  | 1 => x[1].toNat
  | 2 => x[2].toNat
  | 3 => x[3].toNat
  | 4 => x[4].toNat
  | 5 => x[5].toNat
  | _ => 0

/-- The result vector predicted by the ℕ-level specification. -/
def sqrVec (x : Vector (BitVec 64) 8) : Vector (BitVec 64) 8 :=
  #v[BitVec.ofNat 64 (sqLimb (limbNat x) 0), BitVec.ofNat 64 (sqLimb (limbNat x) 1),
     BitVec.ofNat 64 (sqLimb (limbNat x) 2), BitVec.ofNat 64 (sqLimb (limbNat x) 3),
     BitVec.ofNat 64 (sqLimb (limbNat x) 4), BitVec.ofNat 64 (sqLimb (limbNat x) 5),
     0, 0]

set_option maxHeartbeats 4000000 in
/-- **Lane derivation**: on an unreduced input with lane 7 zero, every output
lane of `fd_r43x6_sqr_fast` is the corresponding ℕ-level limb reduced mod
`2^64`. The reduction is the identity, by `sqLimb_lt_two_pow_63`. -/
theorem sqrFastResult_eq (x : Vector (BitVec 64) 8) (hx : Unreduced x) (h7 : x[7] = 0) :
    sqrFastResult x = (sqrVec x).map PoisonOr.value := by
  have b0 : x[0].toNat < 2^47 := hx 0 (by omega)
  have b1 : x[1].toNat < 2^47 := hx 1 (by omega)
  have b2 : x[2].toNat < 2^47 := hx 2 (by omega)
  have b3 : x[3].toNat < 2^47 := hx 3 (by omega)
  have b4 : x[4].toNat < 2^47 := hx 4 (by omega)
  have b5 : x[5].toNat < 2^47 := hx 5 (by omega)
  have b7 : x[7].toNat = 0 := by rw [h7]; rfl
  have b7' : x[7].toNat < 2^47 := by omega
  have s0 : 2 * x[0].toNat < 2^52 := by omega
  have s1 : 2 * x[1].toNat < 2^52 := by omega
  have s2 : 2 * x[2].toNat < 2^52 := by omega
  have s3 : 2 * x[3].toNat < 2^52 := by omega
  have s4 : 2 * x[4].toNat < 2^52 := by omega
  have s7 : 2 * x[7].toNat < 2^52 := by omega
  have t0 : x[0].toNat < 2^52 := by omega
  have t1 : x[1].toNat < 2^52 := by omega
  have t2 : x[2].toNat < 2^52 := by omega
  have t3 : x[3].toNat < 2^52 := by omega
  have t4 : x[4].toNat < 2^52 := by omega
  have t5 : x[5].toNat < 2^52 := by omega
  have t7 : x[7].toNat < 2^52 := by omega
  apply Vector.ext
  intro i hi
  -- Lanes 6 and 7 are identically zero and close on the first `simp only`, so
  -- the later steps are `try`ed and the six real lanes share one script.
  interval_cases i <;>
    · simp only [sqrFastResult, sqrVec, Vector.getElem_map, Vector.getElem_mk,
        List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
      try congr 1
      try simp only [lo_eq, hi_eq, s0, s1, s2, s3, s4, s7, t0, t1, t2, t3, t4, t5, t7,
        toNat_shl1, b0, b1, b2, b3, b4, b7',
        natCast_bv, bv_zero, ← BitVec.ofNat_add, ofNat_mul24, ofNat_shl7]
      try congr 1
      try simp only [sqLimb, sqCol, limbNat, b7, Nat.mul_zero, pl_zero, ph_zero]
      try ring

set_option maxHeartbeats 1000000 in
/-- **Specification of `fd_r43x6_sqr_fast`**: on an unreduced input whose two
high lanes are zero, the six output limbs decode to the square of the decoded
input in `GF(2^255 - 19)`. Concluding `.value` also asserts the result is
poison-free in every lane. -/
theorem spec_fd_r43x6_sqr_fast (x : Vector (BitVec 64) 8)
    (hx : Unreduced x) (h6 : x[6] = 0) (h7 : x[7] = 0) :
    (fun l => (R43x6.decode' l : ZMod p)) <$>
        (fd_r43x6_sqr_fast.denote
          (Ctxt.Valuation.singleton (x.map PoisonOr.value))).head.getValues
      = .value ((R43x6.decode' x : ZMod p)^2) := by
  have b0 : x[0].toNat < 2^47 := hx 0 (by omega)
  have b1 : x[1].toNat < 2^47 := hx 1 (by omega)
  have b2 : x[2].toNat < 2^47 := hx 2 (by omega)
  have b3 : x[3].toNat < 2^47 := hx 3 (by omega)
  have b4 : x[4].toNat < 2^47 := hx 4 (by omega)
  have b5 : x[5].toNat < 2^47 := hx 5 (by omega)
  have hbnd : ∀ i < 6, limbNat x i < 2^47 := by
    intro i hi
    interval_cases i <;> simpa [limbNat] using ‹_›
  -- 1. denotation to lanes to specified limbs; the poison layer collapses
  rw [denote_fd_r43x6_sqr_fast, sqrFastResult_eq x hx h7]
  simp only [HVector.head, Vector.getValues_map_value, PoisonOr.map_value,
    PoisonOr.value_inj]
  -- 2. decode both sides into explicit sums
  have hx8 : x = #v[x[0],x[1],x[2],x[3],x[4],x[5],x[6],x[7]] := by
    apply Vector.ext; intro i hi; interval_cases i <;> rfl
  have hdx : R43x6.decode' x = (limbNat x 0 : Int) + 2^43 * limbNat x 1
      + 2^86 * limbNat x 2 + 2^129 * limbNat x 3 + 2^172 * limbNat x 4
      + 2^215 * limbNat x 5 := by
    conv_lhs => rw [hx8]
    rw [decode'_lit, toInt_of_lt b0, toInt_of_lt b1, toInt_of_lt b2,
      toInt_of_lt b3, toInt_of_lt b4, toInt_of_lt b5]
    simp [limbNat]
  rw [sqrVec, decode'_lit, hdx,
    ofNat_toInt (sqLimb_lt_two_pow_63 _ hbnd 0 (by omega)),
    ofNat_toInt (sqLimb_lt_two_pow_63 _ hbnd 1 (by omega)),
    ofNat_toInt (sqLimb_lt_two_pow_63 _ hbnd 2 (by omega)),
    ofNat_toInt (sqLimb_lt_two_pow_63 _ hbnd 3 (by omega)),
    ofNat_toInt (sqLimb_lt_two_pow_63 _ hbnd 4 (by omega)),
    ofNat_toInt (sqLimb_lt_two_pow_63 _ hbnd 5 (by omega))]
  -- 3. both sides are now casts of `pack`, so `pack_sqLimb_zmod` applies
  rw [show ((sqLimb (limbNat x) 0 : Int) + 2^43 * sqLimb (limbNat x) 1
        + 2^86 * sqLimb (limbNat x) 2 + 2^129 * sqLimb (limbNat x) 3
        + 2^172 * sqLimb (limbNat x) 4 + 2^215 * sqLimb (limbNat x) 5)
      = ((pack (sqLimb (limbNat x)) : ℕ) : Int) from by simp [pack]; try ring,
    show ((limbNat x 0 : Int) + 2^43 * limbNat x 1 + 2^86 * limbNat x 2
        + 2^129 * limbNat x 3 + 2^172 * limbNat x 4 + 2^215 * limbNat x 5)
      = ((pack (limbNat x) : ℕ) : Int) from by simp [pack]; try ring]
  push_cast
  exact pack_sqLimb_zmod (limbNat x)

end Firedancer.Avx512
