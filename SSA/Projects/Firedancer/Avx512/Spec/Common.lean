/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.Firedancer.Avx512.Denote.Common
import SSA.Projects.Firedancer.Avx512.R43x6
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring

/-!
# Shared ℕ-level machinery for the `fd_r43x6` specifications

Every `fd_r43x6` multiply-like operation splits its limb products with the
`vpmadd52lo`/`hi` pair into

    pl a b = (a·b) % 2^52          -- vpmadd52luq
    ph a b = (a·b) / 2^52 * 2^9    -- vpmadd52huq, prescaled by 2^9

so that `pl a b + 2^43·(ph a b) = a·b` (note `2^52 = 2^43·2^9`), and then
folds the resulting radix-`2^43` columns with `2^258 ≡ 152 (mod p)`. This
file holds the split, the `pack` decoding of six limbs, bounds on `pl`/`ph`,
and the `BitVec`/ℕ transfer lemmas that read a lane expression built from
`mulLo52`/`mulHi52` back as a single `BitVec.ofNat` of a `pl`/`ph` sum.

The per-operation column sums (`sqCol`/`col`) and their ring/bounds theorems
live in the respective `Avx512/Spec/fd_r43x6_*.lean` files.
-/

namespace Firedancer.Avx512
open LeanMLIR SLLVM
open InstCombine (LLVM)

/-! ## The `pl`/`ph` split -/

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

/-! ## Bounds on `ph`

Every `pl` is `< 2^52` unconditionally; a `ph` bound depends on the width of
its operands. -/

/-- `ph a b < B * 2^9` whenever `a * b < B * 2^52`. -/
theorem ph_lt_of_mul_lt {a b B : ℕ} (h : a * b < B * 2^52) :
    ph a b < B * 2^9 := by
  have hdiv : a * b / 2^52 < B := Nat.div_lt_of_lt_mul (by omega)
  simp only [ph]
  omega

/-- `ph_lt_of_mul_lt` in the form the operand bounds supply it. -/
theorem ph_lt_bound {a b u v B : ℕ} (ha : a < u) (hb : b < v)
    (h : u * v ≤ B * 2^52) : ph a b < B * 2^9 :=
  ph_lt_of_mul_lt (by
    have hm : a * b < u * v := Nat.mul_lt_mul_of_lt_of_lt ha hb
    omega)

/-! The products a zero limb (a hypothesised-zero lane 6 or 7) eliminates. -/

theorem pl_zero_left (b : ℕ) : pl 0 b = 0 := by simp [pl]

theorem pl_zero_right (a : ℕ) : pl a 0 = 0 := by simp [pl]

theorem ph_zero_left (b : ℕ) : ph 0 b = 0 := by simp [ph]

theorem ph_zero_right (a : ℕ) : ph a 0 = 0 := by simp [ph]

/-! ## `BitVec`/ℕ transfer

A lane is built only from operations that wrap mod `2^64`, so each is a
`BitVec.ofNat` homomorphism. These lemmas push `ofNat` outward until a whole
lane is a single `ofNat`. Only `toNat_shl1` and `hi_eq` need bounds; the rest
hold unconditionally. -/

/-- `<<<` on `BitVec` is LeanMLIR's shift-by-`BitVec`, i.e. shift by `k.toNat`. -/
theorem ofNat_shl (a : Nat) (k : BitVec 64) :
    (BitVec.ofNat 64 a) <<< k = BitVec.ofNat 64 (a * 2 ^ k.toNat) := by
  show (BitVec.ofNat 64 a) <<< k.toNat = _
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mod_mul_mod]

/-- The `<<< 7` of the `za + 152*zb` fold. -/
theorem ofNat_shl7 (a : Nat) :
    (BitVec.ofNat 64 a) <<< (7 : BitVec 64) = BitVec.ofNat 64 (a * 128) := by
  rw [ofNat_shl, show (7 : BitVec 64).toNat = 7 from rfl]
  norm_num

/-! Numeric literals in a lane are `BitVec.ofNat`, but reach the goal as
`Nat.cast` or as `OfNat` and so do not match it syntactically. -/

theorem natCast_bv (n : Nat) : ((n : Nat) : BitVec 64) = BitVec.ofNat 64 n := rfl

theorem bv_zero : (0 : BitVec 64) = BitVec.ofNat 64 0 := rfl

/-- The `* 24` of the `za + 152*zb` fold (`152 = 128 + 24`). -/
theorem ofNat_mul24 (a : Nat) :
    (BitVec.ofNat 64 a) * (24 : BitVec 64) = BitVec.ofNat 64 (a * 24) := by
  rw [show (24 : BitVec 64) = BitVec.ofNat 64 24 from rfl, ← BitVec.ofNat_mul]

/-- The pre-multiply doubling of off-diagonal terms (`fd_r43x6_sqr_fast`). -/
theorem toNat_shl1 (a : BitVec 64) (ha : a.toNat < 2^47) :
    (a <<< (1 : BitVec 64)).toNat = 2 * a.toNat := by
  show (a <<< (1 : BitVec 64).toNat).toNat = _
  simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  omega

/-- `vpmadd52lo` is `pl`, unconditionally: both truncate mod `2^52`. -/
theorem lo_eq (a b : BitVec 64) :
    mulLo52 a b = BitVec.ofNat 64 (pl a.toNat b.toNat) := by
  simp [mulLo52, pl, Nat.mod_mul_mod]

/-- `vpmadd52hi` followed by `wwl_shl(…,9)` is `ph`. Unlike `lo_eq` this needs
the operand bounds: otherwise the implicit truncation to 52 bits is lossy. -/
theorem hi_eq (a b : BitVec 64) (ha : a.toNat < 2^52) (hb : b.toNat < 2^52) :
    mulHi52 a b <<< (9 : BitVec 64) = BitVec.ofNat 64 (ph a.toNat b.toNat) := by
  rw [mulHi52, ofNat_shl, ph, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb,
      show (9 : BitVec 64).toNat = 9 from rfl]

/-- A lane below `2^63` reads back as itself, rather than as a negative. -/
theorem ofNat_toInt {n : Nat} (h : n < 2^63) :
    (BitVec.ofNat 64 n).toInt = (n : Int) := by
  have h64 : n < 2^64 := by omega
  have ht : (BitVec.ofNat 64 n).toNat = n := by rw [BitVec.toNat_ofNat]; omega
  rw [BitVec.toInt_eq_toNat_of_lt (by rw [ht]; omega), ht]

/-! `R43x6.UNN` bounds `BitVec.toInt` on both sides; the lane arithmetic works
in `toNat`. These convert in each direction. The two-sided bound is essential:
an upper bound on `toInt` alone admits negative lanes, on which the
specifications are false. -/

theorem toNat_lt_of_bounds {a : BitVec 64} {N : ℕ} (hN : N ≤ 2^62)
    (hu : a.toInt ≤ (N : Int) - 1) (hl : (0:Int) ≤ a.toInt) : a.toNat < N := by
  have hlt : a.toNat < 2^64 := a.isLt
  have hb := BitVec.toInt_eq_toNat_bmod a
  rw [Int.bmod] at hb
  split at hb <;> omega

/-- An input limb of a `UNN n` vector, as a natural. -/
theorem unn_toNat (x : Vector (BitVec 64) 8) (n : ℕ) (hn : n ≤ 62)
    (hx : R43x6.UNN n x) (i : ℕ) (hi : i < 8) : (x[i]'hi).toNat < 2^n :=
  toNat_lt_of_bounds (Nat.pow_le_pow_right (by omega) hn)
    (by have := hx.1 i hi; push_cast; omega) (hx.2 i hi)

/-- An output lane, back in `toInt` form. -/
theorem lane_toInt_bound {n N : ℕ} (hN : N ≤ 2^63) (h : n < N) :
    (0:Int) ≤ (BitVec.ofNat 64 n).toInt ∧ (BitVec.ofNat 64 n).toInt ≤ (N:Int) - 1 := by
  have h63 : n < 2^63 := by omega
  rw [ofNat_toInt h63]
  omega

/-- An input limb is below `2^63`, so it too reads back as a natural. -/
theorem toInt_of_lt {a : BitVec 64} (h : a.toNat < 2^47) :
    a.toInt = (a.toNat : Int) :=
  BitVec.toInt_eq_toNat_of_lt (by omega)

/-- `decode'` on a literal vector: the low six lanes with radix-`2^43` weights. -/
theorem decode'_lit (a b c d e f g h : BitVec 64) :
    R43x6.decode' #v[a,b,c,d,e,f,g,h] = a.toInt + 2^43 * b.toInt + 2^86 * c.toInt
      + 2^129 * d.toInt + 2^172 * e.toInt + 2^215 * f.toInt := by
  simp [R43x6.decode', R43x6.decode, LimbRepresentations.decode,
    LimbRepresentations.placeValues, R43x6.limbCount, R43x6.baseBits, R43x6.limbWidth,
    show (Vector.range 6 : Vector Nat 6) = #v[0,1,2,3,4,5] from rfl, Vector.sum]
  ring

/-- The input limbs of a vector as naturals, in the `ℕ → ℕ` form the column
sums take. -/
def limbNat (x : Vector (BitVec 64) 8) : ℕ → ℕ
  | 0 => x[0].toNat
  | 1 => x[1].toNat
  | 2 => x[2].toNat
  | 3 => x[3].toNat
  | 4 => x[4].toNat
  | 5 => x[5].toNat
  | _ => 0

/-! ## The predicted result vector

Both `fd_r43x6_sqr_fast` and `fd_r43x6_mul_fast` produce six specified limbs
in lanes 0-5 and zero in lanes 6 and 7. -/

/-- Six ℕ-level limbs as an 8-lane result vector, lanes 6 and 7 zero. -/
def limbVec (l : ℕ → ℕ) : Vector (BitVec 64) 8 :=
  #v[BitVec.ofNat 64 (l 0), BitVec.ofNat 64 (l 1), BitVec.ofNat 64 (l 2),
     BitVec.ofNat 64 (l 3), BitVec.ofNat 64 (l 4), BitVec.ofNat 64 (l 5), 0, 0]

/-- Decoding `limbVec` is `pack`, provided no lane reads back negative. -/
theorem decode'_limbVec (l : ℕ → ℕ) (hb : ∀ k < 6, l k < 2^63) :
    R43x6.decode' (limbVec l) = ((pack l : ℕ) : Int) := by
  rw [limbVec, decode'_lit,
    ofNat_toInt (hb 0 (by omega)), ofNat_toInt (hb 1 (by omega)),
    ofNat_toInt (hb 2 (by omega)), ofNat_toInt (hb 3 (by omega)),
    ofNat_toInt (hb 4 (by omega)), ofNat_toInt (hb 5 (by omega))]
  push_cast [pack]
  try ring

/-- Two-sided lane bounds on `limbVec` from a ceiling `N` on the ℕ-level
limbs: lanes 0-5 are the limbs, lanes 6 and 7 the zero literal. -/
theorem limbVec_bounds (l : ℕ → ℕ) (N : ℕ) (hN : N ≤ 2^63)
    (hb : ∀ k < 6, l k < N) :
    R43x6.BoundedUpper ((N : Int) - 1) (limbVec l)
      ∧ R43x6.BoundedLower 0 (limbVec l) := by
  have key : ∀ k, k < 6 →
      (0:Int) ≤ (BitVec.ofNat 64 (l k)).toInt
      ∧ (BitVec.ofNat 64 (l k)).toInt ≤ (N:Int) - 1 :=
    fun k hk => lane_toInt_bound hN (hb k hk)
  have hN1 : 1 ≤ N := by have := hb 0 (by omega); omega
  have hz : ((0 : BitVec 64)).toInt = 0 := rfl
  refine ⟨fun i hi => ?_, fun i hi => ?_⟩
  · interval_cases i
    · exact (key 0 (by omega)).2
    · exact (key 1 (by omega)).2
    · exact (key 2 (by omega)).2
    · exact (key 3 (by omega)).2
    · exact (key 4 (by omega)).2
    · exact (key 5 (by omega)).2
    · show (0 : BitVec 64).toInt ≤ _
      rw [hz]; omega
    · show (0 : BitVec 64).toInt ≤ _
      rw [hz]; omega
  · interval_cases i
    · exact (key 0 (by omega)).1
    · exact (key 1 (by omega)).1
    · exact (key 2 (by omega)).1
    · exact (key 3 (by omega)).1
    · exact (key 4 (by omega)).1
    · exact (key 5 (by omega)).1
    · show (0 : BitVec 64).toInt ≥ _
      rw [hz]
    · show (0 : BitVec 64).toInt ≥ _
      rw [hz]

end Firedancer.Avx512
