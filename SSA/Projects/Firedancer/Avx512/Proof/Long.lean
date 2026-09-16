/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.SLLVM.Dialect
import SSA.Projects.Firedancer.Avx512.R43x6
import Mathlib.Tactic.Linarith

/-!
# The scalar `long` instructions, at the level of `ℤ`

The serial carry macros compile to scalar `i64` code, and their model in
`Spec/` is over `ℤ`. These lemmas are the transfer: a value carrying the
integer `a` is `BitVec.ofInt 64 a`, and each instruction takes such values to
such values, provided everything in sight satisfies `R43x6.FitsLong`.

The `FitsLong` side conditions are not bookkeeping: `nsw` makes an overflowing
`add` denote to poison, so without them the region has no value at all. They
are exactly what `ChainFitsLong` supplies.
-/

namespace Firedancer.Avx512

open InstCombine (LLVM)
open R43x6 (FitsLong)

/-! ## Values

A `long` carrying the integer `a` is `val a`. Every lemma below is of the form
"instruction on `val`s is `val` of the result", so a derivation stays in this
form from the first extract to the last compare. -/

/-- The `i64` carrying the integer `a`. -/
def val (a : ℤ) : LLVM.IntW 64 :=
  .value (BitVec.ofInt 64 a)

/-- Fold a denoted value into `val`. -/
theorem val_eq (a : ℤ) : PoisonOr.value (BitVec.ofInt 64 a) = val a :=
  rfl

theorem fitsLong_toInt (x : BitVec 64) : FitsLong x.toInt := by
  have h1 := BitVec.toInt_lt (x := x)
  have h2 := BitVec.le_toInt (x := x)
  simp only [FitsLong]
  norm_num at h1 h2 ⊢
  omega

theorem toInt_ofInt {a : ℤ} (h : FitsLong a) : (BitVec.ofInt 64 a).toInt = a := by
  rw [BitVec.toInt_ofInt, Int.bmod]
  simp only [FitsLong] at h
  norm_num
  omega

theorem toNat_ofInt {a : ℤ} (h : FitsLong a) (h0 : 0 ≤ a) :
    ((BitVec.ofInt 64 a).toNat : ℤ) = a := by
  have hb := BitVec.toInt_eq_toNat_bmod (BitVec.ofInt 64 a)
  rw [toInt_ofInt h] at hb
  have hlt : (BitVec.ofInt 64 a).toNat < 2 ^ 64 := (BitVec.ofInt 64 a).isLt
  rw [Int.bmod] at hb
  simp only [FitsLong] at h
  norm_num at hb ⊢
  omega

theorem ofInt_toInt (x : BitVec 64) : BitVec.ofInt 64 x.toInt = x :=
  BitVec.eq_of_toInt_eq (toInt_ofInt (fitsLong_toInt x))

@[simp]
theorem val_inj {a b : ℤ} (ha : FitsLong a) (hb : FitsLong b) : val a = val b ↔ a = b := by
  constructor
  · intro h
    simp only [val, PoisonOr.value_inj] at h
    have := congrArg BitVec.toInt h
    rwa [toInt_ofInt ha, toInt_ofInt hb] at this
  · rintro rfl; rfl

/-- A shift right never leaves the range: it is division by a positive
number. -/
theorem fitsLong_shiftRight {a : ℤ} (ha : FitsLong a) (n : ℕ) : FitsLong (a >>> n) := by
  rw [R43x6.shiftRight_eq]
  have hd : (0 : ℤ) < 2 ^ n := by positivity
  have h1 : (1 : ℤ) ≤ 2 ^ n := by exact_mod_cast Nat.one_le_two_pow
  simp only [FitsLong] at ha ⊢
  refine ⟨?_, ?_⟩
  · rw [Int.le_ediv_iff_mul_le hd]; nlinarith
  · rw [Int.ediv_lt_iff_lt_mul hd]; nlinarith

/-- Masking never leaves the range: the residue is non-negative and below the
mask. -/
theorem fitsLong_emod (a : ℤ) {k : ℕ} (hk : k ≤ 63) : FitsLong (a % 2 ^ k) := by
  have h1 : (0 : ℤ) < 2 ^ k := by positivity
  have h2 : (2 : ℤ) ^ k ≤ 2 ^ 63 := pow_le_pow_right₀ (by norm_num) hk
  have := Int.emod_nonneg a (by omega : (2 : ℤ) ^ k ≠ 0)
  have := Int.emod_lt_of_pos a h1
  simp only [FitsLong]; omega

/-- Shifting a non-negative value right keeps it non-negative. -/
theorem shiftRight_nonneg {a : ℤ} (h : 0 ≤ a) (n : ℕ) : 0 ≤ a >>> n := by
  rw [R43x6.shiftRight_eq]
  exact Int.ediv_nonneg h (by positivity)

/-! ## Instructions -/

/-- `llvm.add`. `nuw` needs both operands non-negative on top of the range. -/
theorem add_ofInt {a b : ℤ} {flags : LLVM.NoWrapFlags} (ha : FitsLong a) (hb : FitsLong b)
    (hab : FitsLong (a + b)) (hnuw : flags.nuw = true → 0 ≤ a ∧ 0 ≤ b) :
    LLVM.add (val a) (val b) flags = val (a + b) := by
  simp only [val, LLVM.add, PoisonOr.value_bind]
  rw [if_neg, if_neg]
  · simp [LLVM.add?, BitVec.ofInt_add]
  · rintro ⟨h1, h2⟩
    obtain ⟨ha0, hb0⟩ := hnuw h1
    simp only [BitVec.uaddOverflow, ge_iff_le, decide_eq_true_eq] at h2
    have := toNat_ofInt ha ha0
    have := toNat_ofInt hb hb0
    simp only [FitsLong] at hab
    omega
  · rintro ⟨-, h2⟩
    simp only [BitVec.saddOverflow, ge_iff_le, decide_eq_true_eq, Bool.or_eq_true] at h2
    rw [toInt_ofInt ha, toInt_ofInt hb] at h2
    simp only [FitsLong] at hab
    omega

/-- `llvm.sub`, `nsw` only -- the one subtraction in the region is the
conditional subtract, where a borrow is intended. -/
theorem sub_ofInt {a b : ℤ} {flags : LLVM.NoWrapFlags} (hnuw : flags.nuw = false) (ha : FitsLong a)
    (hb : FitsLong b) (hab : FitsLong (a - b)) : LLVM.sub (val a) (val b) flags = val (a - b) := by
  simp only [val, LLVM.sub, PoisonOr.value_bind]
  rw [if_neg, if_neg]
  · simp only [LLVM.sub?, sub_eq_add_neg, BitVec.ofInt_add, BitVec.ofInt_neg, BitVec.sub_eq_add_neg]
  · rintro ⟨h1, -⟩; rw [hnuw] at h1; exact absurd h1 (by simp)
  · rintro ⟨-, h2⟩
    simp only [BitVec.ssubOverflow, ge_iff_le, decide_eq_true_eq, Bool.or_eq_true] at h2
    rw [toInt_ofInt ha, toInt_ofInt hb] at h2
    simp only [FitsLong] at hab
    omega

/-- `llvm.mul`, `nsw` only. -/
theorem mul_ofInt {a b : ℤ} {flags : LLVM.NoWrapFlags} (hnuw : flags.nuw = false) (ha : FitsLong a)
    (hb : FitsLong b) (hab : FitsLong (a * b)) : LLVM.mul (val a) (val b) flags = val (a * b) := by
  simp only [val, LLVM.mul, PoisonOr.value_bind]
  rw [if_neg, if_neg]
  · simp [LLVM.mul?, BitVec.ofInt_mul]
  · rintro ⟨h1, -⟩; rw [hnuw] at h1; exact absurd h1 (by simp)
  · rintro ⟨-, h2⟩
    simp only [BitVec.smulOverflow, ge_iff_le, decide_eq_true_eq, Bool.or_eq_true] at h2
    rw [toInt_ofInt ha, toInt_ofInt hb] at h2
    simp only [FitsLong] at hab
    omega

/-- `llvm.ashr` by a constant: floor division, which is what `>>>` is on `ℤ`. -/
theorem ashr_ofInt {a : ℤ} (ha : FitsLong a) {n : ℕ} (hn : n < 64) :
    LLVM.ashr (val a) (val (n : ℤ)) = val (a >>> n) := by
  have hnat : (BitVec.ofInt 64 (n : ℤ)).toNat = n := by
    have :=
      toNat_ofInt (a := (n : ℤ))
        (by
          simp only [FitsLong]; omega)
        (by omega)
    omega
  simp only [val, LLVM.ashr, PoisonOr.value_bind, LLVM.ashr?]
  rw [if_neg (by simp), if_neg]
  · congr 1
    apply BitVec.eq_of_toInt_eq
    rw [BitVec.sshiftRight', hnat, BitVec.toInt_sshiftRight, toInt_ofInt ha,
      toInt_ofInt (fitsLong_shiftRight ha n)]
  · simp only [ge_iff_le, BitVec.le_def, hnat]
    simp
    omega

/-- `llvm.lshr` by a constant, on a non-negative value: the same floor
division as `ashr`. The `x + 19` chain shifts with `lshr`, which is why
`mnrA_nonneg` is part of the specification. -/
theorem lshr_ofInt {a : ℤ} (ha : FitsLong a) (ha0 : 0 ≤ a) {n : ℕ} (hn : n < 64) (hn0 : n ≠ 0) :
    LLVM.lshr (val a) (val (n : ℤ)) = val (a >>> n) := by
  have hnat : (BitVec.ofInt 64 (n : ℤ)).toNat = n := by
    have :=
      toNat_ofInt (a := (n : ℤ))
        (by
          simp only [FitsLong]; omega)
        (by omega)
    omega
  have hxnat : ((BitVec.ofInt 64 a).toNat : ℤ) = a := toNat_ofInt ha ha0
  simp only [val, LLVM.lshr, PoisonOr.value_bind, LLVM.lshr?]
  rw [if_neg (by simp), if_neg]
  · congr 1
    apply BitVec.eq_of_toInt_eq
    show (BitVec.ofInt 64 a >>> (BitVec.ofInt 64 (n : ℤ)).toNat).toInt = _
    rw [BitVec.toInt_ushiftRight, hnat, if_neg hn0, toInt_ofInt (fitsLong_shiftRight ha n),
      R43x6.shiftRight_eq, Nat.shiftRight_eq_div_pow]
    push_cast [Int.natCast_div, hxnat]
    ring
  · simp only [ge_iff_le, BitVec.le_def, hnat]
    simp
    omega

/-- Masking a `long` with `2^k - 1`, on the `BitVec` itself: the `or` chain at
the end of `fd_r43x6_is_nonzero` masks a disjunction rather than each limb, so
the mask has to move across `|||`. -/
theorem and_mask_bv (a : ℤ) {k : ℕ} (hk : k < 64) :
    BitVec.ofInt 64 a &&& BitVec.ofInt 64 (2 ^ k - 1) = BitVec.ofInt 64 (a % 2 ^ k) := by
  have h2k : (1 : ℕ) ≤ 2 ^ k := Nat.one_le_two_pow
  have hkle : (2 : ℕ) ^ k ≤ 2 ^ 63 := Nat.pow_le_pow_right (by omega) (by omega)
  have hcast : ((2 : ℤ) ^ k - 1) = ((2 ^ k - 1 : ℕ) : ℤ) := by
    rw [Nat.cast_sub h2k]; push_cast; ring
  have hmN : (BitVec.ofInt 64 ((2 : ℤ) ^ k - 1)).toNat = 2 ^ k - 1 := by
    rw [hcast, BitVec.toNat_ofInt,
      Int.emod_eq_of_lt (by positivity)
        (by
          push_cast; omega),
      Int.toNat_natCast]
  have hnat :
    ((BitVec.ofInt 64 a) &&& (BitVec.ofInt 64 ((2 : ℤ) ^ k - 1))).toNat =
      (BitVec.ofInt 64 a).toNat % 2 ^ k := by
    rw [BitVec.toNat_and, hmN, Nat.and_two_pow_sub_one_eq_mod]
  have hmodlt : (BitVec.ofInt 64 a).toNat % 2 ^ k < 2 ^ k := Nat.mod_lt _ (by omega)
  apply BitVec.eq_of_toInt_eq
  rw [BitVec.toInt_eq_toNat_of_lt
      (by
        rw [hnat]; omega),
    hnat]
  have hmz : (0 : ℤ) ≤ a % 2 ^ k ∧ a % 2 ^ k < 2 ^ k := by
    have h1 : (0 : ℤ) < 2 ^ k := by positivity
    exact ⟨Int.emod_nonneg a (by omega), Int.emod_lt_of_pos a h1⟩
  have hfits : FitsLong (a % 2 ^ k) := by
    have : (2 : ℤ) ^ k ≤ 2 ^ 63 := by exact_mod_cast hkle
    simp only [FitsLong]; omega
  rw [toInt_ofInt hfits]
  have hx : ((BitVec.ofInt 64 a).toNat : ℤ) = a % 2 ^ 64 := by
    rw [BitVec.toNat_ofInt, Int.toNat_of_nonneg (Int.emod_nonneg a (by positivity))]
    push_cast; ring
  push_cast
  rw [hx]
  exact Int.emod_emod_of_dvd a (pow_dvd_pow 2 (by omega))

/-- `llvm.and` with a `k`-bit mask: the non-negative residue, which is what
`%` is on `ℤ`. -/
theorem and_mask_ofInt {a : ℤ} {k : ℕ} (hk : k < 64) :
    LLVM.and (val a) (val (2 ^ k - 1)) = val (a % 2 ^ k) := by
  simp only [val, LLVM.and, PoisonOr.value_bind, LLVM.and?, and_mask_bv a hk]

/-- `llvm.or`, which the final zero test uses on values that are not all
masked yet. -/
theorem or_ofInt (a b : ℤ) :
    LLVM.or (val a) (val b) = .value (BitVec.ofInt 64 a ||| BitVec.ofInt 64 b) :=
  rfl

/-- `llvm.or` with an accumulated left operand, which is the shape the final
`or` chain takes. -/
theorem or_val (bv : BitVec 64) (b : ℤ) :
    LLVM.or (.value bv) (val b) = .value (bv ||| BitVec.ofInt 64 b) :=
  rfl

/-- `val a` is zero exactly when `a` is. -/
theorem ofInt_eq_zero_iff {a : ℤ} (ha : FitsLong a) : BitVec.ofInt 64 a = 0#64 ↔ a = 0 := by
  constructor
  · intro h
    have := congrArg BitVec.toInt h
    rwa [toInt_ofInt ha, show (0#64 : BitVec 64).toInt = 0 from rfl] at this
  · rintro rfl; rfl

/-- `llvm.icmp ult` on non-negative values. -/
theorem icmp_ult_ofInt {a b : ℤ} (ha : FitsLong a) (hb : FitsLong b) (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) :
    LLVM.icmp .ult (val a) (val b) = .value (BitVec.ofBool (decide (a < b))) := by
  have hna := toNat_ofInt ha ha0
  have hnb := toNat_ofInt hb hb0
  simp only [val, LLVM.icmp, PoisonOr.value_bind, LLVM.icmp?, LLVM.icmp', BitVec.ult,
    PoisonOr.value_inj]
  congr 1
  simp only [decide_eq_decide]
  omega

/-- `llvm.icmp ne` against a `val`, on an accumulated left operand. -/
theorem icmp_ne_val (bv : BitVec 64) (b : ℤ) :
    LLVM.icmp .ne (.value bv) (val b) = .value (BitVec.ofBool (bv != BitVec.ofInt 64 b)) :=
  rfl

/-- `llvm.zext` of a comparison result. -/
theorem zext_ofBool (w : ℕ) (b : Bool) :
    LLVM.zext w (.value (BitVec.ofBool b)) = .value (BitVec.ofBool b |>.setWidth w) :=
  rfl

end Firedancer.Avx512
