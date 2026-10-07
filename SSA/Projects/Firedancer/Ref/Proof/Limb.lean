module

public import Mathlib.Tactic.FinCases
public import Mathlib.Data.Fin.VecNotation
public import SSA.Projects.Firedancer.Proof.Overflow

/-!
# fiat's limbs in 64-bit registers

The ref regions hold a field element as five 51-bit limbs, one per 64-bit
register, and reduce with `19`. These are the `toNat` facts for the operations
that shape entails: a shift by 51, a mask with `2^51 - 1`, a `mul 19`, and the
128-bit products two limbs form.
-/

@[expose] public section

namespace Firedancer.Ref

open LeanMLIR SLLVM

/-- Componentwise, leaving the components untouched: a tactic that reduces
`![…] i` also normalises the arithmetic inside them. -/
theorem forall_fin5 {n a b c d e : ℕ} (ha : a ≤ n) (hb : b ≤ n) (hc : c ≤ n) (hd : d ≤ n)
    (he : e ≤ n) : ∀ i, ![a, b, c, d, e] i ≤ n := by
  intro i
  fin_cases i
  · exact ha
  · exact hb
  · exact hc
  · exact hd
  · exact he

theorem vec_eq {α : Type} (f : Fin 5 → α) : ![f 0, f 1, f 2, f 3, f 4] = f := by
  funext i; fin_cases i <;> rfl

/-- A limb is `ofNat` of what it decodes to, once it is known to fit. -/
theorem eq_ofNat_of_toNat {l : Fin 5 → ℕ} {u : BitVec 64} {i : Fin 5} (h : u.toNat = l i) :
    u = (BitVec.ofNat 64 ∘ l) i := by
  show u = BitVec.ofNat 64 (l i)
  rw [← h, BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-! ### Shifts and masks

The shift amount is a `BitVec`, as `eval_llvm` leaves an `llvm.lshr`. -/

/-- A window of a window: reading `b` bits at `a` out of the `n` bits at `s` is
reading them at `s + a`. -/
theorem extractLsb'_extractLsb' {w : ℕ} (x : BitVec w) {s n a b : ℕ} (h : a + b ≤ n) :
    (x.extractLsb' s n).extractLsb' a b = x.extractLsb' (s + a) b := by
  ext i hi
  have hin : a + i < n := by omega
  simp [BitVec.getElem_extractLsb', Nat.add_assoc, hin]

/-! ### Widening a byte before shifting it

The compiled `from_bytes` shifts each zero-extended byte with `nsw, nuw`, so the
shift is poison unless it provably discards nothing. At a byte and a shift of at
most 50 it never does.

Two forms of each: the register form bounds the shift's `BitVec`, while the
walk meets the shift as `BitVec.ofNat 64 n` and needs the bound on `n`, where
`simp` can discharge it for a literal. -/

theorem zext8_shl_ushr (b : BitVec 8) {k : BitVec 64} (hk : k ≤ 50#64) :
    (BitVec.zeroExtend 64 b <<< k) >>> k = BitVec.zeroExtend 64 b := by
  have hk' : k.toNat ≤ 50 := hk
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  by_cases hi8 : i < 8
  · simp [BitVec.ushiftRight_eq', BitVec.shiftLeft_eq', BitVec.getLsbD_shiftLeft,
      BitVec.getLsbD_setWidth, show k.toNat + i < 64 by omega,
      show ¬k.toNat + i < k.toNat by omega, hi]
  · simp [BitVec.ushiftRight_eq', BitVec.shiftLeft_eq', BitVec.getLsbD_shiftLeft,
      BitVec.getLsbD_setWidth, BitVec.getLsbD_of_ge b i (by omega)]

theorem zext8_shl_sshr (b : BitVec 8) {k : BitVec 64} (hk : k ≤ 50#64) :
    (BitVec.zeroExtend 64 b <<< k).sshiftRight' k = BitVec.zeroExtend 64 b := by
  have hk' : k.toNat ≤ 50 := hk
  have hmsb : (BitVec.zeroExtend 64 b <<< k).msb = false := by
    rw [BitVec.msb_eq_getLsbD_last]
    simp [BitVec.shiftLeft_eq', BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth,
      BitVec.getLsbD_of_ge b (63 - k.toNat) (by omega)]
  rw [BitVec.sshiftRight_eq', BitVec.sshiftRight_eq_of_msb_false hmsb]
  exact zext8_shl_ushr b hk

private theorem ofNat_le_50 {n : ℕ} (hn : n ≤ 50) : BitVec.ofNat 64 n ≤ 50#64 := by
  simp only [BitVec.le_def, BitVec.toNat_ofNat]
  omega

theorem zext8_shl_ushr_ofNat (b : BitVec 8) {n : ℕ} (hn : n ≤ 50) :
    (BitVec.zeroExtend 64 b <<< BitVec.ofNat 64 n) >>> BitVec.ofNat 64 n = BitVec.zeroExtend 64 b :=
  zext8_shl_ushr b (ofNat_le_50 hn)

theorem zext8_shl_sshr_ofNat (b : BitVec 8) {n : ℕ} (hn : n ≤ 50) :
    (BitVec.zeroExtend 64 b <<< BitVec.ofNat 64 n).sshiftRight' (BitVec.ofNat 64 n) =
      BitVec.zeroExtend 64 b :=
  zext8_shl_sshr b (ofNat_le_50 hn)

theorem shift_toNat (x : BitVec 64) : (x >>> 51#64).toNat = x.toNat / 2 ^ 51 := by
  rw [show x >>> 51#64 = x >>> (51 : ℕ) from rfl, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow]

theorem shift_toNat128 (u : BitVec 128) : (u >>> 51#128).toNat = u.toNat / 2 ^ 51 := by
  rw [show u >>> 51#128 = u >>> (51 : ℕ) from rfl, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow]

theorem mask_toNat (a : BitVec 64) : (a &&& 2251799813685247#64).toNat = a.toNat % 2 ^ 51 := by
  rw [BitVec.toNat_and, show (2251799813685247#64).toNat = 2 ^ 51 - 1 by decide,
    Nat.and_two_pow_sub_one_eq_mod]

theorem mask_toNat_lt (a : BitVec 64) : (a &&& 2251799813685247#64).toNat < 2 ^ 51 := by
  rw [mask_toNat]; omega

/-- `2^51` divides `2^64`, so the `trunc` before the mask loses nothing. -/
theorem trunc_mask_toNat (u : BitVec 128) :
    (BitVec.truncate 64 u &&& 2251799813685247#64).toNat = u.toNat % 2 ^ 51 := by
  rw [mask_toNat, BitVec.toNat_setWidth]
  omega

theorem mask64_toNat (u : BitVec 128) :
    (u &&& 18446744073709551615#128).toNat = u.toNat % 2 ^ 64 := by
  rw [BitVec.toNat_and, show (18446744073709551615#128).toNat = 2 ^ 64 - 1 from by decide,
    Nat.and_two_pow_sub_one_eq_mod]

theorem trunc_shift_toNat (u : BitVec 128) :
    (BitVec.truncate 64 (u >>> 51#128)).toNat = u.toNat / 2 ^ 51 % 2 ^ 64 := by
  rw [BitVec.toNat_setWidth, shift_toNat128]

/-! ### The reduction constant -/

theorem mul19_toNat {u : BitVec 64} (h : u.toNat * 19 < 2 ^ 64) :
    (u * 19#64).toNat = u.toNat * 19 := by
  rw [BitVec.toNat_mul, show (19#64).toNat = 19 from by decide]
  omega

/-- At a carry of at most 3 the `mul 19` fits, signed or not. -/
theorem mul19_no_overflow {c : BitVec 64} (hc : c.toNat ≤ 3) :
    c.smulOverflow 19#64 = false ∧ c.umulOverflow 19#64 = false := by
  have h19 : (19#64).toNat = 19 := by decide
  exact
    ⟨smulOverflow_eq_false (by omega) (by omega)
        (by
          rw [h19]; omega),
      umulOverflow_eq_false
        (by
          rw [h19]; omega)⟩

/-- At a `≤ 3` carry and a masked limb neither the `mul` nor the `add` wraps. -/
theorem mul19_add_toNat {c m : BitVec 64} (hc : c.toNat ≤ 3) (hm : m.toNat < 2 ^ 51) :
    (c * 19#64 + m).toNat = c.toNat * 19 + m.toNat := by
  rw [toNat_add
      (by
        rw [mul19_toNat (by omega)]; omega),
    mul19_toNat (by omega)]

/-- ... and carries at most 1, so the next step keeps the `≤ 3` bound. -/
theorem mul19_add_toNat_le {c m : BitVec 64} (hc : c.toNat ≤ 3) (hm : m.toNat < 2 ^ 51) :
    (c * 19#64 + m).toNat ≤ 2 ^ 51 + 56 := by
  rw [mul19_add_toNat hc hm]; omega

theorem add_toNat {c m : BitVec 64} (hc : c.toNat ≤ 3) (hm : m.toNat < 2 ^ 51) :
    (c + m).toNat = c.toNat + m.toNat :=
  toNat_add (by omega)

theorem add_toNat_le {c m : BitVec 64} (hc : c.toNat ≤ 3) (hm : m.toNat < 2 ^ 51) :
    (c + m).toNat ≤ 2 ^ 51 + 2 := by
  rw [add_toNat hc hm]; omega

/-! ### Two limbs, zero-extended into a 128-bit product

Each limb is widened before multiplying, with the `19` folded into the limb it
scales, so three operand shapes occur. -/

theorem toNat_mul128 {u v : BitVec 128} (hu : u.toNat < 2 ^ 64) (hv : v.toNat < 2 ^ 64) :
    (u * v).toNat = u.toNat * v.toNat :=
  toNat_mul
    (calc
      u.toNat * v.toNat < 2 ^ 64 * 2 ^ 64 := Nat.mul_lt_mul_of_lt_of_lt hu hv
      _ = 2 ^ 128 := by norm_num)

theorem toNat_zx {n : ℕ} (h : n < 2 ^ 64) :
    (BitVec.zeroExtend 128 (BitVec.ofNat 64 n)).toNat = n := by
  rw [BitVec.toNat_setWidth_of_le (by omega), BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

theorem toNat_zx19 {n : ℕ} (h : n * 19 < 2 ^ 64) :
    (BitVec.zeroExtend 128 (BitVec.ofNat 64 n * 19#64)).toNat = n * 19 := by
  rw [BitVec.toNat_setWidth_of_le (by omega), BitVec.toNat_mul, BitVec.toNat_ofNat,
    show (19#64).toNat = 19 from by decide]
  omega

theorem toNat_zx_mul_zx {m n : ℕ} (hm : m < 2 ^ 64) (hn : n < 2 ^ 64) :
    (BitVec.zeroExtend 128 (BitVec.ofNat 64 m) * BitVec.zeroExtend 128 (BitVec.ofNat 64 n)).toNat =
      m * n := by
  rw [toNat_mul128
      (by
        rw [toNat_zx hm]; omega)
      (by
        rw [toNat_zx hn]; omega),
    toNat_zx hm, toNat_zx hn]

theorem toNat_zx_mul_zx19 {m n : ℕ} (hm : m < 2 ^ 64) (hn : n * 19 < 2 ^ 64) :
    (BitVec.zeroExtend 128 (BitVec.ofNat 64 m) *
          BitVec.zeroExtend 128 (BitVec.ofNat 64 n * 19#64)).toNat =
      m * (n * 19) := by
  rw [toNat_mul128
      (by
        rw [toNat_zx hm]; omega)
      (by
        rw [toNat_zx19 hn]; omega),
    toNat_zx hm, toNat_zx19 hn]

theorem toNat_zx19_mul_zx {m n : ℕ} (hm : m * 19 < 2 ^ 64) (hn : n < 2 ^ 64) :
    (BitVec.zeroExtend 128 (BitVec.ofNat 64 m * 19#64) *
          BitVec.zeroExtend 128 (BitVec.ofNat 64 n)).toNat =
      m * 19 * n := by
  rw [toNat_mul128
      (by
        rw [toNat_zx19 hm]; omega)
      (by
        rw [toNat_zx hn]; omega),
    toNat_zx19 hm, toNat_zx hn]

/-- A column of five products, left-associated as it is accumulated. -/
theorem toNat_col5 {u₁ u₂ u₃ u₄ u₅ : BitVec 128} {n₁ n₂ n₃ n₄ n₅ : ℕ} (h₁ : u₁.toNat = n₁)
    (h₂ : u₂.toNat = n₂) (h₃ : u₃.toNat = n₃) (h₄ : u₄.toNat = n₄) (h₅ : u₅.toNat = n₅)
    (hb : n₁ + n₂ + n₃ + n₄ + n₅ < 2 ^ 128) :
    (u₁ + u₂ + u₃ + u₄ + u₅).toNat = n₁ + n₂ + n₃ + n₄ + n₅ := by
  have e₂ : (u₁ + u₂).toNat = n₁ + n₂ := by rw [toNat_add (by omega), h₁, h₂]
  have e₃ : (u₁ + u₂ + u₃).toNat = n₁ + n₂ + n₃ := by rw [toNat_add (by omega), e₂, h₃]
  have e₄ : (u₁ + u₂ + u₃ + u₄).toNat = n₁ + n₂ + n₃ + n₄ := by rw [toNat_add (by omega), e₃, h₄]
  rw [toNat_add (by omega), e₄, h₅]

end Firedancer.Ref
