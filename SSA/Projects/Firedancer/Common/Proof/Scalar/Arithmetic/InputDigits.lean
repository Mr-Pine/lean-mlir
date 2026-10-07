import SSA.Projects.Firedancer.Common.Proof.Scalar.Arithmetic.Registers
import SSA.Projects.Firedancer.Common.Proof.Scalar.Arithmetic.MachineLong
import SSA.Projects.Firedancer.Common.Proof.Scalar.Arithmetic.IntegerResult

namespace Firedancer.Common.ScalarArithmetic
open LeanMLIR SLLVM
open InstCombine (LLVM)
open IntegerRegisters

/-- Consecutive little-endian radix-2^21 digits; the last uses all remaining
29 bits of the 64-byte digest. -/
def inputDigits (digest : BitVec 512) : Digits := fun i =>
  ((digest.extractLsb' (21 * i.val) (if i = 23 then 29 else 21)).toNat : Int)

theorem inputDigits_bounded (digest : BitVec 512) : Bounded (inputDigits digest) := by
  intro i
  constructor
  · exact Int.natCast_nonneg _
  · change ((digest.extractLsb' (21 * i.val) (if i = 23 then 29 else 21)).toNat : Int) < _
    exact_mod_cast (digest.extractLsb' (21 * i.val) (if i = 23 then 29 else 21)).isLt

private theorem widen_ofNat {w : Nat} (x : BitVec w) :
    BitVec.ofNat 64 x.toNat = x.setWidth 64 := by
  apply BitVec.eq_of_toNat_eq
  simp

private theorem mask21_bit (i : Nat) (hi : i < 64) :
    (BitVec.ofInt 64 2097151).getLsbD i = decide (i < 21) := by
  have h : ∀ i : Fin 64, (BitVec.ofInt 64 2097151).getLsbD i.val = decide (i.val < 21) := by
    decide +kernel
  exact h ⟨i, hi⟩

private theorem shift_mask21 (digest : BitVec 512) (base shift : Nat)
    (hs : shift + 21 ≤ 64) :
    (digest.extractLsb' base 64 >>> shift) &&& BitVec.ofInt 64 2097151 =
      (digest.extractLsb' (base + shift) 21).setWidth 64 := by
  ext i hi
  simp only [← BitVec.getLsbD_eq_getElem, BitVec.getLsbD_and,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_extractLsb']
  rw [mask21_bit i hi]
  by_cases h : i < 21
  · simp [hi, h, show shift + i < 64 by omega]
    congr 1
    omega
  · simp [hi, h]

private theorem fshl_mask21 (digest : BitVec 512) (base shift : Nat)
    (hs0 : 0 < shift) (hs : shift < 64) :
    SLLVM.fshlBV (digest.extractLsb' (base + 64) 64) (digest.extractLsb' base 64)
        (BitVec.ofNat 64 shift) &&& BitVec.ofInt 64 2097151 =
      (digest.extractLsb' (base + 64 - shift) 21).setWidth 64 := by
  have hw : shift < 2 ^ 64 := by omega
  unfold SLLVM.fshlBV
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hw, Nat.mod_eq_of_lt hs]
  ext i hi
  simp only [← BitVec.getLsbD_eq_getElem, BitVec.getLsbD_and,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_extractLsb',
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_append]
  rw [mask21_bit i hi]
  by_cases h : i < 21
  · by_cases hc : i < shift
    · simp [hi, h, show 64 + i < 128 by omega, show ¬64 + i < shift by omega,
        show 64 + i - shift < 64 by omega]
      congr 1
      omega
    · simp [hi, h, show 64 + i < 128 by omega, show ¬64 + i < shift by omega,
        show ¬64 + i - shift < 64 by omega, show 64 + i - shift - 64 < 64 by omega]
      congr 1
      omega
  · simp [hi, h]

private theorem shift_tail29 (digest : BitVec 512) :
    digest.extractLsb' 448 64 >>> (35 : Nat) =
      (digest.extractLsb' 483 29).setWidth 64 := by
  ext i hi
  simp only [← BitVec.getLsbD_eq_getElem, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_extractLsb']
  by_cases h : i < 29
  · simp [hi, h, show 35 + i < 64 by omega]
    congr 1
    omega
  · simp [hi, h, show ¬35 + i < 64 by omega]

namespace Registers
set_option maxHeartbeats 2000000

theorem r61_value (digest : BitVec 512) : r61 digest = val (inputDigits digest 0) := by
  change r61 digest = .value (BitVec.ofNat 64 (digest.extractLsb' 0 21).toNat)
  rw [widen_ofNat]
  change PoisonOr.value ((digest.extractLsb' 0 64 >>> (0 : Nat)) &&& BitVec.ofInt 64 2097151) = .value ((digest.extractLsb' 0 21).setWidth 64)
  exact congrArg PoisonOr.value (shift_mask21 digest 0 0 (by decide))

theorem r63_value (digest : BitVec 512) : r63 digest = val (inputDigits digest 1) := by
  change r63 digest = .value (BitVec.ofNat 64 (digest.extractLsb' 21 21).toNat)
  rw [widen_ofNat]
  change PoisonOr.value ((digest.extractLsb' 0 64 >>> (21 : Nat)) &&& BitVec.ofInt 64 2097151) = .value ((digest.extractLsb' 21 21).setWidth 64)
  exact congrArg PoisonOr.value (shift_mask21 digest 0 21 (by decide))

theorem r65_value (digest : BitVec 512) : r65 digest = val (inputDigits digest 2) := by
  change r65 digest = .value (BitVec.ofNat 64 (digest.extractLsb' 42 21).toNat)
  rw [widen_ofNat]
  change PoisonOr.value ((digest.extractLsb' 0 64 >>> (42 : Nat)) &&& BitVec.ofInt 64 2097151) = .value ((digest.extractLsb' 42 21).setWidth 64)
  exact congrArg PoisonOr.value (shift_mask21 digest 0 42 (by decide))

theorem r67_value (digest : BitVec 512) : r67 digest = val (inputDigits digest 3) := by
  change r67 digest = .value (BitVec.ofNat 64 (digest.extractLsb' 63 21).toNat)
  rw [widen_ofNat]
  change PoisonOr.value (SLLVM.fshlBV (digest.extractLsb' 64 64) (digest.extractLsb' 0 64) (BitVec.ofNat 64 1) &&& BitVec.ofInt 64 2097151) = .value ((digest.extractLsb' 63 21).setWidth 64)
  exact congrArg PoisonOr.value (fshl_mask21 digest 0 1 (by decide) (by decide))

theorem r69_value (digest : BitVec 512) : r69 digest = val (inputDigits digest 4) := by
  change r69 digest = .value (BitVec.ofNat 64 (digest.extractLsb' 84 21).toNat)
  rw [widen_ofNat]
  change PoisonOr.value ((digest.extractLsb' 64 64 >>> (20 : Nat)) &&& BitVec.ofInt 64 2097151) = .value ((digest.extractLsb' 84 21).setWidth 64)
  exact congrArg PoisonOr.value (shift_mask21 digest 64 20 (by decide))

theorem r71_value (digest : BitVec 512) : r71 digest = val (inputDigits digest 5) := by
  change r71 digest = .value (BitVec.ofNat 64 (digest.extractLsb' 105 21).toNat)
  rw [widen_ofNat]
  change PoisonOr.value ((digest.extractLsb' 64 64 >>> (41 : Nat)) &&& BitVec.ofInt 64 2097151) = .value ((digest.extractLsb' 105 21).setWidth 64)
  exact congrArg PoisonOr.value (shift_mask21 digest 64 41 (by decide))

theorem r73_value (digest : BitVec 512) : r73 digest = val (inputDigits digest 6) := by
  change r73 digest = .value (BitVec.ofNat 64 (digest.extractLsb' 126 21).toNat)
  rw [widen_ofNat]
  change PoisonOr.value (SLLVM.fshlBV (digest.extractLsb' 128 64) (digest.extractLsb' 64 64) (BitVec.ofNat 64 2) &&& BitVec.ofInt 64 2097151) = .value ((digest.extractLsb' 126 21).setWidth 64)
  exact congrArg PoisonOr.value (fshl_mask21 digest 64 2 (by decide) (by decide))

theorem r75_value (digest : BitVec 512) : r75 digest = val (inputDigits digest 7) := by
  change r75 digest = .value (BitVec.ofNat 64 (digest.extractLsb' 147 21).toNat)
  rw [widen_ofNat]
  change PoisonOr.value ((digest.extractLsb' 128 64 >>> (19 : Nat)) &&& BitVec.ofInt 64 2097151) = .value ((digest.extractLsb' 147 21).setWidth 64)
  exact congrArg PoisonOr.value (shift_mask21 digest 128 19 (by decide))

theorem r77_value (digest : BitVec 512) : r77 digest = val (inputDigits digest 8) := by
  change r77 digest = .value (BitVec.ofNat 64 (digest.extractLsb' 168 21).toNat)
  rw [widen_ofNat]
  change PoisonOr.value ((digest.extractLsb' 128 64 >>> (40 : Nat)) &&& BitVec.ofInt 64 2097151) = .value ((digest.extractLsb' 168 21).setWidth 64)
  exact congrArg PoisonOr.value (shift_mask21 digest 128 40 (by decide))

theorem r79_value (digest : BitVec 512) : r79 digest = val (inputDigits digest 9) := by
  change r79 digest = .value (BitVec.ofNat 64 (digest.extractLsb' 189 21).toNat)
  rw [widen_ofNat]
  change PoisonOr.value (SLLVM.fshlBV (digest.extractLsb' 192 64) (digest.extractLsb' 128 64) (BitVec.ofNat 64 3) &&& BitVec.ofInt 64 2097151) = .value ((digest.extractLsb' 189 21).setWidth 64)
  exact congrArg PoisonOr.value (fshl_mask21 digest 128 3 (by decide) (by decide))

theorem r81_value (digest : BitVec 512) : r81 digest = val (inputDigits digest 10) := by
  change r81 digest = .value (BitVec.ofNat 64 (digest.extractLsb' 210 21).toNat)
  rw [widen_ofNat]
  change PoisonOr.value ((digest.extractLsb' 192 64 >>> (18 : Nat)) &&& BitVec.ofInt 64 2097151) = .value ((digest.extractLsb' 210 21).setWidth 64)
  exact congrArg PoisonOr.value (shift_mask21 digest 192 18 (by decide))

theorem r83_value (digest : BitVec 512) : r83 digest = val (inputDigits digest 11) := by
  change r83 digest = .value (BitVec.ofNat 64 (digest.extractLsb' 231 21).toNat)
  rw [widen_ofNat]
  change PoisonOr.value ((digest.extractLsb' 192 64 >>> (39 : Nat)) &&& BitVec.ofInt 64 2097151) = .value ((digest.extractLsb' 231 21).setWidth 64)
  exact congrArg PoisonOr.value (shift_mask21 digest 192 39 (by decide))

theorem r85_value (digest : BitVec 512) : r85 digest = val (inputDigits digest 12) := by
  change r85 digest = .value (BitVec.ofNat 64 (digest.extractLsb' 252 21).toNat)
  rw [widen_ofNat]
  change PoisonOr.value (SLLVM.fshlBV (digest.extractLsb' 256 64) (digest.extractLsb' 192 64) (BitVec.ofNat 64 4) &&& BitVec.ofInt 64 2097151) = .value ((digest.extractLsb' 252 21).setWidth 64)
  exact congrArg PoisonOr.value (fshl_mask21 digest 192 4 (by decide) (by decide))

theorem r87_value (digest : BitVec 512) : r87 digest = val (inputDigits digest 13) := by
  change r87 digest = .value (BitVec.ofNat 64 (digest.extractLsb' 273 21).toNat)
  rw [widen_ofNat]
  change PoisonOr.value ((digest.extractLsb' 256 64 >>> (17 : Nat)) &&& BitVec.ofInt 64 2097151) = .value ((digest.extractLsb' 273 21).setWidth 64)
  exact congrArg PoisonOr.value (shift_mask21 digest 256 17 (by decide))

theorem r89_value (digest : BitVec 512) : r89 digest = val (inputDigits digest 14) := by
  change r89 digest = .value (BitVec.ofNat 64 (digest.extractLsb' 294 21).toNat)
  rw [widen_ofNat]
  change PoisonOr.value ((digest.extractLsb' 256 64 >>> (38 : Nat)) &&& BitVec.ofInt 64 2097151) = .value ((digest.extractLsb' 294 21).setWidth 64)
  exact congrArg PoisonOr.value (shift_mask21 digest 256 38 (by decide))

theorem r91_value (digest : BitVec 512) : r91 digest = val (inputDigits digest 15) := by
  change r91 digest = .value (BitVec.ofNat 64 (digest.extractLsb' 315 21).toNat)
  rw [widen_ofNat]
  change PoisonOr.value (SLLVM.fshlBV (digest.extractLsb' 320 64) (digest.extractLsb' 256 64) (BitVec.ofNat 64 5) &&& BitVec.ofInt 64 2097151) = .value ((digest.extractLsb' 315 21).setWidth 64)
  exact congrArg PoisonOr.value (fshl_mask21 digest 256 5 (by decide) (by decide))

theorem r93_value (digest : BitVec 512) : r93 digest = val (inputDigits digest 16) := by
  change r93 digest = .value (BitVec.ofNat 64 (digest.extractLsb' 336 21).toNat)
  rw [widen_ofNat]
  change PoisonOr.value ((digest.extractLsb' 320 64 >>> (16 : Nat)) &&& BitVec.ofInt 64 2097151) = .value ((digest.extractLsb' 336 21).setWidth 64)
  exact congrArg PoisonOr.value (shift_mask21 digest 320 16 (by decide))

theorem r95_value (digest : BitVec 512) : r95 digest = val (inputDigits digest 17) := by
  change r95 digest = .value (BitVec.ofNat 64 (digest.extractLsb' 357 21).toNat)
  rw [widen_ofNat]
  change PoisonOr.value ((digest.extractLsb' 320 64 >>> (37 : Nat)) &&& BitVec.ofInt 64 2097151) = .value ((digest.extractLsb' 357 21).setWidth 64)
  exact congrArg PoisonOr.value (shift_mask21 digest 320 37 (by decide))

theorem r97_value (digest : BitVec 512) : r97 digest = val (inputDigits digest 18) := by
  change r97 digest = .value (BitVec.ofNat 64 (digest.extractLsb' 378 21).toNat)
  rw [widen_ofNat]
  change PoisonOr.value (SLLVM.fshlBV (digest.extractLsb' 384 64) (digest.extractLsb' 320 64) (BitVec.ofNat 64 6) &&& BitVec.ofInt 64 2097151) = .value ((digest.extractLsb' 378 21).setWidth 64)
  exact congrArg PoisonOr.value (fshl_mask21 digest 320 6 (by decide) (by decide))

theorem r99_value (digest : BitVec 512) : r99 digest = val (inputDigits digest 19) := by
  change r99 digest = .value (BitVec.ofNat 64 (digest.extractLsb' 399 21).toNat)
  rw [widen_ofNat]
  change PoisonOr.value ((digest.extractLsb' 384 64 >>> (15 : Nat)) &&& BitVec.ofInt 64 2097151) = .value ((digest.extractLsb' 399 21).setWidth 64)
  exact congrArg PoisonOr.value (shift_mask21 digest 384 15 (by decide))

theorem r101_value (digest : BitVec 512) : r101 digest = val (inputDigits digest 20) := by
  change r101 digest = .value (BitVec.ofNat 64 (digest.extractLsb' 420 21).toNat)
  rw [widen_ofNat]
  change PoisonOr.value ((digest.extractLsb' 384 64 >>> (36 : Nat)) &&& BitVec.ofInt 64 2097151) = .value ((digest.extractLsb' 420 21).setWidth 64)
  exact congrArg PoisonOr.value (shift_mask21 digest 384 36 (by decide))

theorem r103_value (digest : BitVec 512) : r103 digest = val (inputDigits digest 21) := by
  change r103 digest = .value (BitVec.ofNat 64 (digest.extractLsb' 441 21).toNat)
  rw [widen_ofNat]
  change PoisonOr.value (SLLVM.fshlBV (digest.extractLsb' 448 64) (digest.extractLsb' 384 64) (BitVec.ofNat 64 7) &&& BitVec.ofInt 64 2097151) = .value ((digest.extractLsb' 441 21).setWidth 64)
  exact congrArg PoisonOr.value (fshl_mask21 digest 384 7 (by decide) (by decide))

theorem r105_value (digest : BitVec 512) : r105 digest = val (inputDigits digest 22) := by
  change r105 digest = .value (BitVec.ofNat 64 (digest.extractLsb' 462 21).toNat)
  rw [widen_ofNat]
  change PoisonOr.value ((digest.extractLsb' 448 64 >>> (14 : Nat)) &&& BitVec.ofInt 64 2097151) = .value ((digest.extractLsb' 462 21).setWidth 64)
  exact congrArg PoisonOr.value (shift_mask21 digest 448 14 (by decide))

theorem r106_value (digest : BitVec 512) : r106 digest = val (inputDigits digest 23) := by
  change r106 digest = .value (BitVec.ofNat 64 (digest.extractLsb' 483 29).toNat)
  rw [widen_ofNat]
  change PoisonOr.value (digest.extractLsb' 448 64 >>> (35 : Nat)) = .value ((digest.extractLsb' 483 29).setWidth 64)
  exact congrArg PoisonOr.value (shift_tail29 digest)

end Registers
end Firedancer.Common.ScalarArithmetic
