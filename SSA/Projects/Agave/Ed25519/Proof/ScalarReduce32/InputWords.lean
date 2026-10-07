import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.Montgomery
import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.UnpackPhase

namespace Agave.Ed25519.ScalarReduce32.Execution
open LeanMLIR.RIR
open Arithmetic
set_option maxRecDepth 10000
set_option maxHeartbeats 3000000
set_option exponentiation.threshold 512

/-- The contiguous byte fragments actually assembled by the source loads. -/
def inputFragment (bytes : BitVec 256) (start width shift : Nat) : BitVec 64 :=
  (bytes.extractLsb' start width).setWidth 64 <<< shift

def inputFunnel (a b : BitVec 64) (shift : Nat) : BitVec 64 :=
  ((a ++ b) <<< shift).extractLsb' 64 64

/-- Exact source expressions in registers 176, 175, 174, 172, and 171. -/
def inputWords (bytes : BitVec 256) : Fin 5 → BitVec 64 :=
  ![inputFragment bytes 0 56 0 &&& 4503599627370495#64,
    inputFunnel (inputFragment bytes 64 40 0) (inputFragment bytes 0 64 0) 12,
    inputFunnel (inputFragment bytes 128 32 0) (inputFragment bytes 104 24 40) 24 &&&
      4503599627370495#64,
    inputFunnel (inputFragment bytes 192 16 0) (inputFragment bytes 128 64 0) 36,
    inputFragment bytes 208 48 16 >>> 16]

theorem input_mask_bits (i : Nat) :
    (4503599627370495#64).getLsbD i = decide (i < 52) := by
  change ((BitVec.allOnes 52).setWidth 64).getLsbD i = _
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_allOnes]
  grind

/-- Every actual unmasked funnel has exactly the required 52-bit width. -/
theorem inputWords_extract (bytes : BitVec 256) (limb : Fin 5) :
    inputWords bytes limb = (bytes.extractLsb' (52 * limb.val) 52).setWidth 64 := by
  fin_cases limb <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi
  all_goals
    dsimp [inputWords]
    simp only [inputFunnel, inputFragment, BitVec.getLsbD_and, input_mask_bits,
      BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth,
      BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_append]
    grind only [BitVec.getLsbD_of_ge]

theorem inputWords_bound (bytes : BitVec 256) (i : Fin 5) :
    (inputWords bytes i).toNat < 2 ^ 52 := by
  rw [inputWords_extract, BitVec.toNat_setWidth_of_le (by decide : 52 ≤ 64)]
  exact (bytes.extractLsb' (52 * i.val) 52).isLt

theorem scalar_fiveDigits_value (n : Nat) :
    limbs (n % 2 ^ 52) (n / 2 ^ 52 % 2 ^ 52) (n / 2 ^ 104 % 2 ^ 52)
      (n / 2 ^ 156 % 2 ^ 52) (n / 2 ^ 208 % 2 ^ 52) = n % 2 ^ 260 := by
  have h0 := Nat.mod_add_div n (2 ^ 52)
  have h1 := Nat.mod_add_div (n / 2 ^ 52) (2 ^ 52)
  have h2 := Nat.mod_add_div (n / 2 ^ 104) (2 ^ 52)
  have h3 := Nat.mod_add_div (n / 2 ^ 156) (2 ^ 52)
  have h4 := Nat.mod_add_div (n / 2 ^ 208) (2 ^ 52)
  have h5 := Nat.mod_add_div n (2 ^ 260)
  norm_num [limbs, radix, Nat.div_div_eq_div_mul] at h0 h1 h2 h3 h4 h5 ⊢
  omega

/-- The unpacked words represent all 256 input bits, including the high bit. -/
theorem inputWords_value (bytes : BitVec 256) :
    limbs (inputWords bytes 0).toNat (inputWords bytes 1).toNat
      (inputWords bytes 2).toNat (inputWords bytes 3).toNat (inputWords bytes 4).toNat =
      bytes.toNat := by
  have h := scalar_fiveDigits_value bytes.toNat
  rw [Nat.mod_eq_of_lt (bytes.isLt.trans (by decide : 2 ^ 256 < 2 ^ 260))] at h
  simp only [inputWords_extract, BitVec.toNat_setWidth_of_le (by decide : 52 ≤ 64),
    BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  change limbs (bytes.toNat / 2 ^ 0 % 2 ^ 52) (bytes.toNat / 2 ^ 52 % 2 ^ 52)
    (bytes.toNat / 2 ^ 104 % 2 ^ 52) (bytes.toNat / 2 ^ 156 % 2 ^ 52)
    (bytes.toNat / 2 ^ 208 % 2 ^ 52) = bytes.toNat
  simpa only [Nat.pow_zero, Nat.div_one] using h

end Agave.Ed25519.ScalarReduce32.Execution
