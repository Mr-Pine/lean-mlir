import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.InputFieldFlags
import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.MontgomerySchedule

/-! Exact funnel-shift expressions used by the outer wrapper to split at bit
260. Register fragments are slices of the original little-endian 512-bit input.
The finite bit-index proofs enumerate 64 positions, never input values. -/
namespace Agave.Ed25519.Verifier.Execution.ScalarWide
open Agave.Ed25519.Bridge
open ScalarMontgomeryMul

/-- The exact LLVM fshl word expression for the fixed source shifts. -/
def funnel64 (a b : BitVec 64) (shift : Nat) : BitVec 64 :=
  ((a ++ b) <<< shift).extractLsb' 64 64

def inputFragment (bytes : BitVec 512) (start width shift : Nat) : BitVec 64 :=
  (bytes.extractLsb' start width).setWidth 64 <<< shift

/-- Source registers 262, 263, 267, 268, and 272. -/
def lowSplitWords (bytes : BitVec 512) : Fin 5 → BitVec 64 :=
  ![inputFragment bytes 0 56 0 &&& 4503599627370495#64,
    funnel64 (inputFragment bytes 64 40 0) (inputFragment bytes 0 64 0) 12,
    funnel64 (inputFragment bytes 128 32 0) (inputFragment bytes 104 24 40) 24 &&& 4503599627370495#64,
    funnel64 (inputFragment bytes 192 16 0) (inputFragment bytes 128 64 0) 36,
    funnel64 (inputFragment bytes 256 8 0) (inputFragment bytes 208 48 16) 48 &&& 4503599627370495#64]

/-- Source registers 274, 277, 278, 282, and 284. -/
def highSplitWords (bytes : BitVec 512) : Fin 5 → BitVec 64 :=
  ![(inputFragment bytes 256 64 0 >>> 4) &&& 4503599627370495#64,
    funnel64 (inputFragment bytes 320 48 0) (inputFragment bytes 304 16 48) 8 &&& 4503599627370495#64,
    funnel64 (inputFragment bytes 384 32 0) (inputFragment bytes 320 64 0) 20,
    funnel64 (inputFragment bytes 448 24 0) (inputFragment bytes 416 32 32) 32 &&& 4503599627370495#64,
    inputFragment bytes 448 64 0 >>> 20]

/-- The mask contains exactly 52 low one bits. -/
theorem mask52_bits (i : Nat) :
    (4503599627370495#64).getLsbD i = decide (i < 52) := by
  change ((BitVec.allOnes 52).setWidth 64).getLsbD i = _
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_allOnes]
  grind

/-- Every low-half source word is precisely its 52-bit input slice. -/
theorem lowSplitWords_extract (bytes : BitVec 512) (limb : Fin 5) :
    lowSplitWords bytes limb = (bytes.extractLsb' (52 * limb.val) 52).setWidth 64 := by
  fin_cases limb <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi
  all_goals
    dsimp [lowSplitWords]
    simp only [funnel64, inputFragment, BitVec.getLsbD_and, mask52_bits,
      BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth,
      BitVec.getLsbD_shiftLeft, BitVec.getLsbD_append]
    grind only [BitVec.getLsbD_of_ge]

/-- Every high-half source word is precisely its slice after bit 260. -/
theorem highSplitWords_extract (bytes : BitVec 512) (limb : Fin 5) :
    highSplitWords bytes limb = (bytes.extractLsb' (260 + 52 * limb.val) 52).setWidth 64 := by
  fin_cases limb <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi
  all_goals
    dsimp [highSplitWords]
    simp only [funnel64, inputFragment, BitVec.getLsbD_and, mask52_bits,
      BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth,
      BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_append]
    grind only [BitVec.getLsbD_of_ge]

theorem lowSplitWords_bound (bytes : BitVec 512) (i : Fin 5) :
    (lowSplitWords bytes i).toNat < 2 ^ 52 := by
  rw [lowSplitWords_extract, BitVec.toNat_setWidth_of_le (by decide : 52 ≤ 64)]
  exact (bytes.extractLsb' (52 * i.val) 52).isLt

theorem highSplitWords_bound (bytes : BitVec 512) (i : Fin 5) :
    (highSplitWords bytes i).toNat < 2 ^ 52 := by
  rw [highSplitWords_extract, BitVec.toNat_setWidth_of_le (by decide : 52 ≤ 64)]
  exact (bytes.extractLsb' (260 + 52 * i.val) 52).isLt

end Agave.Ed25519.Verifier.Execution.ScalarWide
