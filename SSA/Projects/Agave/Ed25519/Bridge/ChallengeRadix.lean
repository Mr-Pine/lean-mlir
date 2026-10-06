import SSA.Projects.Agave.Ed25519.Bridge.Challenge
import Mathlib.Tactic.FinCases

/-!
The wide-digest unpacking in pinned `solana-ed25519` 0.2.4,
`MLIR/source/src/backend/serial/u64/scalar.rs::Scalar52::from_bytes_wide`.

The definitions below transcribe the eight little-endian word reads and ten
radix-2^52 bitfield expressions. The proofs identify their exact integer value
for every 512-bit digest. This is source-expression arithmetic, not an RIR
memory/execution refinement or a Montgomery-multiplication correctness proof.
-/

namespace Agave.Ed25519.Bridge.Challenge

/-- Eight consecutive little-endian u64s from the 64-byte digest. -/
def digestWord (digest : BitVec 512) (i : Fin 8) : BitVec 64 :=
  digest.extractLsb' (i.val * 64) 64

def wideLow (digest : BitVec 512) : Fin 5 → BitVec 64 := ![
  digestWord digest 0 &&& 0xfffffffffffff#64,
  (digestWord digest 0 >>> 52 ||| digestWord digest 1 <<< 12) &&& 0xfffffffffffff#64,
  (digestWord digest 1 >>> 40 ||| digestWord digest 2 <<< 24) &&& 0xfffffffffffff#64,
  (digestWord digest 2 >>> 28 ||| digestWord digest 3 <<< 36) &&& 0xfffffffffffff#64,
  (digestWord digest 3 >>> 16 ||| digestWord digest 4 <<< 48) &&& 0xfffffffffffff#64]

def wideHigh (digest : BitVec 512) : Fin 5 → BitVec 64 := ![
  (digestWord digest 4 >>> 4) &&& 0xfffffffffffff#64,
  (digestWord digest 4 >>> 56 ||| digestWord digest 5 <<< 8) &&& 0xfffffffffffff#64,
  (digestWord digest 5 >>> 44 ||| digestWord digest 6 <<< 20) &&& 0xfffffffffffff#64,
  (digestWord digest 6 >>> 32 ||| digestWord digest 7 <<< 32) &&& 0xfffffffffffff#64,
  digestWord digest 7 >>> 20]

/-- The first digest byte is the low byte of word zero. -/
theorem digestWord_toNat (digest : BitVec 512) (i : Fin 8) :
    (digestWord digest i).toNat = (digest.toNat / 2 ^ (i.val * 64)) % 2 ^ 64 := by
  simp [digestWord, Nat.shiftRight_eq_div_pow]

private theorem mask52_eq :
    0xfffffffffffff#64 = (BitVec.allOnes 52).setWidth 64 := by
  decide +kernel

/-- A 52-bit window entirely inside one loaded word. -/
private theorem word_slice (digest : BitVec 512) (base shift : Nat)
    (hfit : shift + 52 ≤ 64) :
    ((digest.extractLsb' base 64) >>> shift) &&& 0xfffffffffffff#64 =
      (digest.extractLsb' (base + shift) 52).setWidth 64 := by
  rw [mask52_eq]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth, BitVec.getLsbD_allOnes,
    hj, decide_true, Bool.true_and]
  by_cases h52 : j < 52
  · have h64 : shift + j < 64 := by omega
    simp only [h52, h64, decide_true, Bool.true_and, Bool.and_true]
    congr 1
    omega
  · simp only [h52, decide_false, Bool.and_false, Bool.false_and]

/-- A 52-bit window crossing the boundary between two consecutive u64s. -/
private theorem words_slice (digest : BitVec 512) (base shift : Nat)
    (hshift : shift ≤ 64) :
    (((digest.extractLsb' base 64) >>> shift |||
        (digest.extractLsb' (base + 64) 64) <<< (64 - shift)) &&& 0xfffffffffffff#64) =
      (digest.extractLsb' (base + shift) 52).setWidth 64 := by
  rw [mask52_eq]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth,
    BitVec.getLsbD_allOnes, hj, decide_true, Bool.true_and]
  by_cases h52 : j < 52
  · simp only [h52, decide_true, Bool.true_and, Bool.and_true]
    by_cases h64 : shift + j < 64
    · have hleft : j < 64 - shift := by omega
      simp only [h64, hleft, decide_true, Bool.true_and,
        Bool.not_true, Bool.false_and, Bool.or_false]
      congr 1
      omega
    · have hleft : ¬j < 64 - shift := by omega
      have hsub : j - (64 - shift) < 64 := by omega
      simp only [h64, hleft, hsub, decide_false, decide_true, Bool.false_and,
        Bool.not_false, Bool.true_and, Bool.false_or]
      congr 1
      omega
  · simp only [h52, decide_false, Bool.and_false, Bool.false_and]

private theorem last_word_slice (digest : BitVec 512) :
    (digest.extractLsb' 448 64) >>> (20 : Nat) = (digest.extractLsb' 468 52).setWidth 64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_extractLsb',
    BitVec.getLsbD_setWidth, hj, decide_true, Bool.true_and]
  have hindex : 448 + (20 + j) = 468 + j := by omega
  rw [hindex]
  by_cases h44 : j < 44
  · have h64 : 20 + j < 64 := by omega
    have h52 : j < 52 := by omega
    simp only [h64, h52, decide_true]
  · have h64 : ¬20 + j < 64 := by omega
    have hzero : digest.getLsbD (468 + j) = false :=
      BitVec.getLsbD_of_ge _ _ (by omega)
    simp only [h64, hzero, decide_false, Bool.and_false]

theorem wideLow_eq_extract (digest : BitVec 512) (i : Fin 5) :
    wideLow digest i = (digest.extractLsb' (i.val * 52) 52).setWidth 64 := by
  fin_cases i
  · simpa [wideLow, digestWord] using word_slice digest 0 0 (by omega)
  · exact words_slice digest 0 52 (by omega)
  · exact words_slice digest 64 40 (by omega)
  · exact words_slice digest 128 28 (by omega)
  · exact words_slice digest 192 16 (by omega)

theorem wideHigh_eq_extract (digest : BitVec 512) (i : Fin 5) :
    wideHigh digest i = (digest.extractLsb' (260 + i.val * 52) 52).setWidth 64 := by
  fin_cases i
  · exact word_slice digest 256 4 (by omega)
  · exact words_slice digest 256 56 (by omega)
  · exact words_slice digest 320 44 (by omega)
  · exact words_slice digest 384 32 (by omega)
  · exact last_word_slice digest

theorem wideLow_tight (digest : BitVec 512) (i : Fin 5) :
    (wideLow digest i).toNat < 2 ^ 52 := by
  rw [wideLow_eq_extract, BitVec.toNat_setWidth_of_le (by decide)]
  exact BitVec.isLt _

theorem wideHigh_tight (digest : BitVec 512) (i : Fin 5) :
    (wideHigh digest i).toNat < 2 ^ 52 := by
  rw [wideHigh_eq_extract, BitVec.toNat_setWidth_of_le (by decide)]
  exact BitVec.isLt _

/-- The integer represented by five radix-2^52 limbs. -/
def value52 (limbs : Fin 5 → BitVec 64) : Nat :=
  (limbs 0).toNat + 2 ^ 52 * (limbs 1).toNat + 2 ^ 104 * (limbs 2).toNat +
    2 ^ 156 * (limbs 3).toNat + 2 ^ 208 * (limbs 4).toNat

def pack52 (limbs : Fin 5 → BitVec 64) : BitVec 260 :=
  (limbs 4).setWidth 52 ++ (limbs 3).setWidth 52 ++ (limbs 2).setWidth 52 ++
    (limbs 1).setWidth 52 ++ (limbs 0).setWidth 52

private theorem append_toNat (x : BitVec m) (y : BitVec n) :
    (x ++ y).toNat = x.toNat * 2 ^ n + y.toNat := by
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt y.isLt, Nat.shiftLeft_eq]

theorem pack52_toNat (limbs : Fin 5 → BitVec 64)
    (htight : ∀ i, (limbs i).toNat < 2 ^ 52) :
    (pack52 limbs).toNat = value52 limbs := by
  have htrunc (i : Fin 5) : ((limbs i).setWidth 52).toNat = (limbs i).toNat := by
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (htight i)]
  simp only [pack52, append_toNat, htrunc, value52]
  norm_num
  ring

theorem pack52_wideLow (digest : BitVec 512) :
    pack52 (wideLow digest) = digest.extractLsb' 0 260 := by
  simp only [pack52, wideLow_eq_extract,
    BitVec.setWidth_setWidth_of_le _ (by decide : 52 ≤ 64), BitVec.setWidth_eq]
  repeat rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (by decide +kernel)]
  rfl

theorem pack52_wideHigh (digest : BitVec 512) :
    pack52 (wideHigh digest) = digest.extractLsb' 260 260 := by
  simp only [pack52, wideHigh_eq_extract,
    BitVec.setWidth_setWidth_of_le _ (by decide : 52 ≤ 64), BitVec.setWidth_eq]
  repeat rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (by decide +kernel)]
  rfl

theorem wideLow_value (digest : BitVec 512) :
    value52 (wideLow digest) = digest.toNat % 2 ^ 260 := by
  rw [← pack52_toNat _ (wideLow_tight digest), pack52_wideLow]
  rfl

theorem wideHigh_value (digest : BitVec 512) :
    value52 (wideHigh digest) = digest.toNat / 2 ^ 260 := by
  rw [← pack52_toNat _ (wideHigh_tight digest), pack52_wideHigh]
  have hpow : (2 : Nat) ^ 512 < 2 ^ 260 * 2 ^ 260 := by
    rw [← Nat.pow_add]
    exact Nat.pow_lt_pow_right (by decide) (by decide)
  have hbound : digest.toNat / 2 ^ 260 < 2 ^ 260 :=
    (Nat.div_lt_iff_lt_mul (Nat.pow_pos (by decide : 0 < 2))).mpr (digest.isLt.trans hpow)
  simpa only [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow] using Nat.mod_eq_of_lt hbound

/-- All 512 input bits are retained. The second group begins at bit 260,
not bit 256; the final high limb therefore has only 44 significant bits. -/
theorem wide_values_reconstruct (digest : BitVec 512) :
    value52 (wideLow digest) + 2 ^ 260 * value52 (wideHigh digest) = digest.toNat := by
  rw [wideLow_value, wideHigh_value, Nat.mod_add_div]

/-- The source-level wide-input representation has exactly the byte-based
hash-to-scalar value. Only the ensuing Montgomery operations remain to refine. -/
theorem hashToScalar_eq_wide_values (digest : BitVec 512) :
    hashToScalar digest =
      (value52 (wideLow digest) + 2 ^ 260 * value52 (wideHigh digest)) % subgroupOrder := by
  rw [wide_values_reconstruct]
  rfl

end Agave.Ed25519.Bridge.Challenge
