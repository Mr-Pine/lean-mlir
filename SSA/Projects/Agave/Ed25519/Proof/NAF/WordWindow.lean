import SSA.Projects.Agave.Ed25519.Spec.NAF
import Mathlib

/-!
# The extracted NAF five-word window

The emitted width-five and width-eight CFGs load word `pos >>> 6`, shift by
`pos & 63`, and, in the crossing branch, OR the next word shifted by
`(-pos) & 63`. The buffer comprises all 256 scalar bits followed by a zero word.
These theorems prove that exact bit network equals the natural tail/window
used in `Spec.NAF`. Memory loads still require the buffer-representation and
GEP contracts; no claim about complete CFG execution is made here.
-/
namespace Agave.Ed25519.NAF.WordWindow

def word (bits : BitVec 320) (i : Nat) : BitVec 64 := bits.extractLsb' (64*i) 64

def rawWindow (bits : BitVec 320) (pos width : Nat) : BitVec 64 :=
  let low := word bits (pos / 64) >>> (pos % 64)
  if pos % 64 < 64 - width then low
  else low ||| (word bits (pos / 64 + 1) <<< (64 - pos % 64))

def window (bits : BitVec 320) (pos width : Nat) : Nat :=
  (rawWindow bits pos width &&& BitVec.ofNat 64 (2 ^ width - 1)).toNat

/-- The precise masked indices emitted by LLVM, for every source loop position. -/
theorem compiled_indices : ∀ pos : Fin 256,
    (BitVec.ofNat 64 pos.val >>> 6).toNat = pos.val / 64 ∧
    (BitVec.ofNat 64 pos.val &&& 63#64).toNat = pos.val % 64 := by
  decide +kernel

/-- The compiler replaces `64-bit_idx` by masked negation. The crossing guard
excludes bit_idx=0, the one point where these two natural numbers differ. -/
theorem compiled_cross_shift (width : Nat) (hw : Supported width) :
    ∀ pos : Fin 256, ¬pos.val % 64 < 64 - width →
      ((-BitVec.ofNat 64 pos.val) &&& 63#64).toNat = 64 - pos.val % 64 := by
  rcases hw with rfl | rfl <;> decide +kernel

/-- Literal compiler index and shift arithmetic, prior to the final low-bit mask. -/
def compiledRawWindow (bits : BitVec 320) (pos : Fin 256) (width : Nat) : BitVec 64 :=
  let p := BitVec.ofNat 64 pos.val
  let index := (p >>> 6).toNat
  let bit := (p &&& 63#64).toNat
  let low := word bits index >>> bit
  if bit < 64 - width then low
  else low ||| (word bits (index + 1) <<< (((-p) &&& 63#64).toNat))

theorem compiledRawWindow_eq (bits : BitVec 320) (pos : Fin 256) (width : Nat)
    (hw : Supported width) : compiledRawWindow bits pos width = rawWindow bits pos.val width := by
  obtain ⟨hindex, hbit⟩ := compiled_indices pos
  simp only [compiledRawWindow, hindex, hbit, rawWindow]
  split_ifs with h
  · rfl
  · rw [compiled_cross_shift width hw pos h]

/-- Bit-level proof works for arbitrary 320-bit buffers, so it includes every
scalar and needs no limb-range or zero-padding assumption. -/
theorem rawWindow_extract (bits : BitVec 320) (pos width : Nat)
    (hw : Supported width) :
    (rawWindow bits pos width).extractLsb' 0 width = bits.extractLsb' pos width := by
  have hw64 : width ≤ 64 := by rcases hw with rfl | rfl <;> omega
  have hb : pos % 64 < 64 := Nat.mod_lt _ (by decide)
  have hd := Nat.mod_add_div pos 64
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hi64 : i < 64 := by omega
  unfold rawWindow
  split_ifs with hcross
  · have hlo : pos % 64 + i < 64 := by omega
    have heq : 64 * (pos / 64) + (pos % 64 + i) = pos + i := by omega
    simp [word, BitVec.getLsbD_extractLsb', BitVec.getLsbD_ushiftRight, hi, hlo, heq]
  · by_cases hlo : pos % 64 + i < 64
    · have hshift : i < 64 - pos % 64 := by omega
      have heq : 64 * (pos / 64) + (pos % 64 + i) = pos + i := by omega
      simp [word, BitVec.getLsbD_extractLsb', BitVec.getLsbD_ushiftRight,
        BitVec.getLsbD_shiftLeft, hi, hi64, hlo, hshift, heq]
    · have hshift : ¬i < 64 - pos % 64 := by omega
      have hsub : i - (64 - pos % 64) < 64 := by omega
      have heq : 64 * (pos / 64 + 1) + (i - (64 - pos % 64)) = pos + i := by omega
      simp [word, BitVec.getLsbD_extractLsb', BitVec.getLsbD_ushiftRight,
        BitVec.getLsbD_shiftLeft, hi, hi64, hlo, hshift, hsub, heq]

theorem mask_eq_extract (x : BitVec 64) (width : Nat) (hw : Supported width) :
    (x &&& BitVec.ofNat 64 (2 ^ width - 1)).toNat =
      (x.extractLsb' 0 width).toNat := by
  have hmask : 2 ^ width - 1 < 2 ^ 64 := by rcases hw with rfl | rfl <;> norm_num
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hmask,
    Nat.and_two_pow_sub_one_eq_mod, BitVec.extractLsb'_toNat, Nat.shiftRight_zero]

/-- Exact correspondence with the normalized natural tail's low-width window. -/
theorem window_eq_tail (bits : BitVec 320) (pos width : Nat) (hw : Supported width) :
    window bits pos width = (bits.toNat / 2 ^ pos) % 2 ^ width := by
  rw [window, mask_eq_extract _ width hw, rawWindow_extract bits pos width hw]
  simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]

/-- Zero-extend the source's 256 scalar bits to its five-u64 temporary buffer. -/
def scalarBuffer (scalar : BitVec 256) : BitVec 320 := scalar.setWidth 320

theorem scalarBuffer_value (scalar : BitVec 256) : (scalarBuffer scalar).toNat = scalar.toNat := by
  exact BitVec.toNat_setWidth_of_le (by decide)

theorem scalar_window_eq_tail (scalar : BitVec 256) (pos width : Nat) (hw : Supported width) :
    window (scalarBuffer scalar) pos width = (scalar.toNat / 2 ^ pos) % 2 ^ width := by
  rw [window_eq_tail _ pos width hw, scalarBuffer_value]

theorem compiled_window_eq_tail (scalar : BitVec 256) (pos : Fin 256)
    (width : Nat) (hw : Supported width) :
    (compiledRawWindow (scalarBuffer scalar) pos width &&&
      BitVec.ofNat 64 (2 ^ width - 1)).toNat =
        (scalar.toNat / 2 ^ pos.val) % 2 ^ width := by
  rw [compiledRawWindow_eq _ pos width hw]
  exact scalar_window_eq_tail scalar pos.val width hw

end Agave.Ed25519.NAF.WordWindow
