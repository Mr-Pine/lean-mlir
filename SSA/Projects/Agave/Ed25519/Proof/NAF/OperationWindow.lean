import SSA.Projects.Agave.Ed25519.Proof.NAF.WordWindow
import SSA.Projects.RIR.Semantics.Operations.Scalar

/-! Poison-aware RIR semantics of the extracted NAF window arithmetic after
capturing the two word loads. The source load/GEP and buffer initialization
contracts are separate; this theorem covers every arithmetic instruction and
its emitted flags in the window fragment. -/
namespace Agave.Ed25519.NAF.WordWindow

open LeanMLIR.RIR

theorem compiled_negation_no_overflow : ∀ pos : Fin 256,
    (0#64).ssubOverflow (BitVec.ofNat 64 pos.val) = false := by
  decide +kernel

/-- The original operations, including LLVM's signed-no-wrap negation and
poison-producing shifts. The two reads use a captured five-word buffer. -/
def capturedWindow (bits : BitVec 320) (pos : Fin 256) (width : Nat) : PoisonOr (BitVec 64) := do
  let p := BitVec.ofNat 64 pos.val
  let index ← Operation.lshr false (.value p) (.value 6)
  let bit ← Operation.and (.value p) (.value 63)
  let low ← Operation.lshr false (.value (word bits index.toNat)) (.value bit)
  let buf ← if bit.toNat < 64 - width then pure low else do
    let neg ← Operation.sub { nsw := true } (.value 0#64) (.value p)
    let shift ← Operation.and (.value neg) (.value 63)
    let high ← Operation.shl {} (.value (word bits (index.toNat + 1))) (.value shift)
    Operation.or false (.value low) (.value high)
  Operation.and (.value buf) (.value (BitVec.ofNat 64 (2 ^ width - 1)))

theorem capturedWindow_exact (bits : BitVec 320) (pos : Fin 256) (width : Nat)
    (hw : Supported width) :
    capturedWindow bits pos width =
      .value (rawWindow bits pos.val width &&& BitVec.ofNat 64 (2 ^ width - 1)) := by
  obtain ⟨hindex, hbit⟩ := compiled_indices pos
  have hb : ¬pos.val % 64 ≥ 64 := by omega
  have hneg := compiled_negation_no_overflow pos
  unfold capturedWindow rawWindow
  by_cases h : pos.val % 64 < 64 - width
  · simp [Operation.lshr, Operation.and, hindex, hbit, hb, h]
  · have hshift := compiled_cross_shift width hw pos h
    have hs := cross_word_shift_safe pos.val width hw h
    have hs' : ¬64 - pos.val % 64 ≥ 64 := by omega
    have hshiftNat : ((2 ^ 64 - pos.val % 2 ^ 64) % 2 ^ 64 &&& 63) =
        64 - pos.val % 64 := by
      simpa only [BitVec.toNat_and, BitVec.toNat_neg, BitVec.toNat_ofNat] using hshift
    norm_num only [Nat.reducePow] at hshiftNat
    simp [Operation.lshr, Operation.and, Operation.sub, Operation.shl, Operation.or,
      hindex, hbit, hb, h, hneg]
    rw [hshiftNat]
    simp only [if_neg hs']

/-- The RIR arithmetic fragment is nonpoison and returns the normalized window
used by the NAF carry/digit proof. -/
theorem capturedWindow_toNat (scalar : BitVec 256) (pos : Fin 256)
    (width : Nat) (hw : Supported width) :
    BitVec.toNat <$> capturedWindow (scalarBuffer scalar) pos width =
      .value ((scalar.toNat / 2 ^ pos.val) % 2 ^ width) := by
  rw [capturedWindow_exact _ pos width hw]
  change PoisonOr.value (window (scalarBuffer scalar) pos.val width) = _
  rw [scalar_window_eq_tail scalar pos.val width hw]

end Agave.Ed25519.NAF.WordWindow
