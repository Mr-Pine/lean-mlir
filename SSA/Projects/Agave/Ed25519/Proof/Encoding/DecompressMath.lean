import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressSqrt
import SSA.Projects.Agave.Ed25519.Proof.Encoding.PointBytes
import SSA.Projects.Agave.Ed25519.Proof.Encoding.FromBytesWord
import SSA.Projects.Agave.Ed25519.Bridge.SmallOrder

/-!
The pinned decompressor's field interpretation refines the shared permissive
encoding relation for every 32-byte string. `decompress_eq_some_iff` has no
canonicality, nonzero-coordinate, or subgroup hypotheses. Its converse also
establishes complete rejection of inputs that encode no curve point.

This is a source-formula theorem. `decompress` below is not an imported RIR
program. `DecompressExecution` separately imports and links the exact decoder
and its complete call closure, but the full memory/control-flow refinement is
still outstanding. The theorem `fromBytesWord_field` connects its byte
interpretation to the word-level parser theorem; it does not fill that gap.
-/

namespace Agave.Ed25519.Encoding.Decompress

open _root_.Ed25519 Bridge

-- Composition uses the proved result contract, never definitional evaluation
-- of the entire square-root algorithm under a coordinate or `ZMod.val`.
attribute [local irreducible] sqrtRatio

/-- All 255 y bits are converted to the field; no canonical-y check occurs. -/
def y (bytes : BitVec 256) : K := (bytes.extractLsb' 0 255).toNat

theorem fromBytesWord_field (bytes : BitVec 256) :
    (Field.serialValue (fromBytesWord bytes) : K) = y bytes := by
  simpa only [y] using congrArg (fun n : Nat => (n : K)) (fromBytesWord_value bytes)

def numerator (bytes : BitVec 256) : K := y bytes ^ 2 - 1
def denominator (bytes : BitVec 256) : K := d * y bytes ^ 2 + 1

theorem denominator_ne_zero (bytes : BitVec 256) : denominator bytes ≠ 0 :=
  denom_ne_zero _

def step1 (bytes : BitVec 256) : Bool × K :=
  sqrtRatio (numerator bytes) (denominator bytes)

theorem step1_success_iff (bytes : BitVec 256) :
    (step1 bytes).1 = true ↔ IsSquare (numerator bytes / denominator bytes) := by
  rw [step1]
  exact sqrtRatio_success_iff (numerator bytes) (denominator bytes)
    (denominator_ne_zero bytes)

theorem step1_even (bytes : BitVec 256) : (step1 bytes).2.val % 2 = 0 := by
  rw [step1]
  exact sqrtRatio_even (numerator bytes) (denominator bytes)

theorem step1_root (bytes : BitVec 256) (hvalid : (step1 bytes).1 = true) :
    (step1 bytes).2 ^ 2 * denominator bytes = numerator bytes := by
  rw [step1] at hvalid ⊢
  exact sqrtRatio_root (numerator bytes) (denominator bytes) hvalid

theorem step1_onCurve (bytes : BitVec 256) (hvalid : (step1 bytes).1 = true) :
    curve.OnCurve (step1 bytes).2 (y bytes) := by
  have hroot := step1_root bytes hvalid
  simp only [numerator, denominator] at hroot
  change -(step1 bytes).2 ^ 2 + y bytes ^ 2 =
    1 + d * (step1 bytes).2 ^ 2 * y bytes ^ 2
  linear_combination -hroot

def unsignedPoint (bytes : BitVec 256) (hvalid : (step1 bytes).1 = true) : CurvePoint :=
  ⟨(step1 bytes).2, y bytes, step1_onCurve bytes hvalid⟩

/-- `decompress::step_2`: conditionally negate the even root, with no
negative-zero or low-order rejection in the decompression helper. -/
def step2 (bytes : BitVec 256) (hvalid : (step1 bytes).1 = true) : CurvePoint :=
  applySign (unsignedPoint bytes hvalid) bytes[255]

theorem step2_encodes (bytes : BitVec 256) (hvalid : (step1 bytes).1 = true) :
    Encodes bytes (step2 bytes hvalid) := by
  unfold step2
  apply applySign_encodes
  · rfl
  · simpa only [unsignedPoint] using step1_even bytes

/-- The `Option` branch of `CompressedEdwardsY::decompress`, interpreted in
the concrete mathematical field and group. -/
def decompress (bytes : BitVec 256) : Option CurvePoint :=
  if hvalid : (step1 bytes).1 = true then some (step2 bytes hvalid) else none

theorem isSquare_of_encodes (bytes : BitVec 256) (P : CurvePoint)
    (henc : Encodes bytes P) : IsSquare (numerator bytes / denominator bytes) := by
  apply (isSquare_div_iff (denominator_ne_zero bytes)).mpr
  refine ⟨P.x, ?_⟩
  change P.x ^ 2 * (d * y bytes ^ 2 + 1) = y bytes ^ 2 - 1
  have hy : P.y = y bytes := henc.1
  rw [← hy]
  exact sq_mul_den P

/-- Full soundness and completeness on all 256 input bits. Noncanonical y,
zero-root sign aliases, and low-order points are included without premises. -/
theorem decompress_eq_some_iff (bytes : BitVec 256) (P : CurvePoint) :
    decompress bytes = some P ↔ Encodes bytes P := by
  constructor
  · unfold decompress
    split
    · rename_i hvalid
      intro h
      cases Option.some.inj h
      exact step2_encodes bytes hvalid
    · intro h
      cases h
  · intro henc
    have hvalid := (step1_success_iff bytes).mpr (isSquare_of_encodes bytes P henc)
    rw [decompress, dif_pos hvalid]
    exact congrArg some (encodes_unique (step2_encodes bytes hvalid) henc)

/-- An invalid square root is precisely a `none` result. -/
theorem decompress_eq_none_iff_nonsquare (bytes : BitVec 256) :
    decompress bytes = none ↔ ¬IsSquare (numerator bytes / denominator bytes) := by
  unfold decompress
  split
  · rename_i hvalid
    simp [← step1_success_iff, hvalid]
  · rename_i hinvalid
    simp [← step1_success_iff, hinvalid]

theorem decompress_eq_none_iff (bytes : BitVec 256) :
    decompress bytes = none ↔ ¬∃ P, Encodes bytes P := by
  constructor
  · intro hnone ⟨P, henc⟩
    have hsome := (decompress_eq_some_iff bytes P).mpr henc
    rw [hnone] at hsome
    cases hsome
  · intro hnone
    cases hresult : decompress bytes with
    | none => rfl
    | some P => exact False.elim (hnone ⟨P, (decompress_eq_some_iff bytes P).mp hresult⟩)

/-- Every point round-trips through canonical compression, including torsion. -/
theorem decompress_compress (P : CurvePoint) : decompress (compress P) = some P :=
  (decompress_eq_some_iff _ _).mpr (compress_encodes P)

/-- Noncanonical y aliases with the same sign have exactly the same result,
including failure. Equality is in the field, not in the 255-bit integer. -/
theorem decompress_congr (left right : BitVec 256)
    (hy : y left = y right) (hs : left[255] = right[255]) :
    decompress left = decompress right := by
  apply Option.ext
  intro P
  rw [decompress_eq_some_iff, decompress_eq_some_iff]
  change (P.y = y left ∧ (P.x ≠ 0 → (P.x.val % 2 = 0 ↔ left[255] = false))) ↔
    (P.y = y right ∧ (P.x ≠ 0 → (P.x.val % 2 = 0 ↔ right[255] = false)))
  rw [hy, hs]

/-- Either sign bit succeeds when the decoded point has x=0. Only the
reduced y-coordinate is required, so this also includes noncanonical aliases. -/
theorem decompress_zero_x (bytes : BitVec 256) (P : CurvePoint)
    (hx : P.x = 0) (hy : P.y = y bytes) : decompress bytes = some P := by
  apply (decompress_eq_some_iff _ _).mpr
  exact ⟨hy, fun hne => False.elim (hne hx)⟩

/-- Decoding itself accepts every encoding of a low-order point. The strict
verifier's later small-order check is a separate operation. -/
theorem decompress_small_order_iff (bytes : BitVec 256) :
    (∃ P, decompress bytes = some P ∧ 8 • P = 0) ↔
      ∃ P : CurvePoint, Encodes bytes P ∧ (P.x, P.y) ∈ lowOrder := by
  simp only [decompress_eq_some_iff, eight_nsmul_eq_zero_iff_mem_lowOrder]

/-- Any byte-level decoder shown to execute this source interpretation gets
the complete encoding contract. The equality premise is the outstanding
machine refinement; this theorem does not postulate it. -/
theorem refinement_of_eq (machine : BitVec 256 → Option CurvePoint)
    (hexecution : ∀ bytes, machine bytes = decompress bytes)
    (bytes : BitVec 256) (P : CurvePoint) :
    machine bytes = some P ↔ Encodes bytes P := by
  rw [hexecution bytes, decompress_eq_some_iff]

end Agave.Ed25519.Encoding.Decompress
