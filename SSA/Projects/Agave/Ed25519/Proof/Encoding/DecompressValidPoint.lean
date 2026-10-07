import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.DecodeWords
import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressValidPointLayout

/-! The concrete decompressor word schedule supplies a `ValidPoint`, retaining
all four exact limb arrays. This closes the mathematical decoder and payload
representation boundary independently of the remaining RIR instruction proof.
No canonical representative is chosen from an affine point. -/
namespace Agave.Ed25519.Encoding.Decompress.Valid
open LeanMLIR.RIR
open Verifier
open Verifier.Execution
open Execution

attribute [local irreducible] step1 Decode.wordStep1 Decode.pointWords

/-- Forget bounds without changing any machine word. -/
def words (P : Decode.PointWords) : Key.PointWords :=
  ⟨P.X.limbs, P.Y.limbs, P.Z.limbs, P.T.limbs⟩

theorem wordValue_eq_curveValue (a : Words) : wordValue a = Key.curveValue a := rfl

theorem words_bytes (P : Decode.PointWords) : (words P).bytes = Decode.pointPayload P := by
  exact pointPayload_eq (words P)

theorem pointWords_represents (bytes : BitVec 256) (hvalid : (step1 bytes).1 = true) :
    (words (Decode.pointWords bytes (Decode.wordStep1 bytes).2)).Represents
      (step2 bytes hvalid) := by
  obtain ⟨hx, hy, hz, ht⟩ := Decode.pointWords_value bytes
  have hX : (step2 bytes hvalid).x =
      if bytes[255] then -(step1 bytes).2 else (step1 bytes).2 := by
    cases hs : bytes[255] <;>
      simp [step2, applySign, unsignedPoint, Edwards.Point.neg_x, hs] <;> rfl
  have hY : (step2 bytes hvalid).y = y bytes := by
    simp [step2, unsignedPoint]
  change wordValue (Decode.pointWords bytes (Decode.wordStep1 bytes).2).Z.limbs ≠ 0 ∧
    wordValue (Decode.pointWords bytes (Decode.wordStep1 bytes).2).X.limbs =
      (step2 bytes hvalid).x * wordValue (Decode.pointWords bytes (Decode.wordStep1 bytes).2).Z.limbs ∧
    wordValue (Decode.pointWords bytes (Decode.wordStep1 bytes).2).Y.limbs =
      (step2 bytes hvalid).y * wordValue (Decode.pointWords bytes (Decode.wordStep1 bytes).2).Z.limbs ∧
    wordValue (Decode.pointWords bytes (Decode.wordStep1 bytes).2).T.limbs =
      (step2 bytes hvalid).x * (step2 bytes hvalid).y *
        wordValue (Decode.pointWords bytes (Decode.wordStep1 bytes).2).Z.limbs
  simp only [hx, hy, hz, ht, hX, hY, mul_one, ne_eq, one_ne_zero, not_false_eq_true]
  exact ⟨trivial, rfl, trivial, rfl⟩

/-- The successful value is constructed directly from the exact parsed,
signed, squared and multiplied words and their proved tight bounds. -/
def point (bytes : BitVec 256) (hvalid : (step1 bytes).1 = true) : ValidPoint where
  words := words (Decode.pointWords bytes (Decode.wordStep1 bytes).2)
  curve := step2 bytes hvalid
  tightX := (Decode.pointWords bytes (Decode.wordStep1 bytes).2).X.tight
  tightY := (Decode.pointWords bytes (Decode.wordStep1 bytes).2).Y.tight
  tightZ := (Decode.pointWords bytes (Decode.wordStep1 bytes).2).Z.tight
  tightT := (Decode.pointWords bytes (Decode.wordStep1 bytes).2).T.tight
  represents := pointWords_represents bytes hvalid

@[simp] theorem point_curve (bytes : BitVec 256) (hvalid : (step1 bytes).1 = true) :
    (point bytes hvalid).curve = step2 bytes hvalid := rfl

theorem point_bytes (bytes : BitVec 256) (hvalid : (step1 bytes).1 = true) :
    (point bytes hvalid).bytes =
      Decode.pointPayload (Decode.pointWords bytes (Decode.wordStep1 bytes).2) :=
  words_bytes _

/-- A fixed, representation-preserving decoder for the concrete verifier
interface. This is a word specification, not an assertion of RIR execution. -/
def decode (bytes : Bytes32) : Option ValidPoint :=
  if hvalid : (step1 bytes).1 = true then some (point bytes hvalid) else none

theorem decode_curve (bytes : Bytes32) :
    (decode bytes).map ValidPoint.curve = decompress bytes := by
  by_cases hvalid : (step1 bytes).1 = true
  · simp only [decode, decompress, dite_eq_left hvalid, Option.map_some, point_curve]
  · simp only [decode, decompress, dite_eq_right hvalid, Option.map_none]

theorem decode_bytes (bytes : Bytes32) :
    (decode bytes).map ValidPoint.bytes =
      (Decode.wordDecode bytes).map Decode.pointPayload := by
  have hflag := congrArg Prod.fst (Decode.wordStep1_value bytes)
  change (Decode.wordStep1 bytes).1 = (step1 bytes).1 at hflag
  by_cases hvalid : (step1 bytes).1 = true
  · simp only [decode, Decode.wordDecode, hflag, dite_eq_left hvalid, ite_eq_left hvalid,
      Option.map_some, point_bytes]
  · simp only [decode, Decode.wordDecode, hflag, dite_eq_right hvalid, ite_eq_right hvalid,
      Option.map_none]

/-- Unconditional soundness and completeness over every 256-bit input.
This discharges `ValidPoint.DecoderCorrect` for the concrete word decoder. -/
theorem decoderCorrect : ValidPoint.DecoderCorrect decode := by
  constructor
  · intro bytes P h
    apply (decompress_eq_some_iff bytes P.curve).mp
    rw [← decode_curve, h]
    rfl
  · intro bytes A henc
    have hs := (decompress_eq_some_iff bytes A).mpr henc
    rw [← decode_curve] at hs
    cases hd : decode bytes with
    | none => simp only [hd, Option.map_none] at hs; cases hs
    | some P =>
      refine ⟨P, rfl, ?_⟩
      simpa only [hd, Option.map_some, Option.some.injEq] using hs

theorem decode_eq_none_iff (bytes : Bytes32) :
    decode bytes = none ↔ ¬∃ P, Bridge.Encodes bytes P := by
  rw [← decompress_eq_none_iff, ← decode_curve]
  simp

theorem decode_eq_some_iff (bytes : Bytes32) (A : Bridge.CurvePoint) :
    (∃ P, decode bytes = some P ∧ P.curve = A) ↔ Bridge.Encodes bytes A := by
  constructor
  · rintro ⟨P, hP, rfl⟩
    exact decoderCorrect.sound bytes P hP
  · exact decoderCorrect.complete bytes A

theorem shared_correct :
    RepresentedSharedCorrect (ValidPoint.shared decode) ValidPoint.curve Fin.val :=
  ValidPoint.shared_correct decode decoderCorrect

end Agave.Ed25519.Encoding.Decompress.Valid
