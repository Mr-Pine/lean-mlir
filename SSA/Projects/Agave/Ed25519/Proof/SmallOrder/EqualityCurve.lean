import SSA.Projects.Agave.Ed25519.Proof.SmallOrder.PointRepresentation
import SSA.Projects.Agave.Ed25519.Proof.Verifier.ValidPoint

/-! Pure interpretation of canonical product comparisons on valid points. -/
namespace Agave.Ed25519.SmallOrder.Execution.EqualityCurve
open LeanMLIR.RIR Verifier.Execution
open Dalek (ReadOnlyFrame ReadBytes choiceByte)
attribute [local instance] Classical.propDecidable
set_option maxRecDepth 16000
set_option maxHeartbeats 8000000

private theorem serialValue_decode (a : Field.Serial) :
    Field.serialValue a = SerialFieldMul.decode (SerialFieldMul.unsigned a) := by
  unfold Field.serialValue
  rw [← Encoding.value_eq_decode51]
  rfl

theorem bytes_eq_iff_curveValue (a b : Field.Serial) :
    Encoding.machineBytes a = Encoding.machineBytes b ↔ Key.curveValue a = Key.curveValue b := by
  have h := machineBytes_eq_iff a b
  have hp : Encoding.modulus = _root_.p := by decide
  change Encoding.machineBytes a = Encoding.machineBytes b ↔
    (Field.serialValue a : ZMod Encoding.modulus) = (Field.serialValue b : ZMod Encoding.modulus) at h
  rw [hp] at h
  simpa only [serialValue_decode, Key.curveValue] using h

theorem machine_curveValue (a b : Field.Serial)
    (ha : SerialFieldMul.Bounded (SerialFieldMul.unsigned a))
    (hb : SerialFieldMul.Bounded (SerialFieldMul.unsigned b)) :
    Key.curveValue (SerialFieldMul.machine a b) = Key.curveValue a * Key.curveValue b := by
  unfold Key.curveValue
  rw [← Nat.cast_mul]
  apply (ZMod.natCast_eq_natCast_iff' _ _ _).2
  exact SerialFieldMul.machine_correct a b ha hb

def wordsResult (P Q : Key.PointWords) : BitVec 8 :=
  choiceByte (decide (Encoding.machineBytes (SerialFieldMul.machine P.X Q.Z) =
      Encoding.machineBytes (SerialFieldMul.machine Q.X P.Z)) &&
    decide (Encoding.machineBytes (SerialFieldMul.machine P.Y Q.Z) =
      Encoding.machineBytes (SerialFieldMul.machine Q.Y P.Z)))

/-- Nonzero projective scales are supplied by the existing representation invariant. -/
theorem cross_iff (P Q : Key.PointWords) (A B : Bridge.CurvePoint)
    (hP : P.Represents A) (hQ : Q.Represents B) :
    (Key.curveValue P.X * Key.curveValue Q.Z = Key.curveValue Q.X * Key.curveValue P.Z ∧
      Key.curveValue P.Y * Key.curveValue Q.Z = Key.curveValue Q.Y * Key.curveValue P.Z) ↔
      A = B := by
  obtain ⟨pz, px, py, _⟩ := hP
  obtain ⟨qz, qx, qy, _⟩ := hQ
  rw [px, py, qx, qy]
  have hz := mul_ne_zero pz qz
  constructor
  · rintro ⟨hx, hy⟩
    have hx' : A.x = B.x := mul_right_cancel₀ hz (by linear_combination hx)
    have hy' : A.y = B.y := mul_right_cancel₀ hz (by linear_combination hy)
    ext <;> assumption
  · intro h
    subst B
    constructor <;> ring

theorem wordsResult_eq_curve (P Q : ValidPoint) :
    wordsResult P.words Q.words = choiceByte (decide (P.curve = Q.curve)) := by
  classical
  have px := SerialPoint.tight_bounded _ P.tightX
  have py := SerialPoint.tight_bounded _ P.tightY
  have pz := SerialPoint.tight_bounded _ P.tightZ
  have qx := SerialPoint.tight_bounded _ Q.tightX
  have qy := SerialPoint.tight_bounded _ Q.tightY
  have qz := SerialPoint.tight_bounded _ Q.tightZ
  have he : (Encoding.machineBytes (SerialFieldMul.machine P.words.X Q.words.Z) =
        Encoding.machineBytes (SerialFieldMul.machine Q.words.X P.words.Z) ∧
      Encoding.machineBytes (SerialFieldMul.machine P.words.Y Q.words.Z) =
        Encoding.machineBytes (SerialFieldMul.machine Q.words.Y P.words.Z)) ↔ P.curve = Q.curve := by
    rw [bytes_eq_iff_curveValue, bytes_eq_iff_curveValue,
      machine_curveValue _ _ px qz, machine_curveValue _ _ qx pz,
      machine_curveValue _ _ py qz, machine_curveValue _ _ qy pz]
    exact cross_iff _ _ _ _ P.represents Q.represents
  unfold wordsResult
  apply congrArg choiceByte
  apply Bool.eq_iff_iff.mpr
  simpa only [Bool.and_eq_true, decide_eq_true_eq] using he

def identityWords : Key.PointWords :=
  ⟨fun _ => 0, ![1, 0, 0, 0, 0], ![1, 0, 0, 0, 0], fun _ => 0⟩

theorem identityWords_represents : identityWords.Represents 0 := by
  norm_num [identityWords, Key.PointWords.Represents, Key.curveValue,
    SerialFieldMul.decode, SerialFieldMul.unsigned]

def identity : ValidPoint where
  words := identityWords
  curve := 0
  tightX := by intro i; fin_cases i <;> decide
  tightY := by intro i; fin_cases i <;> decide
  tightZ := by intro i; fin_cases i <;> decide
  tightT := by intro i; fin_cases i <;> decide
  represents := identityWords_represents

theorem identity_bytes : identity.bytes = Dalek.identityBytes := by decide +kernel

end Agave.Ed25519.SmallOrder.Execution.EqualityCurve
