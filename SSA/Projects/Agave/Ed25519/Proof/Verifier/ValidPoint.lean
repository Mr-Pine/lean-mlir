import SSA.Projects.Agave.Ed25519.Proof.Verifier.KeyPayloadLayout
import SSA.Projects.Agave.Ed25519.Proof.Verifier.CanonicalScalar

/-!
Valid machine representatives retain exact, potentially noncanonical limb
bytes, their arithmetic bounds, and a proved curve interpretation. No operation
in the final interface quantifies over arbitrary 64-bit point arrays.
-/
namespace Agave.Ed25519.Verifier.Execution

/-- A successful decoder/result value, including the invariants required by
the serial arithmetic lemmas. Different words may represent the same point. -/
structure ValidPoint where
  words : Key.PointWords
  curve : Bridge.CurvePoint
  tightX : SerialPoint.Tight (SerialFieldMul.unsigned words.X)
  tightY : SerialPoint.Tight (SerialFieldMul.unsigned words.Y)
  tightZ : SerialPoint.Tight (SerialFieldMul.unsigned words.Z)
  tightT : SerialPoint.Tight (SerialFieldMul.unsigned words.T)
  represents : words.Represents curve

namespace ValidPoint
attribute [local instance] Classical.propDecidable

def bytes (P : ValidPoint) : Dalek.PointBytes := P.words.bytes

/-- Exact constructor negation preserves valid representation and limb bounds.
The curve field is definitionally the group inverse. -/
def negate (P : ValidPoint) : ValidPoint where
  words := P.words.negate
  curve := -P.curve
  tightX := Key.negResult_tight P.words.X
  tightY := P.tightY
  tightZ := P.tightZ
  tightT := Key.negResult_tight P.words.T
  represents := Key.PointWords.negate_represents P.words P.curve P.represents
    (SerialPoint.tight_bounded _ P.tightX) (SerialPoint.tight_bounded _ P.tightT)

@[simp] theorem negate_curve (P : ValidPoint) : P.negate.curve = -P.curve := rfl

@[simp] theorem negate_words (P : ValidPoint) : P.negate.words = P.words.negate := rfl

/-- Both backend outputs must supply a valid representative; equality of
projective coordinates or of serial/AVX result bytes is not required. -/
def ResultRepresents (A : Bridge.CurvePoint) (encoded : Dalek.PointBytes) : Prop :=
  ∃ P : ValidPoint, P.curve = A ∧ P.bytes = encoded

/-- A cofactor schedule returning this type preserves all coordinate and
arithmetic invariants. Its output bytes remain an ordinary exact ABI value. -/
def layout (cofactor : ValidPoint → ValidPoint) :
    Dalek.Layout ValidPoint CanonicalScalar Bridge.CurvePoint where
  point := bytes
  cofactor := fun P => (cofactor P).bytes
  result := ResultRepresents
  scalar := CanonicalScalar.encode
  identity := Dalek.identityBytes
  reduce := Dalek.reduceScalarBytes

noncomputable def shared (decode : Bytes32 → Option ValidPoint) : Shared ValidPoint CanonicalScalar where
  decompress := decode
  negate := negate
  smallOrder := fun P => @decide ((8 : Nat) • P.curve = 0) (Classical.propDecidable _)
  parseScalar := CanonicalScalar.parse

/-- Only successful decoder values are required to carry bounds and valid
extended coordinates; malformed bytes retain the `none` branch. -/
structure DecoderCorrect (decode : Bytes32 → Option ValidPoint) : Prop where
  sound : ∀ bytes P, decode bytes = some P → Bridge.Encodes bytes P.curve
  complete : ∀ bytes A, Bridge.Encodes bytes A →
    ∃ P, decode bytes = some P ∧ P.curve = A

theorem shared_correct (decode : Bytes32 → Option ValidPoint) (h : DecoderCorrect decode) :
    RepresentedSharedCorrect (shared decode) ValidPoint.curve Fin.val := by
  refine ⟨h.sound, h.complete, fun _ => rfl, ?_,
    CanonicalScalar.parse_eq_some_iff, CanonicalScalar.complete⟩
  intro P
  change decide ((8 : Nat) • P.curve = 0) = false ↔ _
  simp

theorem parser_contracts (decode : Bytes32 → Option ValidPoint)
    (cofactor : ValidPoint → ValidPoint) :
    Dalek.ScalarParseContract (layout cofactor) (shared decode) ∧
      Dalek.ScalarParseComplete (layout cofactor) (shared decode) :=
  CanonicalScalar.parserContracts (layout cofactor) (shared decode)

/-- Machine double-base refinement now targets the actual group operation,
with valid inputs supplied by the type and valid output bytes by the layout. -/
def doubleBase (h : CanonicalScalar) (minusA : ValidPoint) (s : CanonicalScalar) :
    Bridge.CurvePoint := h.val • minusA.curve + s.val • Bridge.base

end ValidPoint
end Agave.Ed25519.Verifier.Execution
