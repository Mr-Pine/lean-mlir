import SSA.Projects.Agave.Ed25519.Proof.Verifier.DalekCompressPrimitive
import SSA.Projects.Agave.Ed25519.Proof.Encoding.CompressExecution.LinkedObligations
import SSA.Projects.Agave.Ed25519.Proof.Verifier.ValidPoint
import SSA.Projects.Agave.Ed25519.Proof.SmallOrder.PointRepresentation

/-! The concrete valid-point layout supplies the compressor's projective
interpretation and tight input bounds from the exact bytes in memory. -/
namespace Agave.Ed25519.Verifier.Execution.Dalek
open LeanMLIR.RIR
open SerialFieldMul (readLimbs unsigned)

private theorem compress_wordValue_eq_curveValue (a : Field.Serial) :
    Encoding.Compress.Execution.wordValue a = Key.curveValue a := by
  have h := Encoding.value_eq_decode51 (unsigned a)
  exact (congrArg (fun n : Nat => (n : ZMod _root_.p)) h).symm

/-- Reading the concrete layout recovers all three compressor input arrays,
including their possibly noncanonical representatives. -/
theorem validPoint_compress_input_words (s : GlobalState) (input : Pointer)
    (P : ValidPoint) (h : ReadBytes s input 160 P.bytes) :
    readLimbs s input = P.words.X ∧
    readLimbs s (input.add 40) = P.words.Y ∧
    readLimbs s (input.add 80) = P.words.Z := by
  have hx := SmallOrder.read_coordinate s input P.words h 0
  have hy := SmallOrder.read_coordinate s input P.words h 1
  have hz := SmallOrder.read_coordinate s input P.words h 2
  exact ⟨by simpa [SmallOrder.coordinates] using hx,
    by simpa [SmallOrder.coordinates] using hy,
    by simpa [SmallOrder.coordinates] using hz⟩

/-- The input representation follows from the valid point and exact memory
observation; it does not assume any compressor output. -/
theorem validPoint_compress_projective_input (s : GlobalState) (input : Pointer)
    (P : ValidPoint) (h : ReadBytes s input 160 P.bytes) :
    Encoding.Compress.Execution.ProjectiveInput s input P.curve := by
  obtain ⟨hx, hy, hz⟩ := validPoint_compress_input_words s input P h
  rcases P.represents with ⟨hnz, hX, hY, _⟩
  constructor
  · simpa only [Encoding.Compress.Execution.inputZ, hz,
      compress_wordValue_eq_curveValue] using hnz
  · simpa only [Encoding.Compress.Execution.inputX, Encoding.Compress.Execution.inputZ,
      hx, hz, compress_wordValue_eq_curveValue] using hX
  · simpa only [Encoding.Compress.Execution.inputY, Encoding.Compress.Execution.inputZ,
      hy, hz, compress_wordValue_eq_curveValue] using hY

/-- A represented result supplies tightness for the exact X/Y/Z arrays read
by the linked compressor's lower field operations. -/
theorem validPoint_layout_compress_input_tight (cofactor : ValidPoint → ValidPoint)
    (s : GlobalState) (input : Pointer) (result : Bridge.CurvePoint)
    (encoded : PointBytes) (hread : ReadBytes s input 160 encoded)
    (hresult : (ValidPoint.layout cofactor).result result encoded) :
    SerialPoint.Tight (unsigned (readLimbs s input)) ∧
    SerialPoint.Tight (unsigned (readLimbs s (input.add 40))) ∧
    SerialPoint.Tight (unsigned (readLimbs s (input.add 80))) := by
  obtain ⟨P, _, hbytes⟩ := hresult
  have hread' : ReadBytes s input 160 P.bytes := by simpa only [hbytes] using hread
  obtain ⟨hx, hy, hz⟩ := validPoint_compress_input_words s input P hread'
  rw [hx, hy, hz]
  exact ⟨P.tightX, P.tightY, P.tightZ⟩

/-- Concrete instantiation of the representation premise of
`compressContract_of_primitive_obligations`. -/
theorem validPoint_layout_compress_projective_input (cofactor : ValidPoint → ValidPoint)
    (s : GlobalState) (input : Pointer) (result : Bridge.CurvePoint)
    (encoded : PointBytes) (hread : ReadBytes s input 160 encoded)
    (hresult : (ValidPoint.layout cofactor).result result encoded) :
    Encoding.Compress.Execution.ProjectiveInput s input result := by
  obtain ⟨P, hcurve, hbytes⟩ := hresult
  rw [← hcurve]
  apply validPoint_compress_projective_input s input P
  simpa only [hbytes] using hread

/-- The exact imported compressor satisfies the verifier contract for every
result carried by the concrete valid-point layout. -/
theorem compressContract_linked (cofactor : ValidPoint → ValidPoint) :
    CompressContract Encoding.Compress.Execution.linkedProgram.call
      (ValidPoint.layout cofactor) Bridge.compress := by
  apply compressContract_of_primitive_obligations
    Encoding.Compress.Execution.linkedPrimitives (ValidPoint.layout cofactor) id
  · exact validPoint_layout_compress_projective_input cofactor
  · intro out input s result encoded hwf hout hread hresult _
    obtain ⟨hx, hy, hz⟩ := validPoint_layout_compress_input_tight
      cofactor s input result encoded hread hresult
    exact Encoding.Compress.Execution.linked_primitive_obligations
      out input s hwf hout hread.1 hx hy hz

/-- Public linked leaf endpoint; all arithmetic and execution obligations are
constructed from the concrete imported programs. -/
theorem linked_compress_contract (cofactor : ValidPoint → ValidPoint) :
    CompressContract Encoding.Compress.Execution.linkedProgram.call
      (ValidPoint.layout cofactor) Bridge.compress := compressContract_linked cofactor

end Agave.Ed25519.Verifier.Execution.Dalek
