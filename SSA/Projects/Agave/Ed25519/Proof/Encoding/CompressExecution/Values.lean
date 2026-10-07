import SSA.Projects.Agave.Ed25519.Proof.Encoding.CompressExecution.Frame

/-! The semantic chain of the five field calls, independently of their
instruction execution. Each residual equation names a single field operation.
The inverse and compression conclusions are proved from those equations. -/
namespace Agave.Ed25519.Encoding.Compress.Execution
open LeanMLIR.RIR
open Reduce64.Execution (SmallRange)
open SerialFieldMul (readLimbs)

def wordValue (v : Field.Serial) : K := Field.serialValue v

def inputX (s : GlobalState) (input : Pointer) : K := wordValue (readLimbs s input)
def inputY (s : GlobalState) (input : Pointer) : K := wordValue (readLimbs s (input.add 40))
def inputZ (s : GlobalState) (input : Pointer) : K := wordValue (readLimbs s (input.add 80))

/-- The actual X/Y/Z slots represent the specified affine curve point. This
is an input representation assertion, not a compression result. -/
structure ProjectiveInput (s : GlobalState) (input : Pointer) (P : Bridge.CurvePoint) : Prop where
  nonzero : inputZ s input ≠ 0
  x : inputX s input = P.x * inputZ s input
  y : inputY s input = P.y * inputZ s input

/-- Per-operation value obligations after transporting the inputs through
the two explicit copies and preceding lower-call frames. `pow22501` is the
only two-result operation; there is no assumed field-inversion equation. -/
structure FieldValues (initial : GlobalState) (input : Pointer)
    (words : FieldResults) : Prop where
  pow22501First : wordValue words.powFirst = (Decompress.pow22501 (inputZ initial input)).1
  pow22501Second : wordValue words.powSecond = (Decompress.pow22501 (inputZ initial input)).2
  pow2k : wordValue words.squared = wordValue words.powFirst ^ (2 ^ 5)
  inverseMul : wordValue words.inverse = wordValue words.squared * wordValue words.powSecond
  xMul : wordValue words.affineX = inputX initial input * wordValue words.inverse
  yMul : wordValue words.affineY = inputY initial input * wordValue words.inverse

theorem FieldValues.inverse_value (h : FieldValues initial input words) :
    wordValue words.inverse = invertChain (inputZ initial input) := by
  rw [h.inverseMul, h.pow2k, h.pow22501First, h.pow22501Second]
  rfl

theorem FieldValues.affine_value (h : FieldValues initial input words)
    (P : Bridge.CurvePoint) (hp : ProjectiveInput initial input P) :
    wordValue words.affineX = P.x ∧ wordValue words.affineY = P.y := by
  rw [h.xMul, h.yMul, h.inverse_value]
  exact affine_products _ _ _ P hp.nonzero hp.x hp.y

theorem affineXWords_eq_readLimbs (s : GlobalState) (p : Pointer) :
    affineXWords s p = readLimbs s p := rfl

theorem affineYWords_eq_readLimbs (s : GlobalState) (p : Pointer) :
    affineYWords s p = readLimbs s (p.add 40) := by
  funext i
  fin_cases i <;> simp [affineYWords, readLimbs, Pointer.add, BitVec.add_assoc]

/-- The X and Y stores occupy disjoint halves of the same 80-byte temporary.
The final Y multiplication therefore preserves the preceding X result. -/
theorem FieldMemory.affine_readback
    (mem : FieldMemory initial afterBlack states words)
    (hx : SmallRange states.inverted.mem (scratch initial 5) 40)
    (hxy : SmallRange states.affineX.mem (scratch initial 5) 80) :
    affineXWords states.affineXY (scratch initial 5) = words.affineX ∧
    affineYWords states.affineXY (scratch initial 5) = words.affineY := by
  let temp := scratch initial 5
  have hx' : SmallRange states.affineX.mem temp 40 := by
    simpa only [Pointer.add_zero] using
      SerialPoint.Execution.smallRange_add hxy (k := 0) (count := 40) (by decide)
  have hy' : SmallRange states.affineX.mem (temp.add 40) 40 :=
    SerialPoint.Execution.smallRange_add hxy (k := 40) (count := 40) (by decide)
  have hoff : (temp.add 40#64).offsetInBits = temp.offsetInBits + 320 := by
    simpa using Pointer.offsetInBits_add (hxy.no_wrap (k := 40) (by decide))
  have hd : (Range.of temp 320).Disjoint (Range.of (temp.add 40) 320) := by
    simp only [BitVec.ofNat_eq_ofNat, Range.Disjoint, Range.of, Pointer.add_id, hoff]
    exact Or.inr (Or.inl (by norm_num))
  have hpres := SerialPoint.Execution.readLimbs_storeLimbs_frame states.affineX
    (temp.add 40) temp words.affineY hy' hx' hd
  have hreadX := SerialPoint.Execution.readLimbs_storeLimbs states.inverted temp
    words.affineX hx
  have hreadY := SerialPoint.Execution.readLimbs_storeLimbs states.affineX (temp.add 40)
    words.affineY hy'
  rw [affineXWords_eq_readLimbs, affineYWords_eq_readLimbs]
  constructor
  · calc
      readLimbs states.affineXY temp = readLimbs states.affineX temp := by
        funext i
        simpa only [readLimbs, temp, mem.yMul] using congrFun hpres i
      _ = words.affineX := by
        funext i
        simpa only [readLimbs, temp, mem.xMul] using congrFun hreadX i
  · funext i
    simpa only [readLimbs, temp, mem.yMul] using congrFun hreadY i

/-- Combining the lower arithmetic equations with actual store readback
identifies every emitted output byte with the existing compression spec. -/
theorem encodedBytes_of_field_calls (mem : FieldMemory initial afterBlack states words)
    (values : FieldValues initial input words)
    (hx : SmallRange states.inverted.mem (scratch initial 5) 40)
    (hxy : SmallRange states.affineX.mem (scratch initial 5) 80)
    (P : Bridge.CurvePoint) (hp : ProjectiveInput initial input P) (i : Fin 32) :
    encodedBytes (affineXWords states.affineXY (scratch initial 5))
      (affineYWords states.affineXY (scratch initial 5)) i =
      (Bridge.compress P).extractLsb' (8 * i.val) 8 := by
  obtain ⟨hxr, hyr⟩ := mem.affine_readback hx hxy
  obtain ⟨hxv, hyv⟩ := values.affine_value P hp
  rw [hxr, hyr]
  exact encodedBytes_eq_compress _ _ P hxv hyv i

end Agave.Ed25519.Encoding.Compress.Execution
