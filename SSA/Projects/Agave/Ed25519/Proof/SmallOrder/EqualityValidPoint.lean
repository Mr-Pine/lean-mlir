import SSA.Projects.Agave.Ed25519.Proof.SmallOrder.EqualityResult
import SSA.Projects.Agave.Ed25519.Proof.SmallOrder.EqualityCurve

/-! The exact equality call compares represented curve points. Its small-order
specialization leaves only the cofactor operation's group interpretation as an
explicit premise; no equality-execution or byte-comparison contract is assumed. -/
namespace Agave.Ed25519.SmallOrder.Execution.EqualityValidPoint
open LeanMLIR.RIR Verifier.Execution
open Dalek (ReadOnlyFrame ReadBytes choiceByte)
open EqualityResult EqualityCurve
attribute [local instance] Classical.propDecidable
set_option maxRecDepth 16000
set_option maxHeartbeats 8000000

theorem raw_eq_words (s : GlobalState) (l r : Pointer) (P Q : Key.PointWords)
    (hl : ReadBytes s l 160 P.bytes) (hr : ReadBytes s r 160 Q.bytes) :
    rawResult s l r = wordsResult P Q := by
  have lx := read_coordinate s l P hl 0
  have ly := read_coordinate s l P hl 1
  have lz := read_coordinate s l P hl 2
  have rx := read_coordinate s r Q hr 0
  have ry := read_coordinate s r Q hr 1
  have rz := read_coordinate s r Q hr 2
  change SerialFieldMul.readLimbs s (l.add 0#64) = P.X at lx
  change SerialFieldMul.readLimbs s (l.add 40#64) = P.Y at ly
  change SerialFieldMul.readLimbs s (l.add 80#64) = P.Z at lz
  change SerialFieldMul.readLimbs s (r.add 0#64) = Q.X at rx
  change SerialFieldMul.readLimbs s (r.add 40#64) = Q.Y at ry
  change SerialFieldMul.readLimbs s (r.add 80#64) = Q.Z at rz
  simp only [Pointer.add_zero] at lx rx
  simp only [rawResult, wordsResult, lx, ly, lz, rx, ry, rz]

/-- The imported equality function is mathematical point equality on valid
machine representatives, including distinct noncanonical limb payloads. -/
theorem call_valid (s : GlobalState) (l r : Pointer) (P Q : ValidPoint)
    (hwf : s.WF) (hl : ReadBytes s l 160 P.bytes) (hr : ReadBytes s r 160 Q.bytes) :
    ∃ t, equalityProgram.call (Dalek.args2 l r) s =
      .value (.cons (.value (choiceByte (decide (P.curve = Q.curve)))) .nil, t) ∧
      ReadOnlyFrame s t := by
  classical
  have h := call_raw s l r hwf hl.1 hr.1
  rw [raw_eq_words s l r P.words Q.words hl hr, wordsResult_eq_curve] at h
  exact h

/-- Close the verifier equality leaf. The remaining premise identifies the
separately verified cofactor representative with mathematical multiplication by 8. -/
theorem smallOrder_contract (decode : Verifier.Bytes32 → Option ValidPoint)
    (timesEight : ValidPoint → ValidPoint)
    (hEight : ∀ P, (timesEight P).curve = 8 • P.curve) :
    Dalek.SmallOrderEqContract equalityProgram.call (ValidPoint.layout timesEight)
      (ValidPoint.shared decode) := by
  classical
  intro point ident state value hwf hp hi
  have hi' : ReadBytes state ident 160 identity.bytes := by
    simpa only [identity_bytes, ValidPoint.layout] using hi
  obtain ⟨after, hc, hf⟩ := call_valid state point ident (timesEight value) identity hwf hp hi'
  refine ⟨after, ?_, hf⟩
  have hres : choiceByte (decide ((timesEight value).curve = identity.curve)) =
      (if (ValidPoint.shared decode).smallOrder value then (1 : BitVec 8) else 0) := by
    simp only [identity, ValidPoint.shared, choiceByte, hEight]
    rfl
  rw [hres] at hc
  exact hc

end Agave.Ed25519.SmallOrder.Execution.EqualityValidPoint
