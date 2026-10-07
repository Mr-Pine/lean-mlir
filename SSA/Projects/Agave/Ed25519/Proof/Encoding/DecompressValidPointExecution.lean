import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressValidPoint
import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressValidPointFrames
import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.ParseInput
import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.ReadyValues

/-! The checked final decoder instructions produce the concrete `ValidPoint`
payload. A separate final adapter translates exact word observations into the
verifier leaf interface. Its execution premise remains explicit: the full
sqrt and outer decoder CFG composition is not supplied by this module. -/
namespace Agave.Ed25519.Encoding.Decompress.Valid
open LeanMLIR.RIR
open Verifier
open Verifier.Execution
open Reduce64.Execution (SmallRange)
open Execution

set_option maxRecDepth 8192
attribute [local irreducible] step1 Decode.wordStep1 decode Decode.wordDecode

/-- The actual input load/mask/store slice keeps exactly the Y limbs carried
by the successful valid point, including unreduced encodings. -/
theorem parsed_validY (s : GlobalState) (input dst : Pointer) (bytes : Bytes32)
    (hvalid : (step1 bytes).1 = true)
    (hi : SmallRange s.mem input 32) (hd : SmallRange s.mem dst 40)
    (hbytes : s.mem.readAt input 256 = bytes) :
    Dalek.ReadBytes
      {s with mem := SerialFieldMul.storeLimbs s.mem dst (inputWords s input)} dst 40
      (Key.coordinatePayload (point bytes hvalid).words.Y) := by
  rw [coordinatePayload_eq]
  exact Decode.parsed_readback s input dst bytes hi hd hbytes

/-- Invocation-local initialized globals provide precisely the constant word
arrays used by the bounded decoder/square-root schedules. -/
theorem ready_constant_words (dg : Decode.Globals) (sg : SqrtRatio.Globals)
    (s : GlobalState) (h : Ready dg sg s) :
    SerialFieldMul.readLimbs s dg.address0 = Decode.curveDWord.limbs ∧
      SerialFieldMul.readLimbs s sg.address0 = SqrtRatio.sqrtM1Word.limbs :=
  ⟨h.curveD_read, h.sqrtM1_read⟩

attribute [local irreducible] Decode.pointWords

private theorem pointWords_Z (bytes : Bytes32) :
    Decode.fieldPayload (Decode.pointWords bytes (Decode.wordStep1 bytes).2).Z.limbs =
      1#320 := by
  simp only [Decode.pointWords]
  set_option exponentiation.threshold 512 in decide

/-- Once X and T have been computed, the actual Y/Z stores and output memcpy
produce the valid point's exact bytes, without a canonical-representation
assumption or an independent payload equality premise. -/
theorem finishPoint_run (p : Decode.Primitives) (g : Decode.Globals)
    (E : ⟪Decode.program.Γ⟫) (s : GlobalState) (out scratch yptr : Pointer)
    (bytes : Bytes32) (hvalid : (step1 bytes).1 = true)
    (hout : E.read (%arg0) = .value out)
    (hpoint : E.read (%36) = .value scratch) (hy : E.read (%38) = .value yptr)
    (h40 : E.read (%19) = .value 40#64) (h80 : E.read (%27) = .value 80#64)
    (h88 : E.read (%28) = .value 88#64) (hone : E.read (%6) = .value 1#64)
    (hzero : E.read (%20) = .value 0#8) (h32 : E.read (%10) = .value 32#64)
    (h8 : E.read (%8) = .value 8#64) (h160 : E.read (%29) = .value 160#64)
    (hp : SmallRange s.mem scratch 160) (hyLive : SmallRange s.mem yptr 40)
    (ho : SmallRange s.mem out 168)
    (hdY : (Range.of (scratch.add 40#64) 320).Disjoint (Range.of yptr 320))
    (hdOut : (Range.of (out.add 8#64) 1280).Disjoint (Range.of scratch 1280))
    (hX : s.mem.readAt scratch 320 = Decode.fieldPayload
      (Decode.pointWords bytes (Decode.wordStep1 bytes).2).X.limbs)
    (hY : s.mem.readAt yptr 320 = Decode.fieldPayload
      (Decode.pointWords bytes (Decode.wordStep1 bytes).2).Y.limbs)
    (hT : s.mem.readAt (scratch.add 120#64) 320 = Decode.fieldPayload
      (Decode.pointWords bytes (Decode.wordStep1 bytes).2).T.limbs) :
    Decode.resume p g 1 50 E s = .value (.nil,
      Decode.successState (Decode.finishPointState s scratch yptr) out
        (point bytes hvalid).bytes) := by
  have hcoordinates := Decode.finishPointState_coordinates s scratch yptr _ _ _ hp hX hY hT
  have hread := Decode.finishPointState_read s scratch yptr hp
  have hbits := hread.2.symm.trans hcoordinates.2
  have hpayload : Decode.finishPointBits (s.mem.readAt scratch 1280)
      (s.mem.readAt yptr 320) = (point bytes hvalid).bytes := by
    rw [hbits, point_bytes, Decode.pointPayload, pointWords_Z]
  rw [← hpayload]
  exact Decode.finishPoint_run p g E s out scratch yptr hout hpoint hy
    h40 h80 h88 hone hzero h32 h8 h160 hp hyLive ho hdY hdOut

/-- The suffix's caller-visible tag and exact payload are established by
the concrete stores, including when X is zero or Y was noncanonical. -/
theorem finishPoint_observation (s : GlobalState) (out scratch yptr : Pointer)
    (bytes : Bytes32) (hvalid : (step1 bytes).1 = true)
    (ho : SmallRange s.mem out 168) :
    let after := Decode.successState (Decode.finishPointState s scratch yptr)
      out (point bytes hvalid).bytes
    after.mem.readAt out 64 = 1#64 ∧
      Dalek.ReadBytes after (out.add 8#64) 160 (point bytes hvalid).bytes := by
  exact ⟨Decode.successState_tag (Decode.finishPointState_live ho scratch yptr) _,
    Decode.successState_payload (Decode.finishPointState_live ho scratch yptr) _⟩

/-- The exact word result fixes both tag and raw payload. This predicate
contains no curve interpretation or user-selected layout. -/
def WordObservation (bytes : Bytes32) (after : GlobalState) (out : Pointer) : Prop :=
  (Decode.wordDecode bytes).elim (after.mem.readAt out 64 = 0)
    (fun P => after.mem.readAt out 64 = 1 ∧
      Dalek.ReadBytes after (out.add 8) 160 (Decode.pointPayload P))

private def PayloadObservation (payload : Option (BitVec 1280))
    (after : GlobalState) (out : Pointer) : Prop :=
  payload.elim (after.mem.readAt out 64 = 0)
    (fun bytes => after.mem.readAt out 64 = 1 ∧
      Dalek.ReadBytes after (out.add 8) 160 bytes)

private theorem payloadObservation_map {α : Type} (value : Option α)
    (pack : α → BitVec 1280) (after : GlobalState) (out : Pointer) :
    PayloadObservation (value.map pack) after out =
      value.elim (after.mem.readAt out 64 = 0)
        (fun point => after.mem.readAt out 64 = 1 ∧
          Dalek.ReadBytes after (out.add 8) 160 (pack point)) := by
  cases value <;> rfl

theorem wordObservation_iff (bytes : Bytes32) (after : GlobalState) (out : Pointer) :
    WordObservation bytes after out ↔
      (decode bytes).elim (after.mem.readAt out 64 = 0)
        (fun P => after.mem.readAt out 64 = 1 ∧
          Dalek.ReadBytes after (out.add 8) 160 P.bytes) := by
  have h := congrArg (fun payload => PayloadObservation payload after out) (decode_bytes bytes)
  rw [payloadObservation_map, payloadObservation_map] at h
  unfold WordObservation
  exact Iff.of_eq h.symm

/-- Generic packaging only. The sole substantive premise is the actual
machine call with its exact word result and caller frame. It is intentionally
not asserted for `linkedProgram`: its remaining instruction proofs must still
construct this premise. No decoder correctness or representation premise is
left for the caller to supply. -/
theorem contractUnder_of_word_execution
    (ready : GlobalState → Prop) (call : Vals [.ptr, .ptr] → EffectM (Vals []))
    (cofactor : ValidPoint → ValidPoint)
    (hrun : ∀ (out input : Pointer) (state : GlobalState) (encoded : Bytes32),
      state.WF → ready state → SmallRange state.mem out 168 →
      Dalek.ReadBytes state input 32 encoded →
      (Range.of out 1344).Disjoint (Range.of input 256) →
      ∃ after, call (Dalek.args2 out input) state = .value (.nil, after) ∧
        Dalek.OutputFrame state after out 168 ∧ WordObservation encoded after out) :
    Dalek.DecompressContractUnder ready call (ValidPoint.layout cofactor)
      (ValidPoint.shared decode) := by
  intro out input state encoded hwf hready hout hin hd
  obtain ⟨after, hcall, hframe, hwords⟩ := hrun out input state encoded hwf hready hout hin hd
  refine ⟨after, hcall, hframe, ?_⟩
  have h := (wordObservation_iff encoded after out).mp hwords
  simp only [ValidPoint.shared, ValidPoint.layout]
  generalize heq : decode encoded = decoded at h ⊢
  cases decoded <;> exact h

end Agave.Ed25519.Encoding.Decompress.Valid
