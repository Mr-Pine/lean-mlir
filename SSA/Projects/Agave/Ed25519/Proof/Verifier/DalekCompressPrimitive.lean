import SSA.Projects.Agave.Ed25519.Proof.Encoding.CompressExecution.Values
import SSA.Projects.Agave.Ed25519.Proof.Encoding.CompressExecution.Safety
import SSA.Projects.Agave.Ed25519.Proof.Encoding.CompressExecution.Linked
import SSA.Projects.Agave.Ed25519.Proof.Verifier.DalekExecutionContracts

/-! Adapter from the exact imported point-compression body to the verifier's
primitive interface. The residual bundle below contains only individual field
call equations, their local memory/value results, and the
black-box call. It does not contain compression correctness or its frame.

This is a conditional adapter: constructing the bundle from the concrete
lower helper theorems remains a separate obligation. -/
namespace Agave.Ed25519.Verifier.Execution.Dalek
open LeanMLIR.RIR
open Reduce64.Execution (SmallRange)
set_option maxRecDepth 16384

/-- Explicit remaining facts at the lower-operation boundaries. Every
semantic arithmetic equation is in `FieldValues`; every memory equation is
in `FieldMemory`. No equation describes the complete compressor call. -/
structure CompressPrimitiveObligations (p : Encoding.Compress.Execution.Primitives)
    (initial afterBlack : GlobalState) (input out : Pointer)
    (states : Encoding.Compress.Execution.FieldStates) (words : Encoding.Compress.Execution.FieldResults) : Prop where
  calls : Encoding.Compress.Execution.FieldCalls p initial input states
  memory : Encoding.Compress.Execution.FieldMemory initial afterBlack states words
  values : Encoding.Compress.Execution.FieldValues initial input words
  xOutputLive : SmallRange states.inverted.mem (Encoding.Compress.Execution.scratch initial 5) 40
  outputLive : SmallRange afterBlack.mem out 32
  blackBox : p.blackBoxByte (.cons (.value
    (Encoding.Compress.Execution.inlineParity
      (Encoding.Compress.Execution.affineXWords states.affineXY (Encoding.Compress.Execution.scratch initial 5)))) .nil)
    states.affineXY = .value (.cons (.value
      (Encoding.Compress.Execution.inlineParity
        (Encoding.Compress.Execution.affineXWords states.affineXY (Encoding.Compress.Execution.scratch initial 5)))) .nil,
      afterBlack)

/-- Exact body execution, full stack-frame erasure, canonical serialization,
and sign insertion together establish the verifier-visible result. -/
theorem compress_call_of_primitive_obligations (p : Encoding.Compress.Execution.Primitives)
    (initial afterBlack : GlobalState) (input out : Pointer)
    (states : Encoding.Compress.Execution.FieldStates) (words : Encoding.Compress.Execution.FieldResults)
    (obligations : CompressPrimitiveObligations p initial afterBlack input out states words)
    (P : Bridge.CurvePoint) (hwf : initial.WF)
    (hout : SmallRange initial.mem out 32)
    (hrep : Encoding.Compress.Execution.ProjectiveInput initial input P) :
    ∃ after,
      (Encoding.Compress.Execution.program p).call (args2 out input) initial = .value (.nil, after) ∧
      OutputFrame initial after out 32 ∧
      ReadBytes after out 32 (Bridge.compress P) := by
  let bytes := Encoding.Compress.Execution.encodedBytes
    (Encoding.Compress.Execution.affineXWords states.affineXY (Encoding.Compress.Execution.scratch initial 5))
    (Encoding.Compress.Execution.affineYWords states.affineXY (Encoding.Compress.Execution.scratch initial 5))
  let after : GlobalState :=
    {afterBlack with mem := Encoding.Compress.Execution.storeBytes initial.mem out bytes}
  have hcall := Encoding.Compress.Execution.program_call_of_calls p out input initial afterBlack states
    obligations.calls (Encoding.Compress.Execution.normalizationSafety _ _)
    obligations.outputLive obligations.blackBox
  rw [Encoding.Compress.Execution.storeBytes_erase, obligations.memory.erase hwf] at hcall
  have hbase : ({afterBlack with mem := initial.mem} : GlobalState).WF := by
    intro k hk
    exact lt_of_lt_of_le (hwf k hk) obligations.memory.counter
  have hafter : after.WF := Encoding.Compress.Execution.wf_storeBytes hbase out bytes
  have hbytes (i : Fin 32) : bytes i =
      (Bridge.compress P).extractLsb' (8 * i.val) 8 :=
    Encoding.Compress.Execution.encodedBytes_of_field_calls obligations.memory obligations.values
      obligations.xOutputLive obligations.calls.affineLiveAfterX P hrep i
  refine ⟨after, hcall, ⟨hafter, ?_, ?_⟩, ?_, ?_⟩
  · intro q n hq
    exact Encoding.Compress.Execution.smallRange_storeBytes hq out bytes
  · intro q width hd
    exact Encoding.Compress.Execution.storeBytes_frame initial.mem out q bytes width hout hd
  · exact Encoding.Compress.Execution.smallRange_storeBytes hout out bytes
  · change (Encoding.Compress.Execution.storeBytes initial.mem out bytes).readAt out 256 = _
    have heq : bytes = fun i => (Bridge.compress P).extractLsb' (8 * i.val) 8 :=
      funext hbytes
    rw [heq]
    exact Encoding.Compress.Execution.storeBytes_read initial.mem out (Bridge.compress P) hout

/-- Conditional packaging into the unchanged Dalek interface. The only
universal execution premise supplies the named lower-call obligations above;
the complete compressor call and its 32-byte result are conclusions. Input
layout interpretation is stated separately and cannot be inferred from bytes
being readable alone. -/
theorem compressContract_of_primitive_obligations
    (p : Encoding.Compress.Execution.Primitives) (layout : Layout Point Scalar Result)
    (pointOfResult : Result → Bridge.CurvePoint)
    (hrepresentation : ∀ (state : GlobalState) (input : Pointer)
      (result : Result) (encoded : PointBytes),
      ReadBytes state input 160 encoded → layout.result result encoded →
      Encoding.Compress.Execution.ProjectiveInput state input (pointOfResult result))
    (hprimitive : ∀ (out input : Pointer) (state : GlobalState)
      (result : Result) (encoded : PointBytes), state.WF →
      SmallRange state.mem out 32 → ReadBytes state input 160 encoded →
      layout.result result encoded →
      (Range.of out 256).Disjoint (Range.of input 1280) →
      ∃ states afterBlack words,
        CompressPrimitiveObligations p state afterBlack input out states words) :
    CompressContract (Encoding.Compress.Execution.program p).call layout
      (fun result => Bridge.compress (pointOfResult result)) := by
  intro out input state result encoded hwf hout hin hrep hd
  obtain ⟨states, afterBlack, words, obligations⟩ :=
    hprimitive out input state result encoded hwf hout hin hrep hd
  exact compress_call_of_primitive_obligations p state afterBlack input out states words
    obligations (pointOfResult result) hwf hout
    (hrepresentation state input result encoded hin hrep)

end Agave.Ed25519.Verifier.Execution.Dalek
