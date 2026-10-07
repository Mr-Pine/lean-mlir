import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.Globals
import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.Program
import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.SqrtRatioProgram
import SSA.Projects.Agave.Ed25519.Proof.Verifier.DalekDecompressContractUnder

/-! The only fixed-memory prerequisites of the linked decoder are its two
40-byte field constants. They are stated at the invocation, not assumed from
state well-formedness. Output separation is needed only when transporting this
readiness past a write that must preserve the constants. -/
namespace Agave.Ed25519.Encoding.Decompress.Execution
open LeanMLIR.RIR
open Reduce64.Execution (SmallRange)
open Verifier.Execution.Dalek (ReadBytes OutputFrame ReadOnlyFrame)

structure Ready (dg : Decode.Globals) (sg : SqrtRatio.Globals)
    (s : GlobalState) : Prop where
  curveD : ReadBytes s dg.address0 40
    Agave.Ed25519.Encoding.Decompress.Execution.curveD.bytes
  sqrtM1 : ReadBytes s sg.address0 40
    Agave.Ed25519.Encoding.Decompress.Execution.sqrtM1.bytes

/-- Output frames transport initializer readiness when their concrete write
range is disjoint from each initializer. -/
theorem Ready.of_outputFrame (h : Ready dg sg before)
    (frame : OutputFrame before after output bytes)
    (hd : (Range.of dg.address0 320).Disjoint (Range.of output (8 * bytes)))
    (hi : (Range.of sg.address0 320).Disjoint (Range.of output (8 * bytes))) :
    Ready dg sg after :=
  ⟨OutputFrame.readBytes before after output dg.address0 bytes 40 _root_.Agave.Ed25519.Encoding.Decompress.Execution.curveD.bytes frame h.curveD hd,
    OutputFrame.readBytes before after output sg.address0 bytes 40 _root_.Agave.Ed25519.Encoding.Decompress.Execution.sqrtM1.bytes frame h.sqrtM1 hi⟩

theorem Ready.of_readOnlyFrame (h : Ready dg sg before)
    (frame : ReadOnlyFrame before after) : Ready dg sg after :=
  ⟨ReadOnlyFrame.readBytes before after dg.address0 40 _root_.Agave.Ed25519.Encoding.Decompress.Execution.curveD.bytes frame h.curveD,
    ReadOnlyFrame.readBytes before after sg.address0 40 _root_.Agave.Ed25519.Encoding.Decompress.Execution.sqrtM1.bytes frame h.sqrtM1⟩

/-- Fresh caller/callee stack allocation preserves both initialized constants. -/
theorem Ready.alloca (h : Ready dg sg s) (hwf : s.WF) (bytes : Nat) :
    Ready dg sg (s.alloca bytes) := by
  have hlive {p : Pointer} (hp : SmallRange s.mem p 40) :
      SmallRange (s.alloca bytes).mem p 40 := by
    have hne := GlobalState.ne_allocaPtr_of_fits hwf hp.fits
    obtain ⟨b, hb, hs, hz⟩ := hp
    exact ⟨b, (GlobalState.getElem?_alloca hne).trans hb, hs, hz⟩
  constructor
  · exact ⟨hlive h.curveD.1,
      (MemoryState.readAt_alloca hwf h.curveD.1.fits).trans h.curveD.2⟩
  · exact ⟨hlive h.sqrtM1.1,
      (MemoryState.readAt_alloca hwf h.sqrtM1.1.fits).trans h.sqrtM1.2⟩

/-- A scalar/vector store need preserve only the actual constant byte ranges. -/
theorem Ready.storeAt (h : Ready dg sg s) (out : Pointer) (value : BitVec w)
    (hd : (Range.of out w).Disjoint (Range.of dg.address0 320))
    (hi : (Range.of out w).Disjoint (Range.of sg.address0 320)) :
    Ready dg sg {s with mem := s.mem.storeAt out value} := by
  exact ⟨⟨h.curveD.1.storeAt out value,
      (MemoryState.readAt_storeAt_disjoint hd value).trans h.curveD.2⟩,
    ⟨h.sqrtM1.1.storeAt out value,
      (MemoryState.readAt_storeAt_disjoint hi value).trans h.sqrtM1.2⟩⟩

/-- The original initializer-presence facts imply the more local read predicate. -/
theorem Ready.of_present (s : GlobalState) (did iid : BlockId)
    (hd : _root_.Agave.Ed25519.Encoding.Decompress.Execution.curveD.Present did s.mem) (hi : _root_.Agave.Ed25519.Encoding.Decompress.Execution.sqrtM1.Present iid s.mem) :
    Ready ⟨_root_.Agave.Ed25519.Encoding.Decompress.Execution.curveD.address did⟩ ⟨_root_.Agave.Ed25519.Encoding.Decompress.Execution.sqrtM1.address iid⟩ s := by
  constructor
  · refine ⟨⟨⟨_root_.Agave.Ed25519.Encoding.Decompress.Execution.curveD.length, _root_.Agave.Ed25519.Encoding.Decompress.Execution.curveD.bytes⟩, hd, by decide, ?_⟩, hd.readAt⟩
    simp [ByteGlobal.address, _root_.Agave.Ed25519.Encoding.Decompress.Execution.curveD]
  · refine ⟨⟨⟨_root_.Agave.Ed25519.Encoding.Decompress.Execution.sqrtM1.length, _root_.Agave.Ed25519.Encoding.Decompress.Execution.sqrtM1.bytes⟩, hi, by decide, ?_⟩, hi.readAt⟩
    simp [ByteGlobal.address, _root_.Agave.Ed25519.Encoding.Decompress.Execution.sqrtM1]

end Agave.Ed25519.Encoding.Decompress.Execution
