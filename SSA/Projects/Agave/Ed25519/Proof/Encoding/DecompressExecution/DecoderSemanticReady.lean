import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.SqrtRatioInlineComposeClosed
import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.DecoderSqrtCallerFrames

/-! The linked compressed-point decoder is correct under only its initialized
constant bytes and ordinary live-buffer prerequisites. Every finite-prefix
witness is supplied by exact execution of the original RIR instructions. -/
namespace Agave.Ed25519.Encoding.Decompress.Execution.Decode.ReadySemantic
open LeanMLIR.RIR
open Reduce64.Execution (SmallRange)
open Verifier.Execution (ValidPoint)
open Verifier.Execution.Dalek (ReadBytes OutputFrame args2)
set_option maxRecDepth 32000
set_option maxHeartbeats 2000000

theorem sqrtPrefixProvider (sg : SqrtRatio.Globals) : SqrtPrefixBridge.PrefixProvider sg :=
  SqrtRatio.Inline.prefixWitness_of_ready sg

theorem prefixBoundary_of_ready (dg : Globals) (sg : SqrtRatio.Globals)
    (s : GlobalState) (out input : Pointer) (bytes : BitVec 256)
    (hwf : s.WF) (hin : ReadBytes s input 32 bytes) (hout : SmallRange s.mem out 168)
    (ready : Ready dg sg s) : Semantic.PrefixBoundary dg sg out input s bytes :=
  SqrtPrefixBridge.prefixBoundary_of_provider dg sg (sqrtPrefixProvider sg)
    s out input bytes hwf hin hout ready

/-- Actual rejection and success, including ValidPoint's four-coordinate payload. -/
theorem linked_call_valid (dg : Globals) (sg : SqrtRatio.Globals)
    (out input : Pointer) (s : GlobalState) (bytes : BitVec 256)
    (hwf : s.WF) (hin : ReadBytes s input 32 bytes) (hout : SmallRange s.mem out 168)
    (ready : Ready dg sg s) :
    ∃ after, (linkedProgram dg sg).call (args2 out input) s = .value (.nil,after) ∧
      OutputFrame s after out 168 ∧
      (Valid.decode bytes).elim (after.mem.readAt out 64 = 0)
        (fun point => after.mem.readAt out 64 = 1 ∧
          ReadBytes after (out.add 8#64) 160 point.bytes) :=
  Semantic.linked_call_valid dg sg out input s bytes hwf hout
    (prefixBoundary_of_ready dg sg s out input bytes hwf hin hout ready)

theorem linked_call_classification (dg : Globals) (sg : SqrtRatio.Globals)
    (out input : Pointer) (s : GlobalState) (bytes : BitVec 256)
    (hwf : s.WF) (hin : ReadBytes s input 32 bytes) (hout : SmallRange s.mem out 168)
    (ready : Ready dg sg s) :
    ∃ after, (linkedProgram dg sg).call (args2 out input) s = .value (.nil,after) ∧
      OutputFrame s after out 168 ∧
      (after.mem.readAt out 64 = 0 ↔ ¬∃ A, Bridge.Encodes bytes A) ∧
      (after.mem.readAt out 64 = 1 ↔ ∃ A, Bridge.Encodes bytes A) :=
  Semantic.linked_call_classification dg sg out input s bytes hwf hout
    (prefixBoundary_of_ready dg sg s out input bytes hwf hin hout ready)

/-- The verifier-facing decoder contract has no residual execution or result premise. -/
theorem contractUnder (dg : Globals) (sg : SqrtRatio.Globals)
    (cofactor : ValidPoint → ValidPoint) :
    Verifier.Execution.Dalek.DecompressContractUnder (Ready dg sg) (linkedProgram dg sg).call
      (ValidPoint.layout cofactor) (ValidPoint.shared Valid.decode) :=
  SqrtPrefixBridge.contractUnder_of_provider dg sg cofactor (sqrtPrefixProvider sg)

theorem call_allocation (dg : Globals) (sg : SqrtRatio.Globals)
    (out input : Pointer) (entry after : GlobalState) (bytes : BitVec 256)
    (hwf : entry.WF) (hin : ReadBytes entry input 32 bytes)
    (hout : SmallRange entry.mem out 168) (ready : Ready dg sg entry)
    (hcall : (linkedProgram dg sg).call (args2 out input) entry = .value (.nil,after))
    (id : BlockId) (hi : id ≠ out.id) : after.mem[id]? = entry.mem[id]? :=
  SqrtPrefixBridge.call_allocation_of_prefix dg sg out input entry after bytes
    (prefixBoundary_of_ready dg sg entry out input bytes hwf hin hout ready) hcall id hi

theorem call_shape (dg : Globals) (sg : SqrtRatio.Globals)
    (out input : Pointer) (entry after : GlobalState) (bytes : BitVec 256)
    (hwf : entry.WF) (hin : ReadBytes entry input 32 bytes)
    (hout : SmallRange entry.mem out 168) (ready : Ready dg sg entry)
    (hcall : (linkedProgram dg sg).call (args2 out input) entry = .value (.nil,after))
    (id : BlockId) : (after.mem[id]?).map MemoryBlock.length =
      (entry.mem[id]?).map MemoryBlock.length :=
  SqrtPrefixBridge.call_shape_of_prefix dg sg out input entry after bytes
    (prefixBoundary_of_ready dg sg entry out input bytes hwf hin hout ready) hcall id

theorem call_callerBlocks (dg : Globals) (sg : SqrtRatio.Globals)
    (out input : Pointer) (entry after : GlobalState) (bytes : BitVec 256)
    (hwf : entry.WF) (hin : ReadBytes entry input 32 bytes)
    (hout : SmallRange entry.mem out 168) (ready : Ready dg sg entry)
    (hcall : (linkedProgram dg sg).call (args2 out input) entry = .value (.nil,after))
    (mark : Nat) (hmark : mark ≤ out.id.id) :
    ∀ id : BlockId, id.id < mark → after.mem[id]? = entry.mem[id]? :=
  SqrtPrefixBridge.call_callerBlocks_of_prefix dg sg out input entry after bytes
    (prefixBoundary_of_ready dg sg entry out input bytes hwf hin hout ready) hcall mark hmark

end Agave.Ed25519.Encoding.Decompress.Execution.Decode.ReadySemantic
