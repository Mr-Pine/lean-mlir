import SSA.Projects.Agave.Ed25519.Proof.Encoding.CompressExecution.Lower
import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.Pow22501Execution
import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.LimbMemoryExact

/-! Concrete refinement of the imported two-result addition-chain helper. -/
namespace Agave.Ed25519.Encoding.Compress.Execution
open LeanMLIR.RIR
open Reduce64.Execution (SmallRange)
open SerialFieldMul (readLimbs storeLimbs unsigned)
open SerialPoint.Execution

theorem linked_pow22501_contract :
    Pow22501PrimitiveContract linkedPrimitives.pow22501 := by
  intro out input s hwf hout hin htight
  obtain ⟨hcall, hvalue, hfirst, hsecond⟩ :=
    Decompress.Execution.Pow22501.program_call_field out input s hwf hout hin htight
  let first := (Decompress.Execution.Pow22501.rawWordChain (readLimbs s input)).1
  let second := (Decompress.Execution.Pow22501.rawWordChain (readLimbs s input)).2
  have hout2 : SmallRange s.mem (out.add 40) 40 :=
    smallRange_add hout (k := 40) (count := 40) (by decide)
  have hexact := Decompress.Execution.storeLimbs_exact
    (storeLimbs s.mem out first) (out.add 40) second
    (smallRange_storeLimbs hout2 out first)
  refine ⟨Decompress.Execution.Pow22501.resultState s out (readLimbs s input),
    first, second, hcall, hexact.symm, ?_, ?_, ?_, ?_, hfirst, hsecond⟩
  · have hstore : ({s with mem := (storeLimbs s.mem out first).storeAt (out.add 40) (Decompress.Execution.limbBytes second)} : GlobalState).WF :=
      (wf_storeLimbs hwf out first).storeAt
    exact hstore.add_blocks
  · change s.alloc.nextFreeBlock ≤ s.alloc.nextFreeBlock + 20
    omega
  · have h := congrArg Prod.fst hvalue
    simpa only [Decompress.Execution.wordValue_eq_serialValue, wordValue] using h
  · have h := congrArg Prod.snd hvalue
    simpa only [Decompress.Execution.wordValue_eq_serialValue, wordValue] using h

end Agave.Ed25519.Encoding.Compress.Execution
