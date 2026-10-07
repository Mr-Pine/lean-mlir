import SSA.Projects.Agave.Ed25519.Proof.Verifier.DalekExecutionContextual
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Execution.ColdChallengeCall
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Execution.ColdCallerFrame

/-! The mutable SHA dispatch byte is a distinct global allocation. All
readiness is local to this verifier invocation, before its stack allocation. -/
namespace Agave.Ed25519.Verifier.Execution.Dalek
open LeanMLIR.RIR
open SHA512Finalization (CompressionGlobals CompressionReady)

structure ColdEntryReady (cg : CompressionGlobals) (rg : ScalarWide.Globals)
    (dg : Globals) (ddg : Encoding.Decompress.Execution.Decode.Globals)
    (dsg : Encoding.Decompress.Execution.SqrtRatio.Globals)
    (initial : GlobalState) (key signature message : Pointer) : Prop where
  compression : CompressionReady cg initial
  reduction : ScalarWide.Ready rg (allocated initial) (stackSlot initial 12)
  keyCache : key.id ≠ cg.cache
  signatureCache : signature.id ≠ cg.cache
  messageCache : message.id ≠ cg.cache
  reduceRCache : rg.address0.id ≠ cg.cache
  reduceRRCache : rg.address1.id ≠ cg.cache
  identityCache : dg.address0.id ≠ cg.cache
  dalekCache : dg.address1.id ≠ cg.cache
  curveDCache : ddg.address0.id ≠ cg.cache
  sqrtM1Cache : dsg.address0.id ≠ cg.cache

theorem compressionReady_stackState (cg : CompressionGlobals) (initial : GlobalState)
    (h : CompressionReady cg initial) (hwf : initial.WF) (n : Nat) :
    CompressionReady cg (stackState initial n) := by
  induction n with
  | zero => exact h
  | succ n ih => exact CompressionReady.alloca cg _ _ ih (stackState_wf initial hwf n)

variable {cg : CompressionGlobals} {rg : ScalarWide.Globals} {dg : Globals}
  {ddg : Encoding.Decompress.Execution.Decode.Globals}
  {dsg : Encoding.Decompress.Execution.SqrtRatio.Globals}
  {initial : GlobalState} {key signature message : Pointer}

theorem ColdEntryReady.stackCache
    (h : ColdEntryReady cg rg dg ddg dsg initial key signature message)
    (hwf : initial.WF) (i : Nat) : (stackSlot initial i).id ≠ cg.cache :=
  stackSlot_ne_caller initial hwf i h.compression.cache_range

theorem ColdEntryReady.challenge
    (h : ColdEntryReady cg rg dg ddg dsg initial key signature message)
    (hwf : initial.WF) :
    Challenge.ColdChallengeReady cg rg (allocated initial) (stackSlot initial 12)
      key signature message :=
  ⟨compressionReady_stackState cg initial h.compression hwf 13, h.reduction,
    h.stackCache hwf 12,
    stackSlot_ne_caller initial hwf 12 h.compression.constants_range,
    h.keyCache, h.signatureCache, h.messageCache, h.reduceRCache, h.reduceRRCache⟩

end Agave.Ed25519.Verifier.Execution.Dalek
