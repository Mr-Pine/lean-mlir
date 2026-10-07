import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.Arithmetic
import SSA.Projects.Agave.Ed25519.Proof.Verifier.DalekExecutionContracts

/-! Exact local ABI obligation for `Scalar::from_bytes_mod_order_wide`.
This file defines the obligation and proves consequences of it. It does not
supply an inhabitant for the independently extracted RIR implementation. -/

namespace Agave.Ed25519.Verifier.Execution.ScalarWide

open LeanMLIR.RIR
open Agave.Ed25519.Bridge Agave.Ed25519.Bridge.Challenge
open Agave.Ed25519.Reduce64.Execution (SmallRange)
open Agave.Ed25519.Verifier.Execution.Dalek (args2 ReadBytes OutputFrame)

/-- Success, canonical little-endian scalar bytes, and the caller-visible
frame. Input and output do not alias, as required by the pinned Rust ABI.
Any implementation's global-initialization obligations must be discharged
separately before it can satisfy this contract. -/
def ReduceWideContract (call : Vals [.ptr, .ptr] → EffectM (Vals [])) : Prop :=
  ∀ (out input : Pointer) (state : GlobalState) (bytes : BitVec 512),
    state.WF → SmallRange state.mem out 32 → ReadBytes state input 64 bytes →
    (Range.of out 256).Disjoint (Range.of input 512) →
    ∃ after,
      call (args2 out input) state = .value (.nil, after) ∧
      OutputFrame state after out 32 ∧ ReadBytes after out 32 (reducedBytes bytes)

/-- Explicit observations available at a call site once the reducer contract
has independently been proved: exact integer result, canonical bound, and
preservation of all 64 input bytes, with the full output frame retained. -/
theorem observations_of_contract
    (call : Vals [.ptr, .ptr] → EffectM (Vals []))
    (contract : ReduceWideContract call)
    (out input : Pointer) (before : GlobalState) (bytes : BitVec 512)
    (hwf : before.WF) (hout : SmallRange before.mem out 32)
    (hin : ReadBytes before input 64 bytes)
    (hdisjoint : (Range.of out 256).Disjoint (Range.of input 512)) :
    ∃ after,
      call (args2 out input) before = .value (.nil, after) ∧
      OutputFrame before after out 32 ∧
      ReadBytes after input 64 bytes ∧
      ReadBytes after out 32 (reducedBytes bytes) ∧
      (after.mem.readAt out 256).toNat =
        decodeLE (bytesOf (n := 64) bytes) % subgroupOrder ∧
      (after.mem.readAt out 256).toNat < subgroupOrder := by
  obtain ⟨after, hcall, hframe, hread⟩ := contract out input before bytes hwf hout hin hdisjoint
  refine ⟨after, hcall, hframe,
    OutputFrame.readBytes before after out input 32 64 bytes hframe hin hdisjoint.symm,
    hread, ?_, ?_⟩
  · rw [hread.2, reducedBytes_toNat, hashToScalar_eq_decodeLE]
  · rw [hread.2]
    exact reducedBytes_canonical bytes

end Agave.Ed25519.Verifier.Execution.ScalarWide
