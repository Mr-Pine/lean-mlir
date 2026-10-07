import SSA.Projects.Agave.Ed25519.Proof.SHA512.Execution.Contracts

/-! Contextual forms of the reducer/finalizer ABI. A concrete globally bound
wide reducer requires the immutable Montgomery tables to be present. Keeping
that prerequisite explicit avoids claiming an all-state contract for a callee
whose global addresses can otherwise be unallocated or contain arbitrary bytes. -/

namespace Agave.Ed25519.Verifier.Execution.SHA512Finalization

open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.Bridge.Challenge
open Challenge

/-- Exact scalar reduction under an explicit caller/global invariant. -/
def ReduceWideContractUnder (ready : GlobalState → Pointer → Prop)
    (call : Vals [.ptr, .ptr] → EffectM (Vals [])) : Prop :=
  ∀ (state : GlobalState) (dst src : Pointer),
    state.WF → ready state dst →
    SmallRange state.mem dst 32 → SmallRange state.mem src 64 →
    (Range.of dst 256).Disjoint (Range.of src 512) →
    ∃ after,
      call (.cons (.value dst) (.cons (.value src) .nil)) state =
        .value (.nil, after) ∧
      StoreEffect state after dst (digestScalarBytes (state.mem.readAt src 512))

/-- The unrestricted primitive assumption remains available as the special
case in which global readiness has already been incorporated into the callee. -/
theorem reduceWide_unrestricted (call : Vals [.ptr, .ptr] → EffectM (Vals [])) :
    ReduceWideContractUnder (fun _ _ => True) call ↔ ReduceWideContract call := by
  constructor
  · intro h state dst src hwf hd hs hdisjoint
    exact h state dst src hwf trivial hd hs hdisjoint
  · intro h state dst src hwf _ hd hs hdisjoint
    exact h state dst src hwf hd hs hdisjoint

/-- The concrete finalizer ABI can retain the wide reducer's immutable-global
invariant at entry. It has the same all-length SHA context and exact scalar
output as the generic challenge contract. -/
def ScalarFromSha512ContractUnder (ready : GlobalState → Pointer → Prop)
    (call : Vals [.ptr, .ptr] → EffectM (Vals [])) (sha : Sha512Model) : Prop :=
  ∀ (state : GlobalState) (dst ctx : Pointer) (completed pending : Bytes),
    state.WF → ready state dst → SmallRange state.mem dst 32 →
    ContextRepresents sha state.mem ctx completed pending →
    (Range.of dst 256).Disjoint (Range.of ctx 1664) →
    ∃ after,
      call (.cons (.value dst) (.cons (.value ctx) .nil)) state =
        .value (.nil, after) ∧
      StoreEffect state after dst (digestScalarBytes (sha.digest (completed ++ pending)))

theorem scalarFromSha512_unrestricted
    (call : Vals [.ptr, .ptr] → EffectM (Vals [])) (sha : Sha512Model) :
    ScalarFromSha512ContractUnder (fun _ _ => True) call sha ↔
      ScalarFromSha512Contract call sha := by
  constructor
  · intro h state dst ctx completed pending hwf hd hc hdisjoint
    exact h state dst ctx completed pending hwf trivial hd hc hdisjoint
  · intro h state dst ctx completed pending hwf _ hd hc hdisjoint
    exact h state dst ctx completed pending hwf hd hc hdisjoint

end Agave.Ed25519.Verifier.Execution.SHA512Finalization
