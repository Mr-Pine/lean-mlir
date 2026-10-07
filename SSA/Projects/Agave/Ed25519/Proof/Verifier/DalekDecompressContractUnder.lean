import SSA.Projects.Agave.Ed25519.Proof.Verifier.DalekExecutionContracts

/-! Decompression's external constant-memory requirement belongs to the actual
invocation state. The unconditional interface does not establish that memory. -/
namespace Agave.Ed25519.Verifier.Execution.Dalek
open LeanMLIR.RIR
open Reduce64.Execution (SmallRange)

/-- Contextual version of the existing decoder leaf contract. `ready` supplies
only invocation-local prerequisites, such as readable initialized globals. -/
def DecompressContractUnder (ready : GlobalState → Prop)
    (call : Vals [.ptr, .ptr] → EffectM (Vals []))
    (layout : Layout Point Scalar Result) (shared : Shared Point Scalar) : Prop :=
  ∀ (out input : Pointer) (state : GlobalState) (encoded : Bytes32), state.WF →
    ready state → SmallRange state.mem out 168 → ReadBytes state input 32 encoded →
    (Range.of out 1344).Disjoint (Range.of input 256) →
    ∃ after,
      call (args2 out input) state = .value (.nil, after) ∧
      OutputFrame state after out 168 ∧
      match shared.decompress encoded with
      | none => after.mem.readAt out 64 = 0
      | some point => after.mem.readAt out 64 = 1 ∧
          ReadBytes after (out.add 8) 160 (layout.point point)

theorem DecompressContract.under
    (h : DecompressContract call layout shared) (ready : GlobalState → Prop) :
    DecompressContractUnder ready call layout shared := by
  intro out input state encoded hwf _ hout hin hd
  exact h out input state encoded hwf hout hin hd

theorem DecompressContractUnder.mono
    (h : DecompressContractUnder ready call layout shared)
    (hready : ∀ state, stronger state → ready state) :
    DecompressContractUnder stronger call layout shared := by
  intro out input state encoded hwf hs hout hin hd
  exact h out input state encoded hwf (hready state hs) hout hin hd

end Agave.Ed25519.Verifier.Execution.Dalek
