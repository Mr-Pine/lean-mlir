import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullExecution
import SSA.Projects.RIR.Run.Call

/-! Actual RIR function and call interfaces for the verified scalar count-one path. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 2400000

namespace Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.Verifier.Execution.Challenge
open Agave.Ed25519.Verifier.Execution.SHA512Finalization

def oneArgs (chain data : Pointer) : Vals [.ptr, .ptr, .bv 64] :=
  .cons (.value chain) (.cons (.value data) (.cons (.value 1#64) .nil))

def oneAfter (state : GlobalState) (chain data : Pointer) : GlobalState :=
  {state with mem := state.mem.storeAt chain (Spec.compression.run (state.mem.readAt chain 512) (readBytes state.mem data 128))}

theorem warm_scalar_one_run (p : Primitives) (cg : CompressionGlobals)
    (state : GlobalState) (chain data : Pointer) (hg : CompressionReady cg state)
    (hc : SmallRange state.mem chain 64) (hd : SmallRange state.mem data 128)
    (hb : state.mem.readAt cg.cachePtr 8 = 0#8) :
    (program p (readyGlobals cg)).run (oneArgs chain data) state =
      .value (.nil, oneAfter state chain data) := by
  rw [Func.run_runFrom_eq]
  apply warm_scalar_one_of_ready p cg _ state chain data hg hc hd hb <;> rfl

/-- The scalar backend allocates no frame; the RIR call cleanup therefore
preserves its exact single-store result in every well-formed caller state. -/
theorem warm_scalar_one_call (p : Primitives) (cg : CompressionGlobals)
    (state : GlobalState) (chain data : Pointer) (hwf : state.WF)
    (hg : CompressionReady cg state)
    (hc : SmallRange state.mem chain 64) (hd : SmallRange state.mem data 128)
    (hb : state.mem.readAt cg.cachePtr 8 = 0#8) :
    (program p (readyGlobals cg)).call (oneArgs chain data) state =
      .value (.nil, oneAfter state chain data) := by
  apply Func.call_eq_of_run_eq (warm_scalar_one_run p cg state chain data hg hc hd hb)
  · exact hwf.storeAt
  · rfl

/-- The exact external-call result, whole-memory store effect and preserved
global readiness needed by the count-one Ed25519 SHA finalizer. -/
theorem warm_scalar_one_call_ready (p : Primitives) (cg : CompressionGlobals)
    (state : GlobalState) (chain data : Pointer) (hwf : state.WF)
    (hg : CompressionCallReady cg state chain data)
    (hc : SmallRange state.mem chain 64) (hd : SmallRange state.mem data 128)
    (hb : state.mem.readAt cg.cachePtr 8 = 0#8) :
    (program p (readyGlobals cg)).call (oneArgs chain data) state =
      .value (.nil, oneAfter state chain data) ∧
    StoreEffect state (oneAfter state chain data) chain
      (Spec.compression.run (state.mem.readAt chain 512) (readBytes state.mem data 128)) ∧
    CompressionCallReady cg (oneAfter state chain data) chain data := by
  refine ⟨warm_scalar_one_call p cg state chain data hwf hg.globals hc hd hb,
    ⟨rfl, Nat.le_refl _⟩, ?_⟩
  exact ⟨CompressionReady.storeAt cg state chain _ hg.globals hg.chainConstants hg.chainCache,
    hg.chainConstants, hg.chainCache, hg.dataCache⟩

end Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
