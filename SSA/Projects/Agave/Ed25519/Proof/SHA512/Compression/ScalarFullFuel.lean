import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullCall

/-! A finite six-block execution witness for the count-one scalar call. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 2400000
set_option linter.unusedVariables false

namespace Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.Verifier.Execution.Challenge
open Agave.Ed25519.Verifier.Execution.SHA512Finalization
open Spec

theorem scalar_backend_one_eval (p : Primitives) (g : Globals) (E : Env program.Γ)
    (state : GlobalState) (chain data kp : Pointer) (initial : Spec.State)
    (hc : SmallRange state.mem chain 64) (hd : SmallRange state.mem data 128)
    (hi : InitialReady E initial) (hs : StoreReady E chain) (hconst : Constants E kp)
    (hk : KRead state.mem kp) (hdata : E.read (%200) = .value data)
    (hend : E.read (%176) = .value (data.add 128#64)) :
    (program p g).evalFrom 3 E 4 state = .value (some .nil,
      {state with mem := state.mem.storeAt chain (Spec.pack (compressBlock initial (readBytes state.mem data 128)))}) := by
  obtain ⟨E', hstep, hresult, hstore⟩ := scalar_block_one E state chain data kp initial
    hc hd hi hs hconst hk hdata hend
  simp only [Func.evalFrom, EffectM.bind_eq]
  change (program.bb4.run program.blockParams E state >>= _) = _
  rw [hstep]
  change (program.bb5.run program.blockParams E' state >>= _) = _
  rw [store_step E' state chain _ hstore hresult hc]
  rfl

/-- Exact imported block sequence: bb0, bb2, bb3, bb4, bb5, bb7. -/
theorem warm_scalar_one_eval (p : Primitives) (cg : CompressionGlobals)
    (state : GlobalState) (chain data : Pointer) (hg : CompressionReady cg state)
    (hc : SmallRange state.mem chain 64) (hd : SmallRange state.mem data 128)
    (hb : state.mem.readAt cg.cachePtr 8 = 0#8) :
    (program p (readyGlobals cg)).eval 6 (oneArgs chain data) state =
      .value (some .nil, oneAfter state chain data) := by
  let E : Env program.Γ := Env.init (oneArgs chain data).get
  let g := readyGlobals cg
  change (program p g).evalFrom 6 E 0 state = _
  rw [scalar_warm_one_evalFrom p g E state chain data 3
    hg.constants_range hg.cache_range hb hc hd (by rfl) (by rfl) (by rfl)]
  have hs := scalar_backend_one_eval p g (scalarOneBodyEnv E g state chain data) state
    chain data g.address1 (scalarChainState state.mem chain) hc hd
    (seed_initial E g state chain data) (seed_store E g state chain data (by rfl))
    (seed_constants E g state chain data) (constants_read cg state hg)
    (scalar_one_cursor E g state chain data).1 (scalar_one_cursor E g state chain data).2
  simpa only [oneAfter, Spec.compression,
    Spec.run_one_block _ _ (readBytes_length _ _ _), compressBlockBytes,
    scalarChainState_eq_unpack state.mem chain hc] using hs

end Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
