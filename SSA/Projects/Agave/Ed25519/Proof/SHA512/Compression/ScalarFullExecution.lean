import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullRounds
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullSeed
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullConstantsMemory
import SSA.Projects.Agave.Ed25519.Proof.SHA512.CompressionFold

/-! Count-one scalar execution of the original sha2 0.11.0 dispatcher.
The complete imported arithmetic, memory accesses and CFG refine the independent
SHA-512 compression specification. Globals and the warm scalar cache byte are
explicit premises; no external primitive execution equation is needed. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 2400000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.Verifier.Execution.Challenge
open Agave.Ed25519.Verifier.Execution.SHA512Finalization
open Spec

private theorem input_store (E : Env program.Γ) (mem : MemoryState) (chain data : Pointer)
    (h : StoreReady E chain) : StoreReady (inputEnv E mem data) chain := by
  have hb := input_before E mem data
  constructor
  · change (inputEnv E mem data).args 0 = .value chain
    rw [hb.1]
    exact h.chainPtr
  · rw [hb.read_val 179 (by decide) (by rfl)]; exact h.p1
  · rw [hb.read_val 180 (by decide) (by rfl)]; exact h.p2
  · rw [hb.read_val 181 (by decide) (by rfl)]; exact h.p3
  · rw [hb.read_val 182 (by decide) (by rfl)]; exact h.p4
  · rw [hb.read_val 183 (by decide) (by rfl)]; exact h.p5
  · rw [hb.read_val 184 (by decide) (by rfl)]; exact h.p6
  · rw [hb.read_val 185 (by decide) (by rfl)]; exact h.p7

/-- Execute the entire imported scalar block, from message loads through
all eighty rounds and the count-one branch to the scalar stores. -/
theorem scalar_block_one (E : Env program.Γ) (state : GlobalState)
    (chain data kp : Pointer) (initial : Spec.State)
    (hc : SmallRange state.mem chain 64) (hd : SmallRange state.mem data 128)
    (hi : InitialReady E initial) (hs : StoreReady E chain) (hconst : Constants E kp)
    (hk : KRead state.mem kp) (hdata : E.read (%200) = .value data)
    (hend : E.read (%176) = .value (data.add 128#64)) :
    ∃ E', program.bb4.run program.blockParams E state = .value ((E', .inr 5), state) ∧
      ResultReady E' (compressBlock initial (readBytes state.mem data 128)) ∧
      StoreReady E' chain := by
  let E₀ := inputEnv E state.mem data
  obtain ⟨E₁, hr, hresult, _, hf⟩ := scalar_rounds_compressBlock E₀ state initial
    (readBytes state.mem data 128) kp (input_initial E state.mem data initial hi)
    (input_ready E state.mem data initial hi) (input_constants E state.mem data kp hconst) hk
  have hn : E₁.read (%202) = .value (data.add 128#64) := by
    rw [hf.read_val 202 (by decide) (by rfl)]
    simp [E₀, inputEnv, mlir_env]
  have he : E₁.read (%176) = .value (data.add 128#64) := by
    rw [hf.read_val 176 (by decide) (by rfl)]
    rw [(input_before E state.mem data).read_val 176 (by decide) (by rfl)]
    exact hend
  have ht := terminal_body E₁ state (data.add 128#64) hn he
  have hp := runBodyFrom_slice E E₀ 0 50 state (input_body E state data hd hdata)
  have hb : program.bb4.runBodyFrom E 0 state = .value (terminalEnv E₁, state) :=
    hp.trans (hr.trans ht)
  refine ⟨terminalEnv E₁, ?_, terminal_result E₁ _ hresult,
    ((input_store E state.mem chain data hs).of_frame hf).of_frame (terminal_frame E₁)⟩
  rw [BasicBlock.run_eq]
  change (program.bb4.runBodyFrom E 0 state >>= _) = _
  rw [hb]
  simp [program.bb4, Exit.run, Jump.run, terminalEnv, mlir_env, mlir_effect,
    EffectM.bind_eq, EffectM.pure_eq, program.blockParams]
  all_goals rfl

/-- Full scalar backend return, including exactly the native chaining-state store. -/
theorem scalar_backend_one (p : Primitives) (g : Globals) (E : Env program.Γ)
    (state : GlobalState) (chain data kp : Pointer) (initial : Spec.State)
    (hc : SmallRange state.mem chain 64) (hd : SmallRange state.mem data 128)
    (hi : InitialReady E initial) (hs : StoreReady E chain) (hconst : Constants E kp)
    (hk : KRead state.mem kp) (hdata : E.read (%200) = .value data)
    (hend : E.read (%176) = .value (data.add 128#64)) :
    (program p g).runFrom E 4 state = .value (.nil,
      {state with mem := state.mem.storeAt chain (Spec.pack (compressBlock initial (readBytes state.mem data 128)))}) := by
  obtain ⟨E', hstep, hresult, hstore⟩ := scalar_block_one E state chain data kp initial
    hc hd hi hs hconst hk hdata hend
  rw [Func.runFrom_eq]
  change (program.bb4.run program.blockParams E state >>= _) = _
  rw [hstep]
  exact store_return p g E' state chain _ hstore hresult hc

/-- Exact count-one warm-scalar dispatcher refinement. Every memory premise
is local: live chaining/input/table/cache ranges, the table words, and cache 0. -/
theorem warm_scalar_one (p : Primitives) (g : Globals) (E : Env program.Γ)
    (state : GlobalState) (chain data : Pointer)
    (hc : SmallRange state.mem chain 64) (hd : SmallRange state.mem data 128)
    (hkr : SmallRange state.mem g.address1 640) (hbr : SmallRange state.mem g.address0 1)
    (hk : KRead state.mem g.address1) (hb : state.mem.readAt g.address0 8 = 0#8)
    (hchain : E.read (%arg0) = .value chain)
    (hdata : E.read (%arg1) = .value data) (hcount : E.read (%arg2) = .value 1#64) :
    (program p g).runFrom E 0 state = .value (.nil,
      {state with mem := state.mem.storeAt chain (Spec.compression.run (state.mem.readAt chain 512) (readBytes state.mem data 128))}) := by
  rw [scalar_warm_one_runFrom p g E state chain data hkr hbr hb hc hd hchain hdata hcount]
  have hs := scalar_backend_one p g (scalarOneBodyEnv E g state chain data) state
    chain data g.address1 (scalarChainState state.mem chain) hc hd
    (seed_initial E g state chain data) (seed_store E g state chain data hchain)
    (seed_constants E g state chain data) hk
    (scalar_one_cursor E g state chain data).1 (scalar_one_cursor E g state chain data).2
  simpa only [Spec.compression, Spec.run_one_block _ _ (readBytes_length _ _ _),
    compressBlockBytes, scalarChainState_eq_unpack state.mem chain hc] using hs

/-- Tie the extracted global addresses to explicit K64/cache allocations. -/
def readyGlobals (cg : CompressionGlobals) : Globals :=
  ⟨cg.cachePtr, cg.constantsPtr⟩

/-- The checked global invariant discharges all eighty volatile K64 loads.
No assumption about an external compression primitive occurs in this theorem. -/
theorem warm_scalar_one_of_ready (p : Primitives) (cg : CompressionGlobals)
    (E : Env program.Γ) (state : GlobalState) (chain data : Pointer)
    (hg : CompressionReady cg state)
    (hc : SmallRange state.mem chain 64) (hd : SmallRange state.mem data 128)
    (hb : state.mem.readAt cg.cachePtr 8 = 0#8)
    (hchain : E.read (%arg0) = .value chain)
    (hdata : E.read (%arg1) = .value data) (hcount : E.read (%arg2) = .value 1#64) :
    (program p (readyGlobals cg)).runFrom E 0 state = .value (.nil,
      {state with mem := state.mem.storeAt chain (Spec.compression.run (state.mem.readAt chain 512) (readBytes state.mem data 128))}) :=
  warm_scalar_one p (readyGlobals cg) E state chain data hc hd
    hg.constants_range hg.cache_range (constants_read cg state hg) hb hchain hdata hcount

end Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
