import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarBulkExecution

/-! Generic scalar source continuation, independent of cache branch selection. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace Agave.Ed25519.SHA512.Execution.Dispatch.ScalarBulk
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.Verifier.Execution.Challenge
open ScalarFull

def backendBodyEnv (E : Env program.Γ) (state : GlobalState)
    (chain data : Pointer) (count : BitVec 64) : Env program.Γ :=
  scalarLoopEnv (scalarLoadEnv (boundsEnv E data count)
    chain (scalarChainState state.mem chain)) data (scalarChainState state.mem chain)

theorem backend_before (E : Env program.Γ) (state : GlobalState)
    (chain data : Pointer) (count : BitVec 64) :
    Before 175 E (backendBodyEnv E state chain data count) := by
  exact before_trans (bounds_before _ _ _) (before_trans
    (before_weaken (load_before _ _ _) (by decide))
    (before_weaken (loop_before _ _ _) (by decide)))

theorem backend_store (E : Env program.Γ) (state : GlobalState)
    (chain data : Pointer) (count : BitVec 64)
    (hchain : E.read (%arg0) = .value chain) :
    StoreReady (backendBodyEnv E state chain data count) chain := by
  constructor
  · change E.args 0 = .value chain
    exact hchain
  all_goals simp [backendBodyEnv, scalarLoopEnv, scalarLoadEnv, mlir_env]

theorem backend_cursor (E : Env program.Γ) (state : GlobalState)
    (chain data : Pointer) (count : BitVec 64) :
    (backendBodyEnv E state chain data count).read (%200) = .value data ∧
    (backendBodyEnv E state chain data count).read (%176) =
      .value (data.add (BitVec.ofNat 64 (128 * count.toNat))) := by
  simp [backendBodyEnv, scalarLoopEnv, scalarLoadEnv, boundsEnv, mlir_env]

/-- Every scalar-path source execution from bb2, regardless of how the
original cache switch selected it. The source inputs and constant registers
are explicit, while the global memory and all per-block instructions execute. -/
theorem scalar_bulk_runFrom (p : Primitives) (g : Globals) (E : Env program.Γ)
    (state : GlobalState) (chain data kp : Pointer) (count : BitVec 64)
    (hc : SmallRange state.mem chain 64) (hd : SmallRange state.mem data (128 * count.toNat))
    (hk : KRead state.mem kp) (hconst : Constants E kp)
    (hzero : E.read (%2) = .value 0#64)
    (hchain : E.read (%arg0) = .value chain)
    (hdata : E.read (%arg1) = .value data) (hcount : E.read (%arg2) = .value count) :
    (program p g).runFrom E 2 state = .value (.nil,
      {state with mem := state.mem.storeAt chain (Spec.compression.run (state.mem.readAt chain 512) (readBytes state.mem data (128 * count.toNat)))}) := by
  have h2 := bounds_step E state data count hd hdata hcount hconst.v1 hzero
  rw [Func.runFrom_eq]
  change (program.bb2.run program.blockParams E state >>= _) = _
  rw [h2]
  cases hn : count.toNat with
  | zero =>
    have hz : count = 0#64 := BitVec.eq_of_toNat_eq hn
    subst count
    change (program p g).runFrom (boundsEnv E data 0) 7 state = _
    rw [dispatch_return]
    simp [Spec.compression, readBytes, Spec.run_empty, store_read_self]
  | succ n =>
    have hz : count ≠ 0#64 := by intro hz; subst count; simp at hn
    rw [ite_eq_right hz]
    change (program p g).runFrom (boundsEnv E data count) 3 state = _
    rw [Func.runFrom_eq]
    change (program.bb3.run program.blockParams (boundsEnv E data count) state >>= _) = _
    rw [scalar_load_step (boundsEnv E data count) state chain data hc
      (by simpa [boundsEnv, mlir_env] using hchain)
      (by simpa [boundsEnv, mlir_env] using hdata)]
    change (program p g).runFrom (backendBodyEnv E state chain data count) 4 state = _
    have hcur := backend_cursor E state chain data count
    have hloop := scalar_loop_positive p g state chain kp hc hk n
      (backendBodyEnv E state chain data count) data (scalarChainState state.mem chain)
      (by simpa only [hn] using hd) (loop_initial _ _ _)
      (backend_store E state chain data count hchain)
      (constants_before hconst (before_weaken (backend_before E state chain data count) (by decide)))
      hcur.1 (by simpa only [hn] using hcur.2)
    simpa only [Spec.compression, hn, scalarChainState_eq_unpack state.mem chain hc,
      Spec.pack_unpack] using hloop

/-- The imported dispatch entry establishes its constants before inspecting
the cache byte. The same constant invariant therefore covers all three cache
values and either initializer return value. -/
theorem entry_constants (E : Env program.Γ) (g : Globals) (cache : BitVec 8) :
    Constants (dispatchEntryEnv E g cache) g.address1 := by
  have h0 : Constants (dispatchEntryEnv E g 0) g.address1 :=
    constants_before (seed_constants E g ⟨default, default⟩ g.address0 g.address0)
      (before_weaken (before_symm (one_body_before E g ⟨default, default⟩ g.address0 g.address0)) (by decide))
  apply constants_before h0
  let base := dispatchChunk4 (dispatchChunk3 (dispatchChunk2
    (dispatchChunk1 (dispatchChunk0 E g 0) g 0) g 0) g 0) g 0
  change Before 173 (base[%173 := .value (0 : BitVec 8)]) (base[%173 := .value cache])
  exact before_trans
    (before_symm (Before.write (Before.refl base 173) _ _ (by decide)))
    (Before.write (Before.refl base 173) _ _ (by decide))

end Agave.Ed25519.SHA512.Execution.Dispatch.ScalarBulk
