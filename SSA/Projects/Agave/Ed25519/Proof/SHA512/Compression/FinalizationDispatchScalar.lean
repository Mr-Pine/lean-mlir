import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarBulkCall

/-! The proved scalar suffix is independent of whether entry was cold or
warm. Only the live scalar registers and table bytes are required at bb2. -/
namespace Agave.Ed25519.SHA512.Execution.Dispatch.Finalization

open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.Verifier.Execution.Challenge
open Agave.Ed25519.Verifier.Execution.SHA512Finalization
open ScalarFull ScalarBulk

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

def scalarSuffixEnv (E : Env program.Γ) (state : GlobalState)
    (chain data : Pointer) (count : BitVec 64) : Env program.Γ :=
  scalarLoopEnv (scalarLoadEnv (boundsEnv E data count)
    chain (scalarChainState state.mem chain)) data (scalarChainState state.mem chain)

theorem scalarSuffix_before (E : Env program.Γ) (state : GlobalState)
    (chain data : Pointer) (count : BitVec 64) :
    Before 173 E (scalarSuffixEnv E state chain data count) := by
  exact before_weaken (before_trans (bounds_before _ _ _) (before_trans
    (before_weaken (load_before _ _ _) (by decide))
    (before_weaken (loop_before _ _ _) (by decide)))) (by decide)

theorem dispatch_entry_constants (E : Env program.Γ) (g : Globals) (cache : BitVec 8) :
    Constants (dispatchEntryEnv E g cache) g.address1 := by
  constructor <;> simp [dispatchEntryEnv, dispatchChunk0, dispatchChunk1, dispatchChunk2,
    dispatchChunk3, dispatchChunk4, dispatchChunk5, mlir_env, Pointer.add_add]

theorem dispatch_entry_zero (E : Env program.Γ) (g : Globals) (cache : BitVec 8) :
    (dispatchEntryEnv E g cache).read (%2) = .value 0#64 := by
  simp [dispatchEntryEnv, dispatchChunk0, dispatchChunk1, dispatchChunk2,
    dispatchChunk3, dispatchChunk4, dispatchChunk5, mlir_env]

/-- Exact arbitrary-count execution beginning at the scalar branch, including
zero. Neither the cache value nor the initializer result is read by this suffix. -/
theorem scalar_suffix (p : Primitives) (g : Globals) (E : Env program.Γ)
    (state : GlobalState) (chain data : Pointer) (count : BitVec 64)
    (hc : SmallRange state.mem chain 64) (hd : SmallRange state.mem data (128 * count.toNat))
    (hk : KRead state.mem g.address1) (hconst : Constants E g.address1)
    (hzero : E.read (%2) = .value 0#64)
    (hchain : E.read (%arg0) = .value chain)
    (hdata : E.read (%arg1) = .value data) (hcount : E.read (%arg2) = .value count) :
    (program p g).runFrom E 2 state = .value (.nil, bulkAfter state chain data count) := by
  have hb := bounds_step E state data count hd hdata hcount hconst.v1 hzero
  rw [Func.runFrom_eq]
  change (program.bb2.run program.blockParams E state >>= _) = _
  rw [hb]
  cases hn : count.toNat with
  | zero =>
    have hz : count = 0#64 := BitVec.eq_of_toNat_eq hn
    subst count
    change (program p g).runFrom (boundsEnv E data 0) 7 state = _
    rw [dispatch_return]
    simp [bulkAfter, Spec.compression, readBytes, Spec.run_empty, store_read_self]
  | succ n =>
    have hz : count ≠ 0#64 := by intro hz; subst count; simp at hn
    change (program p g).runFrom (boundsEnv E data count)
      (if count = 0#64 then 7 else 3) state = _
    rw [ite_eq_right hz, Func.runFrom_eq]
    change (program.bb3.run program.blockParams (boundsEnv E data count) state >>= _) = _
    have h3 := scalar_load_step (boundsEnv E data count) state chain data hc
      (by simpa [boundsEnv, mlir_env] using hchain)
      (by simpa [boundsEnv, mlir_env] using hdata)
    rw [h3]
    change (program p g).runFrom (scalarSuffixEnv E state chain data count) 4 state = _
    have hs : StoreReady (scalarSuffixEnv E state chain data count) chain := by
      constructor
      · change E.args 0 = .value chain
        exact hchain
      all_goals simp [scalarSuffixEnv, scalarLoopEnv, scalarLoadEnv, mlir_env]
    have hr := scalar_loop_positive p g state chain g.address1 hc hk n
      (scalarSuffixEnv E state chain data count) data (scalarChainState state.mem chain)
      (by simpa only [hn] using hd) (loop_initial _ _ _) hs
      (constants_before hconst (scalarSuffix_before E state chain data count))
      (by simp [scalarSuffixEnv, scalarLoopEnv, mlir_env])
      (by simp [scalarSuffixEnv, scalarLoopEnv, scalarLoadEnv, boundsEnv, mlir_env, hn])
    simpa only [bulkAfter, Spec.compression, hn, scalarChainState_eq_unpack state.mem chain hc,
      Spec.pack_unpack] using hr

end Agave.Ed25519.SHA512.Execution.Dispatch.Finalization
