import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarBulkSeed

/-! Exact source entry and zero/nonzero branch for every live scalar count. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace Agave.Ed25519.SHA512.Execution.Dispatch.ScalarBulk
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution

theorem warm_bounds_runFrom (p : Primitives) (g : Globals) (E : Env program.Γ)
    (state : GlobalState) (data : Pointer) (count : BitVec 64)
    (hk : SmallRange state.mem g.address1 640) (hb : SmallRange state.mem g.address0 1)
    (hr : state.mem.readAt g.address0 8 = 0#8)
    (hd : SmallRange state.mem data (128 * count.toNat))
    (hdata : E.read (%arg1) = .value data) (hcount : E.read (%arg2) = .value count) :
    (program p g).runFrom E 0 state =
      (program p g).runFrom (boundsEnv (dispatchEntryEnv E g 0) data count)
        (if count = 0#64 then 7 else 3) state := by
  change E.args 1 = .value data at hdata
  change E.args 2 = .value count at hcount
  rw [dispatch_entry_runFrom p g E state 0 hk hb hr]
  change (program p g).runFrom (dispatchEntryEnv E g 0) 2 state = _
  have h2 : program.bb2.run program.blockParams (dispatchEntryEnv E g 0) state =
      .value ((boundsEnv (dispatchEntryEnv E g 0) data count,
        .inr (if count = 0#64 then 7 else 3)), state) := by
    apply bounds_step _ state data count hd
    all_goals simp [dispatchEntryEnv, dispatchChunk0, dispatchChunk1, dispatchChunk2,
      dispatchChunk3, dispatchChunk4, dispatchChunk5, mlir_env, hdata, hcount]
  rw [Func.runFrom_eq]
  change (program.bb2.run program.blockParams (dispatchEntryEnv E g 0) state >>= _) = _
  rw [h2]
  rfl

theorem warm_positive_runFrom (p : Primitives) (g : Globals) (E : Env program.Γ)
    (state : GlobalState) (chain data : Pointer) (count : BitVec 64) (hn : count ≠ 0#64)
    (hk : SmallRange state.mem g.address1 640) (hb : SmallRange state.mem g.address0 1)
    (hr : state.mem.readAt g.address0 8 = 0#8)
    (hc : SmallRange state.mem chain 64) (hd : SmallRange state.mem data (128 * count.toNat))
    (hchain : E.read (%arg0) = .value chain)
    (hdata : E.read (%arg1) = .value data) (hcount : E.read (%arg2) = .value count) :
    (program p g).runFrom E 0 state =
      (program p g).runFrom (bodyEnv E g state chain data count) 4 state := by
  rw [warm_bounds_runFrom p g E state data count hk hb hr hd hdata hcount, ite_eq_right hn]
  rw [Func.runFrom_eq]
  change (program.bb3.run program.blockParams (boundsEnv (dispatchEntryEnv E g 0) data count) state >>= _) = _
  have h3 := scalar_load_step (boundsEnv (dispatchEntryEnv E g 0) data count) state chain data hc
    (by simpa [boundsEnv, dispatchEntryEnv, dispatchChunk0, dispatchChunk1, dispatchChunk2,
      dispatchChunk3, dispatchChunk4, dispatchChunk5, mlir_env] using hchain)
    (by simpa [boundsEnv, dispatchEntryEnv, dispatchChunk0, dispatchChunk1, dispatchChunk2,
      dispatchChunk3, dispatchChunk4, dispatchChunk5, mlir_env] using hdata)
  rw [h3]
  rfl

theorem warm_zero_runFrom (p : Primitives) (g : Globals) (E : Env program.Γ)
    (state : GlobalState) (data : Pointer)
    (hk : SmallRange state.mem g.address1 640) (hb : SmallRange state.mem g.address0 1)
    (hr : state.mem.readAt g.address0 8 = 0#8)
    (hd : SmallRange state.mem data 0)
    (hdata : E.read (%arg1) = .value data) (hcount : E.read (%arg2) = .value 0#64) :
    (program p g).runFrom E 0 state = .value (.nil, state) := by
  rw [warm_bounds_runFrom p g E state data 0 hk hb hr (by simpa using hd) hdata hcount]
  exact dispatch_return p g _ state

end Agave.Ed25519.SHA512.Execution.Dispatch.ScalarBulk
