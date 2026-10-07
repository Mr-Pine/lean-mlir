import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarExecutionEntry

/-! Composition of the three successful original CFG steps for a warm
scalar count-one call. Both bounded execution and the continuation equation
are exposed; the theorem reaches the real unrolled eighty-round body. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace Agave.Ed25519.SHA512.Execution.Dispatch
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution

/-- Concrete register state at the first scalar iteration. -/
def scalarOneBodyEnv (E : Env program.Γ) (g : Globals) (state : GlobalState)
    (chain data : Pointer) : Env program.Γ :=
  scalarLoopEnv
    (scalarLoadEnv (scalarBoundsEnv (dispatchEntryEnv E g 0) data)
      chain (scalarChainState state.mem chain)) data (scalarChainState state.mem chain)

/-- The exact three successful imported steps, all with unchanged state. -/
theorem scalar_warm_one_steps (g : Globals) (E : Env program.Γ)
    (state : GlobalState) (chain data : Pointer)
    (hk : SmallRange state.mem g.address1 640)
    (hb : SmallRange state.mem g.address0 1)
    (hr : state.mem.readAt g.address0 8 = 0#8)
    (hc : SmallRange state.mem chain 64) (hd : SmallRange state.mem data 128)
    (hchain : E.read (%arg0) = .value chain)
    (hdata : E.read (%arg1) = .value data)
    (hcount : E.read (%arg2) = .value 1#64) :
    (program.bb0 g).run program.blockParams E state =
      .value ((dispatchEntryEnv E g 0, .inr 2), state) ∧
    program.bb2.run program.blockParams (dispatchEntryEnv E g 0) state =
      .value ((scalarBoundsEnv (dispatchEntryEnv E g 0) data, .inr 3), state) ∧
    program.bb3.run program.blockParams
        (scalarBoundsEnv (dispatchEntryEnv E g 0) data) state =
      .value ((scalarOneBodyEnv E g state chain data, .inr 4), state) := by
  change E.args 0 = .value chain at hchain
  change E.args 1 = .value data at hdata
  change E.args 2 = .value 1#64 at hcount
  refine ⟨?_, ?_, ?_⟩
  · exact dispatch_entry_step g E state 0 hk hb hr
  · apply scalar_one_bounds_step _ state data hd <;>
      simp [dispatchEntryEnv, dispatchChunk0, dispatchChunk1, dispatchChunk2,
        dispatchChunk3, dispatchChunk4, dispatchChunk5, mlir_env, hdata, hcount]
  · apply scalar_load_step _ state chain data hc <;>
      simp [scalarBoundsEnv, dispatchEntryEnv, dispatchChunk0, dispatchChunk1,
        dispatchChunk2, dispatchChunk3, dispatchChunk4, dispatchChunk5,
        mlir_env, hchain, hdata]

/-- The continuation starts at bb4 after three concretely defined steps.
No property of the unfinished eighty-round body is assumed. -/
theorem scalar_warm_one_runFrom (p : Primitives) (g : Globals) (E : Env program.Γ)
    (state : GlobalState) (chain data : Pointer)
    (hk : SmallRange state.mem g.address1 640)
    (hb : SmallRange state.mem g.address0 1)
    (hr : state.mem.readAt g.address0 8 = 0#8)
    (hc : SmallRange state.mem chain 64) (hd : SmallRange state.mem data 128)
    (hchain : E.read (%arg0) = .value chain)
    (hdata : E.read (%arg1) = .value data)
    (hcount : E.read (%arg2) = .value 1#64) :
    (program p g).runFrom E 0 state =
      (program p g).runFrom (scalarOneBodyEnv E g state chain data) 4 state := by
  obtain ⟨h0, h2, h3⟩ := scalar_warm_one_steps g E state chain data
    hk hb hr hc hd hchain hdata hcount
  rw [Func.runFrom_eq]
  change ((program.bb0 g).run program.blockParams E state >>= _) = _
  rw [h0]
  change (program p g).runFrom (dispatchEntryEnv E g 0) 2 state = _
  rw [Func.runFrom_eq]
  change (program.bb2.run program.blockParams (dispatchEntryEnv E g 0) state >>= _) = _
  rw [h2]
  change (program p g).runFrom (scalarBoundsEnv (dispatchEntryEnv E g 0) data) 3 state = _
  rw [Func.runFrom_eq]
  change (program.bb3.run program.blockParams
    (scalarBoundsEnv (dispatchEntryEnv E g 0) data) state >>= _) = _
  rw [h3]
  rfl

/-- Bounded execution confirms the finite entry trace independently of the
behavior or termination of the pending scalar compression body. -/
theorem scalar_warm_one_evalFrom (p : Primitives) (g : Globals) (E : Env program.Γ)
    (state : GlobalState) (chain data : Pointer) (fuel : Nat)
    (hk : SmallRange state.mem g.address1 640)
    (hb : SmallRange state.mem g.address0 1)
    (hr : state.mem.readAt g.address0 8 = 0#8)
    (hc : SmallRange state.mem chain 64) (hd : SmallRange state.mem data 128)
    (hchain : E.read (%arg0) = .value chain)
    (hdata : E.read (%arg1) = .value data)
    (hcount : E.read (%arg2) = .value 1#64) :
    (program p g).evalFrom (fuel + 3) E 0 state =
      (program p g).evalFrom fuel (scalarOneBodyEnv E g state chain data) 4 state := by
  obtain ⟨h0, h2, h3⟩ := scalar_warm_one_steps g E state chain data
    hk hb hr hc hd hchain hdata hcount
  simp only [Func.evalFrom, EffectM.bind_eq]
  change ((program.bb0 g).run program.blockParams E state >>= _) = _
  rw [h0]
  change ((program.bb2).run program.blockParams (dispatchEntryEnv E g 0) state >>= _) = _
  rw [h2]
  change ((program.bb3).run program.blockParams
    (scalarBoundsEnv (dispatchEntryEnv E g 0) data) state >>= _) = _
  rw [h3]
  rfl

/-- At count one the loop cursor and the end pointer share the data
allocation, and the next 128-byte advance is exactly the end pointer. -/
theorem scalar_one_cursor (E : Env program.Γ) (g : Globals) (state : GlobalState)
    (chain data : Pointer) :
    (scalarOneBodyEnv E g state chain data).read (%200) = .value data ∧
    (scalarOneBodyEnv E g state chain data).read (%176) = .value (data.add 128#64) := by
  simp [scalarOneBodyEnv, scalarLoopEnv, scalarLoadEnv, scalarBoundsEnv, mlir_env]

end Agave.Ed25519.SHA512.Execution.Dispatch
