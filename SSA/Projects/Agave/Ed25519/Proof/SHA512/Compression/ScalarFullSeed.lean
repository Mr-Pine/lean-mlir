import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullInput
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullTerminal
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarExecutionPrefix

/-! Discharge concrete register invariants from the checked count-one CFG prefix. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 2400000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Spec

theorem seed_initial (E : Env program.Γ) (g : Globals) (state : GlobalState)
    (chain data : Pointer) :
    InitialReady (scalarOneBodyEnv E g state chain data) (scalarChainState state.mem chain) := by
  constructor <;> simp [scalarOneBodyEnv, scalarLoopEnv, mlir_env]

theorem seed_store (E : Env program.Γ) (g : Globals) (state : GlobalState)
    (chain data : Pointer) (hchain : E.read (%arg0) = .value chain) :
    StoreReady (scalarOneBodyEnv E g state chain data) chain := by
  constructor
  · change E.args 0 = .value chain
    exact hchain
  all_goals simp [scalarOneBodyEnv, scalarLoopEnv, scalarLoadEnv, mlir_env]

theorem seed_constants (E : Env program.Γ) (g : Globals) (state : GlobalState)
    (chain data : Pointer) :
    Constants (scalarOneBodyEnv E g state chain data) g.address1 := by
  constructor <;>
    simp [scalarOneBodyEnv, scalarLoopEnv, scalarLoadEnv, scalarBoundsEnv,
      dispatchEntryEnv, dispatchChunk0, dispatchChunk1, dispatchChunk2,
      dispatchChunk3, dispatchChunk4, dispatchChunk5, mlir_env, Pointer.add_add]

end Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
