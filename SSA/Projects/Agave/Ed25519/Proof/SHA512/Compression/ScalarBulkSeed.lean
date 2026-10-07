import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarBulkBounds
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullSeed

/-! Scalar live-register invariants for the arbitrary-count CFG prefix. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace Agave.Ed25519.SHA512.Execution.Dispatch.ScalarBulk
open LeanMLIR.RIR
open ScalarFull

theorem before_symm (h : Before bound E₀ E₁) : Before bound E₁ E₀ :=
  ⟨h.1.symm, fun i hi => (h.2 i hi).symm⟩

theorem load_before (E : Env program.Γ) (chain : Pointer) (s : Spec.State) :
    Before 178 E (scalarLoadEnv E chain s) := by
  unfold scalarLoadEnv
  repeat' (apply Before.write <;> try decide)
  exact Before.refl E _

def bodyEnv (E : Env program.Γ) (g : Globals) (state : GlobalState)
    (chain data : Pointer) (count : BitVec 64) : Env program.Γ :=
  scalarLoopEnv (scalarLoadEnv (boundsEnv (dispatchEntryEnv E g 0) data count)
    chain (scalarChainState state.mem chain)) data (scalarChainState state.mem chain)

theorem body_before (E : Env program.Γ) (g : Globals) (state : GlobalState)
    (chain data : Pointer) (count : BitVec 64) :
    Before 175 (dispatchEntryEnv E g 0) (bodyEnv E g state chain data count) := by
  exact before_trans (bounds_before _ _ _) (before_trans
    (before_weaken (load_before _ _ _) (by decide))
    (before_weaken (loop_before _ _ _) (by decide)))

theorem one_body_before (E : Env program.Γ) (g : Globals) (state : GlobalState)
    (chain data : Pointer) :
    Before 175 (dispatchEntryEnv E g 0) (scalarOneBodyEnv E g state chain data) := by
  have hb : Before 175 (dispatchEntryEnv E g 0) (scalarBoundsEnv (dispatchEntryEnv E g 0) data) := by
    unfold scalarBoundsEnv
    exact Before.write (Before.write (Before.write (Before.refl _ _) _ _ (by decide)) _ _ (by decide)) _ _ (by decide)
  exact before_trans hb (before_trans
    (before_weaken (load_before _ _ _) (by decide))
    (before_weaken (loop_before _ _ _) (by decide)))

theorem body_constants (E : Env program.Γ) (g : Globals) (state : GlobalState)
    (chain data : Pointer) (count : BitVec 64) :
    Constants (bodyEnv E g state chain data count) g.address1 :=
  constants_before (seed_constants E g state chain data)
    (before_weaken (before_trans (before_symm (one_body_before E g state chain data))
      (body_before E g state chain data count)) (by decide))

theorem body_initial (E : Env program.Γ) (g : Globals) (state : GlobalState)
    (chain data : Pointer) (count : BitVec 64) :
    InitialReady (bodyEnv E g state chain data count) (scalarChainState state.mem chain) :=
  loop_initial _ _ _

theorem body_store (E : Env program.Γ) (g : Globals) (state : GlobalState)
    (chain data : Pointer) (count : BitVec 64)
    (hchain : E.read (%arg0) = .value chain) :
    StoreReady (bodyEnv E g state chain data count) chain := by
  constructor
  · change E.args 0 = .value chain
    exact hchain
  all_goals simp [bodyEnv, scalarLoopEnv, scalarLoadEnv, mlir_env]

theorem body_cursor (E : Env program.Γ) (g : Globals) (state : GlobalState)
    (chain data : Pointer) (count : BitVec 64) :
    (bodyEnv E g state chain data count).read (%200) = .value data ∧
    (bodyEnv E g state chain data count).read (%176) =
      .value (data.add (BitVec.ofNat 64 (128 * count.toNat))) := by
  simp [bodyEnv, scalarLoopEnv, scalarLoadEnv, boundsEnv, mlir_env]

end Agave.Ed25519.SHA512.Execution.Dispatch.ScalarBulk
