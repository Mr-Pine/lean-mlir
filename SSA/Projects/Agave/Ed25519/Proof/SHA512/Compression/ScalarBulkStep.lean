import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarBulkMemory
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarBulkRegisters

/-! Exact original scalar-loop backedge after a complete compression block. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace Agave.Ed25519.SHA512.Execution.Dispatch.ScalarBulk
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.Verifier.Execution.Challenge
open ScalarFull
open Spec

theorem scalar_body (E : Env program.Γ) (state : GlobalState)
    (data kp : Pointer) (initial : Spec.State)
    (hd : SmallRange state.mem data 128) (hi : InitialReady E initial)
    (hc : Constants E kp) (hk : KRead state.mem kp)
    (hdata : E.read (%200) = .value data) :
    ∃ E', program.bb4.runBodyFrom E 0 state = program.bb4.runBodyFrom E' 2970 state ∧
      ResultReady E' (compressBlock initial (readBytes state.mem data 128)) ∧
      Before 202 E E' ∧ E'.read (%202) = .value (data.add 128#64) := by
  let E₀ := inputEnv E state.mem data
  obtain ⟨E₁, hr, hresult, _, hf⟩ := scalar_rounds_compressBlock E₀ state initial
    (readBytes state.mem data 128) kp (input_initial E state.mem data initial hi)
    (input_ready E state.mem data initial hi) (input_constants E state.mem data kp hc) hk
  have hp := runBodyFrom_slice E E₀ 0 50 state (input_body E state data hd hdata)
  refine ⟨E₁, hp.trans hr, hresult,
    before_trans (input_before E state.mem data) (before_weaken (frame_before hf) (by decide)), ?_⟩
  rw [hf.read_val 202 (by decide) (by rfl)]
  simp [E₀, inputEnv, mlir_env]

def continueEnv (E : Env program.Γ) : Env program.Γ := E[%3170 := .value 0#1]

theorem continue_before (E : Env program.Γ) : Before 202 E (continueEnv E) := by
  apply Before.write (Before.refl E _)
  decide

theorem continue_body (E : Env program.Γ) (state : GlobalState) (data : Pointer) (n : Nat)
    (hd : SmallRange state.mem data (128 * (n + 2)))
    (hn : E.read (%202) = .value (data.add 128#64))
    (he : E.read (%176) = .value (data.add (BitVec.ofNat 64 (128 * (n + 2))))) :
    program.bb4.runBodyFrom E 2970 state = .value (continueEnv E, state) := by
  have hne := next_ne_end data n hd
  simp [BasicBlock.runBodyFrom, program.bb4, List.foldlM_cons, List.foldlM_nil,
    Instr.run, continueEnv, hn, he, Operation.ptrCmp, Pointer.add_id, hne,
    BinOp.compute, EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect]

/-- The real scalar source compares end pointers; it has no decrement instruction. -/
theorem scalar_continue (E : Env program.Γ) (state : GlobalState)
    (chain data kp : Pointer) (initial : Spec.State) (n : Nat)
    (hd : SmallRange state.mem data (128 * (n + 2)))
    (hi : InitialReady E initial) (hs : StoreReady E chain) (hc : Constants E kp)
    (hk : KRead state.mem kp) (hdata : E.read (%200) = .value data)
    (hend : E.read (%176) = .value (data.add (BitVec.ofNat 64 (128 * (n + 2))))) :
    ∃ E', program.bb4.run program.blockParams E state = .value ((E', .inr 4), state) ∧
      InitialReady E' (compressBlock initial (readBytes state.mem data 128)) ∧
      StoreReady E' chain ∧ Constants E' kp ∧
      E'.read (%200) = .value (data.add 128#64) ∧
      E'.read (%176) = .value ((data.add 128#64).add (BitVec.ofNat 64 (128 * (n + 1)))) := by
  obtain ⟨E₁, hr, hresult, hf, hnext⟩ := scalar_body E state data kp initial
    (live_prefix hd (by omega)) hi hc hk hdata
  have he : E₁.read (%176) = .value (data.add (BitVec.ofNat 64 (128 * (n + 2)))) := by
    rw [hf.read_val 176 (by decide) (by rfl)]
    exact hend
  have hb := hr.trans (continue_body E₁ state data n hd hnext he)
  let result := compressBlock initial (readBytes state.mem data 128)
  let E₂ := scalarLoopEnv (continueEnv E₁) (data.add 128#64) result
  have hlow : Before 193 E E₂ := before_trans
    (before_weaken (before_trans hf (continue_before E₁)) (by decide))
    (loop_before (continueEnv E₁) (data.add 128#64) result)
  refine ⟨E₂, ?_, loop_initial _ _ _, store_before hs hlow,
    constants_before hc (before_weaken hlow (by decide)), loop_cursor _ _ _, ?_⟩
  · rw [BasicBlock.run_eq]
    change (program.bb4.runBodyFrom E 0 state >>= _) = _
    rw [hb]
    simp [program.bb4, Exit.run, Jump.run, continueEnv, E₂, scalarLoopEnv,
      hresult.a, hresult.b, hresult.c, hresult.d, hresult.e, hresult.f, hresult.g, hresult.h,
      hnext, result, mlir_env, mlir_effect, EffectM.bind_eq, EffectM.pure_eq]
  · rw [hlow.read_val 176 (by decide) (by rfl), hend, next_end]

end Agave.Ed25519.SHA512.Execution.Dispatch.ScalarBulk
