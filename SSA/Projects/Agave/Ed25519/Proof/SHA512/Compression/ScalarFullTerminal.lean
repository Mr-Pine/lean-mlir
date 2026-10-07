import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullRound79
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullStoreMemory
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.DispatchExecutionControl

/-! Original final pointer comparison, eight scalar stores and return. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false

namespace Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Spec

structure StoreReady (E : Env program.Γ) (chain : Pointer) : Prop where
  chainPtr : E.read (%arg0) = .value chain
  p1 : E.read (%179) = .value (chain.add 8#64)
  p2 : E.read (%180) = .value (chain.add 16#64)
  p3 : E.read (%181) = .value (chain.add 24#64)
  p4 : E.read (%182) = .value (chain.add 32#64)
  p5 : E.read (%183) = .value (chain.add 40#64)
  p6 : E.read (%184) = .value (chain.add 48#64)
  p7 : E.read (%185) = .value (chain.add 56#64)

theorem StoreReady.of_frame (h : StoreReady E₀ chain) (hf : Frame E₀ E₁) : StoreReady E₁ chain := by
  constructor
  · change E₁.args 0 = .value chain
    rw [hf.1]
    exact h.chainPtr
  · rw [hf.read_val 179 (by decide) (by rfl)]; exact h.p1
  · rw [hf.read_val 180 (by decide) (by rfl)]; exact h.p2
  · rw [hf.read_val 181 (by decide) (by rfl)]; exact h.p3
  · rw [hf.read_val 182 (by decide) (by rfl)]; exact h.p4
  · rw [hf.read_val 183 (by decide) (by rfl)]; exact h.p5
  · rw [hf.read_val 184 (by decide) (by rfl)]; exact h.p6
  · rw [hf.read_val 185 (by decide) (by rfl)]; exact h.p7

def terminalEnv (E : Env program.Γ) : Env program.Γ := E[%3170 := .value 1#1]

theorem terminal_body (E : Env program.Γ) (state : GlobalState) (last : Pointer)
    (hn : E.read (%202) = .value last) (he : E.read (%176) = .value last) :
    program.bb4.runBodyFrom E 2970 state = .value (terminalEnv E, state) := by
  simp [BasicBlock.runBodyFrom, program.bb4, List.foldlM_cons, List.foldlM_nil,
    Instr.run, terminalEnv, hn, he, Operation.ptrCmp, BinOp.compute,
    EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect]

theorem terminal_frame (E : Env program.Γ) : Frame E (terminalEnv E) := by
  apply Frame.write (Frame.refl E)
  decide

theorem terminal_result (E : Env program.Γ) (result : Spec.State)
    (h : ResultReady E result) : ResultReady (terminalEnv E) result := by
  constructor <;> simp [terminalEnv, mlir_env, h.a, h.b, h.c, h.d, h.e, h.f, h.g, h.h]

theorem store_body (E : Env program.Γ) (state : GlobalState) (chain : Pointer)
    (result : Spec.State) (h : StoreReady E chain) (hr : ResultReady E result)
    (hc : SmallRange state.mem chain 64) :
    List.foldlM Instr.run E program.bb5.body state =
      .value (E, {state with mem := state.mem.storeAt chain (Spec.pack result)}) := by
  have hchain := h.chainPtr
  change E.args 0 = .value chain at hchain
  have hf1 : Fits state.mem (chain.add 8#64) 64 := hc.fits_add (k := 8) (count := 8) (by decide)
  have hf2 : Fits state.mem (chain.add 16#64) 64 := hc.fits_add (k := 16) (count := 8) (by decide)
  have hf3 : Fits state.mem (chain.add 24#64) 64 := hc.fits_add (k := 24) (count := 8) (by decide)
  have hf4 : Fits state.mem (chain.add 32#64) 64 := hc.fits_add (k := 32) (count := 8) (by decide)
  have hf5 : Fits state.mem (chain.add 40#64) 64 := hc.fits_add (k := 40) (count := 8) (by decide)
  have hf6 : Fits state.mem (chain.add 48#64) 64 := hc.fits_add (k := 48) (count := 8) (by decide)
  have hf7 : Fits state.mem (chain.add 56#64) 64 := hc.fits_add (k := 56) (count := 8) (by decide)
  have hf0 : Fits state.mem chain 64 := by
    simpa only [Pointer.add_zero] using hc.fits_add (k := 0) (count := 8) (by decide)
  rw [← storeMem_eq state.mem chain hc result]
  simp [program.bb5, List.foldlM_cons, List.foldlM_nil, Instr.run, storeMem,
    hchain, h.p1, h.p2, h.p3, h.p4, h.p5, h.p6, h.p7,
    hr.a, hr.b, hr.c, hr.d, hr.e, hr.f, hr.g, hr.h,
    hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, Fits.storeAt_iff,
    Operation.store, EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect, throwUBIf]

theorem store_step (E : Env program.Γ) (state : GlobalState) (chain : Pointer)
    (result : Spec.State) (h : StoreReady E chain) (hr : ResultReady E result)
    (hc : SmallRange state.mem chain 64) :
    program.bb5.run program.blockParams E state =
      .value ((E, .inr 7), {state with mem := state.mem.storeAt chain (Spec.pack result)}) := by
  unfold BasicBlock.run
  change (List.foldlM Instr.run E program.bb5.body state >>= _) = _
  rw [store_body E state chain result h hr hc]
  simp [program.bb5, Exit.run, mlir_env, mlir_effect, program.blockParams, Jump.run]

theorem store_return (p : Primitives) (g : Globals) (E : Env program.Γ)
    (state : GlobalState) (chain : Pointer) (result : Spec.State)
    (h : StoreReady E chain) (hr : ResultReady E result)
    (hc : SmallRange state.mem chain 64) :
    (program p g).runFrom E 5 state =
      .value (.nil, {state with mem := state.mem.storeAt chain (Spec.pack result)}) := by
  rw [Func.runFrom_eq]
  change (program.bb5.run program.blockParams E state >>= _) = _
  rw [store_step E state chain result h hr hc]
  exact dispatch_return p g E _

end Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
