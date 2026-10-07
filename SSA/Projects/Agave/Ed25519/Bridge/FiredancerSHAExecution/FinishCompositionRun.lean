import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.FinishCompositionExecution
import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.FinishCompositionState

/-! Full execution of the imported Firedancer finalizer with its actual scalar
core, including both padding branches and caller-frame cleanup. -/
namespace Agave.Ed25519.Bridge.FiredancerSHAExecution.Finish
open LeanMLIR.RIR Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.SHA512 Agave.Ed25519.SHA512.Spec
set_option maxRecDepth 100000
set_option maxHeartbeats 2500000
set_option linter.unusedSimpArgs false

/-- Full imported finalizer execution, under only live memory, the actual
installed constant table, legal buffer count and ordinary allocation separation. -/
theorem run (kp context output : Pointer) (state : GlobalState) (used : Nat) (lo hi : Word)
    (h : Ready state context output kp) (hu : used < 128)
    (hc : state.mem.readAt (context.add 200#64) 64 = BitVec.ofNat 64 used)
    (hlo : state.mem.readAt (context.add 208#64) 64 = lo)
    (hhi : state.mem.readAt (context.add 216#64) 64 = hi) :
    (program (Core.program kp).call).run (program.args (.value context) (.value output)) state =
      .value (.cons (.value output) .nil, finishState state context output used lo hi) := by
  let core := (Core.program kp).call
  let E : Env program.Γ := Env.init (program.args (.value context) (.value output)).get
  let marked := markerState state context used
  have hm : Ready marked context output kp := h.marker used
  by_cases hs : used < 112
  · let prepared := lastState marked context (used + 1) lo hi
    let after := compressionState prepared context
    have hp : Ready prepared context output kp := hm.last _ lo hi
    have ha : Ready after context output kp := hp.compression
    have hb0 := entry_short core E state context used lo hi (by rfl) hs h.contextLive hc hlo hhi
    have hready := entry_lastReady E context output used (used + 1) lo hi (by rfl) (by rfl)
    have hb2 := last_block core _ marked after context output (used + 1) lo hi
      (readState after.mem context) hready (by omega) hm.contextLive
      ha.contextLive ha.outputLive h.output_ne_context rfl
      (compression_call kp context output prepared hp)
    have hr : (program core).run (program.args (.value context) (.value output)) state =
        .value (.cons (.value output) .nil, finalOutputState after context output) := by
      rw [Func.run_runFrom_eq, Func.runFrom_eq]
      change (program.bb0.run (program core).blockParams E state >>= fun x =>
        (program core).continue x.1.1 x.1.2 x.2) = _
      rw [hb0]
      change (program core).runFrom (lastEntry (entryEnv E context used lo hi) (used + 1))
        2 marked = _
      rw [Func.runFrom_eq]
      change ((program.bb2 core).run (program core).blockParams _ marked >>= fun x =>
        (program core).continue x.1.1 x.1.2 x.2) = _
      rw [hb2]
      rfl
    simpa only [finishState, beforeOutput, ite_eq_left hs, finalOutputState,
      after, prepared, marked] using hr
  · let first := longState marked context used
    let middle := compressionState first context
    let prepared := lastState middle context 0 lo hi
    let after := compressionState prepared context
    have hf : Ready first context output kp := hm.long used
    have hmid : Ready middle context output kp := hf.compression
    have hp : Ready prepared context output kp := hmid.last 0 lo hi
    have ha : Ready after context output kp := hp.compression
    have hb0 := entry_long core E state context used lo hi (by rfl) hu (by omega)
      h.contextLive hc hlo hhi
    have hb1 := long_block core (entryEnv E context used lo hi) marked middle context used
      hu hm.contextLive (by simp only [entryEnv, mlir_env]; rfl)
      (by simp [entryEnv, mlir_env])
      (by simp [entryEnv, mlir_env, BitVec.ofNat_add])
      (by simp [entryEnv, mlir_env]) (by simp [entryEnv, mlir_env])
      (by simp [entryEnv, mlir_env]) (by simp [entryEnv, mlir_env])
      (by simp [entryEnv, mlir_env]) (compression_call kp context output first hf)
    have hready := long_lastReady E context output used lo hi (by rfl) (by rfl)
    have hb2 := last_block core _ middle after context output 0 lo hi
      (readState after.mem context) hready (by decide) hmid.contextLive
      ha.contextLive ha.outputLive h.output_ne_context rfl
      (compression_call kp context output prepared hp)
    have hr : (program core).run (program.args (.value context) (.value output)) state =
        .value (.cons (.value output) .nil, finalOutputState after context output) := by
      rw [Func.run_runFrom_eq, Func.runFrom_eq]
      change (program.bb0.run (program core).blockParams E state >>= fun x =>
        (program core).continue x.1.1 x.1.2 x.2) = _
      rw [hb0]
      change (program core).runFrom (entryEnv E context used lo hi) 1 marked = _
      rw [Func.runFrom_eq]
      change ((program.bb1 core).run (program core).blockParams _ marked >>= fun x =>
        (program core).continue x.1.1 x.1.2 x.2) = _
      rw [hb1]
      change (program core).runFrom
        (lastEntry (longEnv (entryEnv E context used lo hi) context used) 0) 2 middle = _
      rw [Func.runFrom_eq]
      change ((program.bb2 core).run (program core).blockParams _ middle >>= fun x =>
        (program core).continue x.1.1 x.1.2 x.2) = _
      rw [hb2]
      rfl
    simpa only [finishState, beforeOutput, ite_eq_right hs, finalOutputState,
      after, prepared, middle, first, marked] using hr

/-- Actual callee invocation and cleanup, with no finalizer or core execution
premise. The exact caller-visible result includes buffer and chaining updates. -/
theorem call (kp context output : Pointer) (state : GlobalState) (used : Nat) (lo hi : Word)
    (h : Ready state context output kp) (hu : used < 128)
    (hc : state.mem.readAt (context.add 200#64) 64 = BitVec.ofNat 64 used)
    (hlo : state.mem.readAt (context.add 208#64) 64 = lo)
    (hhi : state.mem.readAt (context.add 216#64) 64 = hi) :
    (program (Core.program kp).call).call (program.args (.value context) (.value output)) state =
      .value (.cons (.value output) .nil, finishState state context output used lo hi) := by
  have hr := Func.call_of_run (run kp context output state used lo hi h hu hc hlo hhi)
  simpa only [finishState_erase state context output used lo hi h.wf] using hr

end Agave.Ed25519.Bridge.FiredancerSHAExecution.Finish
