import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.DispatchExecutionEntry

/-! Concrete dispatcher continuations. External initialization is kept as an
explicit successful effect with its returned Boolean and post-state; no
assumption about CPUID truth is needed. The AVX2 call is the exact imported
call site, ready for the independently verified backend to be linked. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 1800000

namespace Agave.Ed25519.SHA512.Execution.Dispatch
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution

/-- The cold-cache branch executes exactly one initialization primitive. -/
theorem dispatch_cold_step (p : Primitives) (E : Env program.Γ)
    (before after : GlobalState) (enabled : Bool)
    (hi : p.initializeAvx2Cache .nil before =
      .value (.cons (.value (BitVec.ofBool enabled)) .nil, after)) :
    (program.bb1 p).run program.blockParams E before =
      .value ((E[%174 := .value (BitVec.ofBool enabled)],
        .inr (if enabled then 6 else 2)), after) := by
  cases enabled <;>
    simp [BasicBlock.run, program.bb1, List.foldlM_cons, List.foldlM_nil,
      Instr.run, Exit.run, Jump.run, hi, mlir_env, Regs.read_nil,
      Env.writeMany_nil, EffectM.bind_eq, EffectM.pure_eq, mlir_effect]

/-- The cold branch's execution equation retains the initializer's actual
memory effects, rather than assuming initialization was read-only. -/
theorem dispatch_cold_runFrom (p : Primitives) (g : Globals) (E : Env program.Γ)
    (before after : GlobalState) (enabled : Bool)
    (hi : p.initializeAvx2Cache .nil before =
      .value (.cons (.value (BitVec.ofBool enabled)) .nil, after)) :
    (program p g).runFrom E 1 before =
      (program p g).runFrom (E[%174 := .value (BitVec.ofBool enabled)])
        (if enabled then 6 else 2) after := by
  rw [Func.runFrom_eq]
  change ((program.bb1 p).run program.blockParams E before >>= _) = _
  rw [dispatch_cold_step p E before after enabled hi]
  rfl

/-- The final return itself has no memory or allocation effect. -/
theorem dispatch_return (p : Primitives) (g : Globals) (E : Env program.Γ)
    (state : GlobalState) :
    (program p g).runFrom E 7 state = .value (.nil, state) := by
  rw [Func.runFrom_eq]
  rfl

/-- Exact execution of the AVX2 call site and its branch to return. -/
theorem dispatch_avx2_step (p : Primitives) (E : Env program.Γ)
    (before after : GlobalState) (chain data : Pointer) (count : BitVec 64)
    (hchain : E.read (%arg0) = .value chain)
    (hdata : E.read (%arg1) = .value data)
    (hcount : E.read (%arg2) = .value count)
    (hcall : p.avx2Compress (.cons (.value chain) (.cons (.value data)
      (.cons (.value count) .nil))) before = .value (.nil, after)) :
    (program.bb6 p).run program.blockParams E before =
      .value ((E, .inr 7), after) := by
  simp [BasicBlock.run, program.bb6, List.foldlM_cons, List.foldlM_nil,
    Instr.run, Exit.run, Jump.run, hchain, hdata, hcount, hcall,
    mlir_env, Regs.read_nil, Env.writeMany_nil,
    EffectM.bind_eq, EffectM.pure_eq, mlir_effect]

/-- Successful backend execution implies successful dispatcher suffix
execution, with exactly the backend's returned state. -/
theorem dispatch_avx2_runFrom (p : Primitives) (g : Globals) (E : Env program.Γ)
    (before after : GlobalState) (chain data : Pointer) (count : BitVec 64)
    (hchain : E.read (%arg0) = .value chain)
    (hdata : E.read (%arg1) = .value data)
    (hcount : E.read (%arg2) = .value count)
    (hcall : p.avx2Compress (.cons (.value chain) (.cons (.value data)
      (.cons (.value count) .nil))) before = .value (.nil, after)) :
    (program p g).runFrom E 6 before = .value (.nil, after) := by
  rw [Func.runFrom_eq]
  change ((program.bb6 p).run program.blockParams E before >>= _) = _
  rw [dispatch_avx2_step p E before after chain data count hchain hdata hcount hcall]
  exact dispatch_return p g E after

/-- A warm AVX2 invocation is exactly the selected backend invocation;
the dispatcher contributes no writes, allocations, or CPU-feature premise. -/
theorem dispatch_warm_avx2 (p : Primitives) (g : Globals) (E : Env program.Γ)
    (before after : GlobalState) (chain data : Pointer) (count : BitVec 64)
    (hk : SmallRange before.mem g.address1 640)
    (hc : SmallRange before.mem g.address0 1)
    (hr : before.mem.readAt g.address0 8 = 1#8)
    (hchain : E.read (%arg0) = .value chain)
    (hdata : E.read (%arg1) = .value data)
    (hcount : E.read (%arg2) = .value count)
    (hcall : p.avx2Compress (.cons (.value chain) (.cons (.value data)
      (.cons (.value count) .nil))) before = .value (.nil, after)) :
    (program p g).runFrom E 0 before = .value (.nil, after) := by
  rw [dispatch_entry_runFrom p g E before 1 hk hc hr]
  apply dispatch_avx2_runFrom p g _ before after chain data count
  · simpa [dispatchEntryEnv, dispatchChunk0, dispatchChunk1, dispatchChunk2, dispatchChunk3, dispatchChunk4, dispatchChunk5, mlir_env] using hchain
  · simpa [dispatchEntryEnv, dispatchChunk0, dispatchChunk1, dispatchChunk2, dispatchChunk3, dispatchChunk4, dispatchChunk5, mlir_env] using hdata
  · simpa [dispatchEntryEnv, dispatchChunk0, dispatchChunk1, dispatchChunk2, dispatchChunk3, dispatchChunk4, dispatchChunk5, mlir_env] using hcount
  · exact hcall

end Agave.Ed25519.SHA512.Execution.Dispatch
