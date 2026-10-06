/- Released under Apache 2.0 license as described in the file LICENSE. -/
import SSA.Projects.Agave.LatticeHash.MLIR.BatchXofScalar16
import SSA.Projects.Agave.LatticeHash.MLIR.BatchXofEnv16

namespace AgaveLatticeHash.MLIR.BatchXofLoop16
open LeanMLIR SLLVM Firedancer Blake3Compression CompressionRound
open InstCombine (LLVM)
open BatchReduction16
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false

/-- The captured round environment is unchanged by the counter or compression state. -/
theorem sourceRound_env (B : agave_batch_16.cfgCtx.Valuation)
    (cv : CV Words16) (len flags : Words16) (msg sched : Pointer)
    (h : RoundEnv16 (sourceVal B (extras cv len flags 0) 0 (rootInitial cv len flags 0)) msg sched)
    (c : Nat) :
    RoundEnv16 (sourceVal B (extras cv len flags c) 0 (rootInitial cv len flags c)) msg sched := by
  exact sourceEnv_extras_change B (extras cv len flags 0) (extras cv len flags c) 0 0
    (rootInitial cv len flags 0) (rootInitial cv len flags c) msg sched h

/-- The actual width16 root XOF loop returns from initial byte-backed memory. -/
theorem xof32_run_initial (B : agave_batch_16.cfgCtx.Valuation)
    (cv : CV Words16) (len flags : Words16) (out msg sched : Pointer)
    (hInit : InitEnv B) (hOut : OutputEnv B out) (s : GlobalState) (m : State Words16)
    (old : Nat → Vector (BitVec 16) 32)
    (hRound : RoundEnv16 (sourceVal B (extras cv len flags 0) 0 (rootInitial cv len flags 0)) msg sched)
    (hMem : InitialMemory s out msg sched m old) :
    StateT.run (agave_batch_16.blocks.run B (rootTarget cv len flags 0)) s =
      .value (.nil, accumulatedState s out cv len flags m old 32) := by
  exact xof32_run B cv len flags out msg sched hInit hOut s m old
    (fun c _ => sourceRound_env B cv len flags msg sched hRound c)
    (fun c hc => hMem.iteration s out msg sched cv len flags m old c hc)

attribute [local irreducible] delta finalState accumulatedState scalarDelta

/-- Actual normal return and all 32 completed accumulator chunk readbacks. -/
theorem xof32_run_readback (B : agave_batch_16.cfgCtx.Valuation)
    (cv : CV Words16) (len flags : Words16) (out msg sched : Pointer)
    (hInit : InitEnv B) (hOut : OutputEnv B out) (s : GlobalState) (m : State Words16)
    (old : Nat → Vector (BitVec 16) 32)
    (hRound : RoundEnv16 (sourceVal B (extras cv len flags 0) 0 (rootInitial cv len flags 0)) msg sched)
    (hMem : InitialMemory s out msg sched m old) :
    ∃ final, StateT.run (agave_batch_16.blocks.run B (rootTarget cv len flags 0)) s = .value (.nil, final) ∧
      ∀ c, c < 32 → readWord? (outputPtr out c) 512 final.mem =
        some (packBits (BatchOutput16.sums32 (old c) (delta cv len flags m c))) := by
  refine ⟨accumulatedState s out cv len flags m old 32,
    xof32_run_initial B cv len flags out msg sched hInit hOut s m old hRound hMem, ?_⟩
  intro c hc
  exact hMem.completed_reads s out msg sched cv len flags m old 32 c (by omega) hc

/-- Direct-MLIR normal return with every stored output chunk equal to its
initial accumulator plus sixteen scalar BLAKE3 contributions, modulo 2^16. -/
theorem xof32_run_scalar_readback (B : agave_batch_16.cfgCtx.Valuation)
    (cv : CV Words16) (len flags : Words16) (out msg sched : Pointer)
    (hInit : InitEnv B) (hOut : OutputEnv B out) (s : GlobalState) (m : State Words16)
    (old : Nat → Vector (BitVec 16) 32)
    (hRound : RoundEnv16 (sourceVal B (extras cv len flags 0) 0 (rootInitial cv len flags 0)) msg sched)
    (hMem : InitialMemory s out msg sched m old) :
    ∃ final, StateT.run (agave_batch_16.blocks.run B (rootTarget cv len flags 0)) s = .value (.nil, final) ∧
      ∀ c, c < 32 → readWord? (outputPtr out c) 512 final.mem =
        some (packBits (BatchOutput16.sums32 (old c) (scalarDelta cv len flags m c))) := by
  obtain ⟨final, hrun, hread⟩ := xof32_run_readback B cv len flags out msg sched hInit hOut s m old hRound hMem
  refine ⟨final, hrun, ?_⟩
  intro c hc
  rw [← delta_eq_scalarDelta cv len flags m c hc]
  exact hread c hc

end AgaveLatticeHash.MLIR.BatchXofLoop16
