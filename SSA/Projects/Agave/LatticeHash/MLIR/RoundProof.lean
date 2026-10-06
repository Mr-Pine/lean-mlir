import SSA.Projects.Agave.LatticeHash.MLIR.RoundCore

namespace AgaveLatticeHash.MLIR.CompressionRound
open LeanMLIR SLLVM Firedancer
open InstCombine (LLVM)
open Blake3Compression

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
/-- The reusable block theorem instantiated with the actual CFG continuation. -/
theorem round8_run (V : agave_compress_pre_8.cfgCtx.Valuation)
    (msg sched : Pointer) (hV : RoundEnv8 V msg sched) (s : GlobalState)
    (r : Fin 7) (v m : State (Vector Word 8))
    (hsi : ∀ i, Fits s.mem (schedulePtr sched r i) 64)
    (hsv : ∀ i, readWord? (schedulePtr sched r i) 64 s.mem =
      some (BitVec.ofNat 64 (schedule r i).val))
    (hmi : ∀ i, Fits s.mem (messagePtr8 msg i) 256)
    (hmv : ∀ i, readWord? (messagePtr8 msg i) 256 s.mem = some (packBits (m i))) :
    StateT.run (agave_compress_pre_8.blocks.run V (headerAt8 (BitVec.ofNat 64 r.val) v)) s =
    StateT.run (agave_compress_pre_8.blocks.run V
      (if r.val = 6 then exitAt8 (roundFn gVectors v m r)
       else headerAt8 (BitVec.ofNat 64 (r.val+1)) (roundFn gVectors v m r))) s := by
  have h := round8_cont_run (α := HVector toType ([] : List SLLVM.Ty)) (fun t => match t with
    | .inl rets => pure rets
    | .inr next => agave_compress_pre_8.blocks.run V next)
    V msg sched hV s r v m hsi hsv hmi hmv
  conv_lhs =>
    rw [Blocks.run_step]
    simp only [agave_compress_pre_8, agave_compress_pre_8.cfgBlocks, Blocks.get]
  convert h using 1
  simp only [EffectM.run_bind, headerAt8, agave_compress_pre_8, agave_compress_pre_8.cfgBlocks]
  simp only [simp_spine]
  congr 1
  funext p
  rcases p with ⟨⟨Vout, t⟩, sNext⟩
  cases t <;> rfl

end AgaveLatticeHash.MLIR.CompressionRound
