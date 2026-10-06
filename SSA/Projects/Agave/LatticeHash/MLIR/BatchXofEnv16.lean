import SSA.Projects.Agave.LatticeHash.MLIR.BatchXofLoop16
namespace AgaveLatticeHash.MLIR.BatchXofLoop16
open LeanMLIR SLLVM Firedancer Blake3Compression CompressionRound
open InstCombine (LLVM)
open BatchReduction16
set_option maxHeartbeats 400000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
/-- Captured round constants and pointers depend only on the entry environment. -/
theorem sourceEnv_extras_change (B : agave_batch_16.cfgCtx.Valuation)
    (e e' : HVector TyDenote.toType ExtraTypes)
    (r r' : BitVec 64) (v v' : State Words16) (msg sched : Pointer)
    (h : RoundEnv16 (sourceVal B e r v) msg sched) :
    RoundEnv16 (sourceVal B e' r' v') msg sched := by
  cases e
  rename_i a0x e
  cases e
  rename_i a1x e
  cases e
  rename_i a2x e
  cases e
  rename_i a3x e
  cases e
  rename_i a4x e
  cases e
  rename_i a5x e
  cases e
  rename_i a6x e
  cases e
  rename_i a7x e
  cases e
  rename_i a8x e
  cases e
  rename_i a9x e
  cases e
  rename_i a10x e
  cases e
  cases e'
  rename_i a0y e'
  cases e'
  rename_i a1y e'
  cases e'
  rename_i a2y e'
  cases e'
  rename_i a3y e'
  cases e'
  rename_i a4y e'
  cases e'
  rename_i a5y e'
  cases e'
  rename_i a6y e'
  cases e'
  rename_i a7y e'
  cases e'
  rename_i a8y e'
  cases e'
  rename_i a9y e'
  cases e'
  rename_i a10y e'
  cases e'
  exact ⟨h.msg, h.sched, h.one, h.seven, h.off8, h.off16, h.off24, h.off32,
    h.off40, h.off48, h.off56, h.off64, h.off72, h.off80, h.off88, h.off96,
    h.off104, h.off112, h.off120, h.rot16, h.rot20, h.rot24, h.rot25⟩
end AgaveLatticeHash.MLIR.BatchXofLoop16
