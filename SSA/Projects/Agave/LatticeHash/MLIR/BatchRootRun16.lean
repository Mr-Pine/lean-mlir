/- Released under Apache 2.0 license as described in the file LICENSE. -/
import SSA.Projects.Agave.LatticeHash.MLIR.BatchRootCopy16
import SSA.Projects.Agave.LatticeHash.MLIR.BatchGuardsRun16

namespace AgaveLatticeHash.MLIR.BatchRootRun16
open LeanMLIR SLLVM Firedancer
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
noncomputable def input5 (A : agave_batch_16.cfgCtx.Valuation)
    (args : HVector TyDenote.toType (agave_batch_16.cfgSigs[5]'(by decide))) :
    BatchRootCopy16.Input5.Valuation := Ctxt.Valuation.ofHVector args.reverse ++ A

attribute [local irreducible] BlockCom.denote Blocks.run

/-- Execute the actual root-copy block inside the compiled CFG dispatcher,
retaining the exact continuation payload and destination-memory splice. -/
theorem run5 (A : agave_batch_16.cfgCtx.Valuation)
    (args : HVector TyDenote.toType (agave_batch_16.cfgSigs[5]'(by decide)))
    (s : GlobalState) (src dst : Pointer) (bytes : BitVec 8192)
    (hsrc : input5 A args ⟨44, rfl⟩ = PoisonOr.value src)
    (hdst : input5 A args ⟨43, rfl⟩ = PoisonOr.value dst)
    (hlen : input5 A args ⟨143, rfl⟩ = PoisonOr.value 1024#64)
    (fsrc : Fits s.mem src 8192) (fdst : Fits s.mem dst 8192)
    (hread : readWord? src 8192 s.mem = some bytes) :
    StateT.run (agave_batch_16.blocks.run A ⟨5, rfl, args⟩) s =
    StateT.run (agave_batch_16.blocks.run A (BatchRootCopy16.next5 (input5 A args)))
      {s with mem := s.mem.splice dst bytes} := by
  have h := BatchRootCopy16.block5_continue (input5 A args) s src dst bytes
    hsrc hdst hlen fsrc fdst hread (BatchGuardsRun16.resume A)
  denote_enter_block
  dsimp only [input5, BatchGuardsRun16.resume, Blocks.force_limit_next.match_1,
    EffectM, EffectM.instMonad] at h ⊢
  exact h

end AgaveLatticeHash.MLIR.BatchRootRun16
