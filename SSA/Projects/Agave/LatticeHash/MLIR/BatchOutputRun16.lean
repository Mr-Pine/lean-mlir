/- Released under Apache 2.0 license as described in the file LICENSE. -/
import SSA.Projects.Agave.LatticeHash.MLIR.BatchOutput16Memory
import SSA.Projects.Agave.LatticeHash.MLIR.BatchGuardsRun16
import SSA.Projects.Agave.LatticeHash.MLIR.BatchProof16

namespace AgaveLatticeHash.MLIR.BatchOutputRun16
open LeanMLIR SLLVM Firedancer
open BatchOutput16
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option linter.auxLemma false
noncomputable def input11 (A : agave_batch_16.cfgCtx.Valuation)
    (args : HVector TyDenote.toType (agave_batch_16.cfgSigs[11]'(by decide))) :
    Input11.Valuation := Ctxt.Valuation.ofHVector args.reverse ++ A

attribute [local irreducible] BlockCom.denote Blocks.run

/-- The real output block dispatches after the checked exact reduction/store
specification, preserving the dispatcher continuation. -/
theorem run11_spec (A : agave_batch_16.cfgCtx.Valuation)
    (args : HVector TyDenote.toType (agave_batch_16.cfgSigs[11]'(by decide)))
    (s : GlobalState) :
    StateT.run (agave_batch_16.blocks.run A ⟨11, rfl, args⟩) s =
    StateT.run (output16Spec (input11 A args) >>= BatchGuardsRun16.resume A) s := by
  have h := block11_continue (input11 A args) s (BatchGuardsRun16.resume A)
  denote_enter_block
  dsimp only [input11, BatchGuardsRun16.resume, Blocks.force_limit_next.match_1,
    EffectM, EffectM.instMonad] at h ⊢
  exact h

/-- Exact actual output-block step for a bounded XOF counter and initialized
accumulator chunk, including the final normal-exit edge. -/
theorem run11 (A : agave_batch_16.cfgCtx.Valuation)
    (args : HVector TyDenote.toType (agave_batch_16.cfgSigs[11]'(by decide)))
    (s : GlobalState)
    (counter : Nat) (hc : counter < 32) (ptr : Pointer)
    (old delta : Vector (BitVec 16) 32)
    (hcounter : (input11 A args) ⟨16, rfl⟩ = .value (BitVec.ofNat 64 counter))
    (hshift : (input11 A args) ⟨81, rfl⟩ = .value 6#64)
    (hone : (input11 A args) ⟨110, rfl⟩ = .value 1#64)
    (hend : (input11 A args) ⟨100, rfl⟩ = .value 32#64)
    (hptr : gep ((input11 A args) ⟨162, rfl⟩) 1 0 (.value (BitVec.ofNat 64 (64*counter))) = .value ptr)
    (hdelta : delta16 (input11 A args) = delta.map PoisonOr.value)
    (fit : Fits s.mem ptr 512)
    (read : readWord? ptr 512 s.mem = some (packBits old)) :
    StateT.run (agave_batch_16.blocks.run A ⟨11, rfl, args⟩) s =
    StateT.run (agave_batch_16.blocks.run A
      (if counter = 31 then ⟨12, rfl, .nil⟩
        else next11 (input11 A args) (.value (BitVec.ofNat 64 (counter+1)))))
      {s with mem := s.mem.splice ptr (packBits (sums32 old delta))} := by
  rw [run11_spec]
  have h := output16Spec_run (input11 A args) s counter hc ptr old delta
    hcounter hshift hone hend hptr hdelta fit read
  apply EffectM.run_bind_of_value h

/-- Reaching the actual compiler exit block returns normally with memory
unchanged; no successful-run hypothesis is required. -/
theorem run12 (A : agave_batch_16.cfgCtx.Valuation) (s : GlobalState) :
    StateT.run (agave_batch_16.blocks.run A ⟨12, rfl, .nil⟩) s = .value ([]ₕ, s) := by
  denote_enter_block
  apply EffectM.run_bind_of_value (agave_batch_16_exit A s)

end AgaveLatticeHash.MLIR.BatchOutputRun16
