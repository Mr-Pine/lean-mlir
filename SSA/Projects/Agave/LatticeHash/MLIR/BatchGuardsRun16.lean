import SSA.Projects.Agave.LatticeHash.MLIR.BatchGuards16
namespace AgaveLatticeHash.MLIR.BatchGuardsRun16
open LeanMLIR SLLVM
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option linter.auxLemma false
noncomputable def input1 (A : agave_batch_16.cfgCtx.Valuation)
    (args : HVector TyDenote.toType (agave_batch_16.cfgSigs[1]'(by decide))) : BatchGuards16.Input1.Valuation :=
  Ctxt.Valuation.ofHVector args.reverse ++ A
/-- Match the dispatcher continuation exactly, keeping recursive execution opaque. -/
noncomputable def resume (A : agave_batch_16.cfgCtx.Valuation)
    (r : HVector TyDenote.toType ([] : List SLLVM.Ty) ⊕ SuccArgs agave_batch_16.cfgSigs) :
    EffectM (HVector TyDenote.toType ([] : List SLLVM.Ty)) :=
  Blocks.force_limit_next.match_1 (fun _ => EffectM (HVector TyDenote.toType ([] : List SLLVM.Ty))) r
    (fun rets => pure rets) (fun next => agave_batch_16.blocks.run A next)

attribute [local irreducible] BlockCom.denote Blocks.run

/-- The fifteen actual guard checks all pass and select exactly block 2. -/
theorem run1 (A : agave_batch_16.cfgCtx.Valuation)
    (args : HVector TyDenote.toType (agave_batch_16.cfgSigs[1]'(by decide)))
    (s : GlobalState) (offsets : Vector (BitVec 64) 15)
    (hV : BatchGuards16.Env1 (input1 A args) offsets)
    (hb : ∀ i : Fin 15, offsets[i].toNat ≤ 960) :
    StateT.run (agave_batch_16.blocks.run A ⟨1, rfl, args⟩) s =
      StateT.run (agave_batch_16.blocks.run A (BatchGuards16.next1 (input1 A args))) s := by
  have h := BatchGuards16.block1_continue (α := HVector TyDenote.toType ([] : List SLLVM.Ty))
    (input1 A args) s offsets hV hb (resume A)
  denote_enter_block
  dsimp only [input1, resume, Blocks.force_limit_next.match_1, EffectM, EffectM.instMonad] at h ⊢
  exact h
end AgaveLatticeHash.MLIR.BatchGuardsRun16
