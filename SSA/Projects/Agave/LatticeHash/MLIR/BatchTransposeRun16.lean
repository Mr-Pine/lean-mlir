/- Released under Apache 2.0 license as described in the file LICENSE. -/
import SSA.Projects.Agave.LatticeHash.MLIR.BatchTranspose16
import SSA.Projects.Agave.LatticeHash.MLIR.BatchGuardsRun16
namespace AgaveLatticeHash.MLIR.BatchTransposeRun16
open LeanMLIR SLLVM Firedancer Blake3Compression
open BatchTranspose16 CompressionExit

noncomputable def input2 (A : agave_batch_16.cfgCtx.Valuation)
    (args : HVector TyDenote.toType (agave_batch_16.cfgSigs[2]'(by decide))) : InCtx16.Valuation :=
  Ctxt.Valuation.ofHVector args.reverse ++ A

attribute [local irreducible] BlockCom.denote Blocks.run

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
/-- One actual dispatcher transition performs all source loads and scratch stores
and selects the root or nonroot successor from the frozen activity mask. -/
theorem run2 (A : agave_batch_16.cfgCtx.Valuation)
    (args : HVector TyDenote.toType (agave_batch_16.cfgSigs[2]'(by decide)))
    (out : Pointer) (inputs : Fin 16 → Pointer) (rows : Vector (Vector Word 16) 16)
    (mask : BitVec 16) (s : GlobalState)
    (hV : Env16 (input2 A args) out inputs mask)
    (hf : ∀ i, Fits s.mem (inputs i) 512)
    (hr : ∀ i, readWord? (inputs i) 512 s.mem = some (packBits rows[i]))
    (hfit : ∀ k < 16, Fits s.mem (out.withOffset (BitVec.ofNat 64 (64*k))) 512) :
    StateT.run (agave_batch_16.blocks.run A ⟨2, rfl, args⟩) s =
      StateT.run (agave_batch_16.blocks.run A
        (if mask = 0 then rootTarget16 (input2 A args) else nonrootTarget16 (input2 A args)))
        {s with mem := outputMem out (columns16 rows) 16 s.mem} := by
  obtain ⟨V', hv⟩ := transpose16_run (input2 A args) out inputs rows mask hV s hf hr hfit
  denote_enter_block
  change StateT.run (do
    let (_, r) ← agave_batch_16.cfgBlock_2.denote (input2 A args)
    BatchGuardsRun16.resume A r) s = _
  rw [EffectM.run_bind, hv]
  rfl

end AgaveLatticeHash.MLIR.BatchTransposeRun16
