/- Released under Apache 2.0 license as described in the file LICENSE. -/
import SSA.Projects.Agave.LatticeHash.MLIR.BatchSecondHalf

namespace AgaveLatticeHash.MLIR.BatchFieldForward
open LeanMLIR SLLVM
open InstCombine (LLVM)

noncomputable def afterSecond (A : agave_batch_8.cfgCtx.Valuation)
    (args : HVector TyDenote.toType (agave_batch_8.cfgSigs[2]'(by decide)))
    (rows : Fin 6 → Vector (BitVec 32) 8) : BatchTranspose.InCtx8.Valuation :=
  Ctxt.Valuation.ofHVector (BatchLoads.next8 (BatchSecondLoadPath.input8 A
    (BatchSecondLoadPath.args8 A args rows))).args.reverse ++ A

set_option maxRecDepth 4096 in
theorem second_mask (A : agave_batch_8.cfgCtx.Valuation)
    (args : HVector TyDenote.toType (agave_batch_8.cfgSigs[2]'(by decide)))
    (rows : Fin 6 → Vector (BitVec 32) 8) :
    afterSecond A args rows ⟨18, rfl⟩ = BatchSecondLoadPath.input2 A args ⟨25, rfl⟩ := by rfl

theorem first_transpose_mask (A : agave_batch_8.cfgCtx.Valuation)
    (V : BatchFirstTranspose.InCtx8.Valuation) (cols : Vector BatchTranspose.Row8 8)
    (off : LLVM.IntW 64) :
    BatchSecondLoadPath.input2 A (BatchFirstTranspose.next8 V cols off).args ⟨25, rfl⟩ =
      V ⟨24, rfl⟩ := by rfl

set_option maxRecDepth 4096 in
theorem first_mask (A : agave_batch_8.cfgCtx.Valuation)
    (args : HVector TyDenote.toType (agave_batch_8.cfgSigs[10]'(by decide)))
    (rows : Fin 6 → Vector (BitVec 32) 8) :
    BatchFirstHalf.firstTransposeInput A (BatchLoadPath.args16 A args rows) ⟨24, rfl⟩ =
      BatchLoadPath.input10 A args ⟨18, rfl⟩ := by rfl

theorem header_mask (A : agave_batch_8.cfgCtx.Valuation) (W : Header8Ctx.Valuation) :
    BatchLoadPath.input10 A (BatchHeader.next8 W).args ⟨18, rfl⟩ =
      BatchHeader.values8 W ⟨24, rfl⟩ := by rfl

noncomputable def beforeFirst (A : agave_batch_8.cfgCtx.Valuation) (W : Header8Ctx.Valuation)
    (lo : Vector (Vector (BitVec 32) 8) 8) : BatchFirstTranspose.InCtx8.Valuation :=
  BatchFirstHalf.firstTransposeInput A (BatchLoadPath.args16 A (BatchHeader.next8 W).args (BatchFirstHalf.firstRows lo))

noncomputable def afterAll (A : agave_batch_8.cfgCtx.Valuation) (W : Header8Ctx.Valuation)
    (lo hi : Vector (Vector (BitVec 32) 8) 8) : BatchTranspose.InCtx8.Valuation :=
  afterSecond A (BatchFirstTranspose.next8 (beforeFirst A W lo)
    (BatchFirstTranspose.transposeRows8 (lo.map (·.map PoisonOr.value)))
    (BatchFirstTranspose.nextOffset8 (beforeFirst A W lo))).args (BatchFirstHalf.firstRows hi)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
theorem all_mask (A : agave_batch_8.cfgCtx.Valuation) (W : Header8Ctx.Valuation)
    (lo hi : Vector (Vector (BitVec 32) 8) 8) :
    afterAll A W lo hi ⟨18, rfl⟩ = BatchHeader.values8 W ⟨24, rfl⟩ := by
  rfl

end AgaveLatticeHash.MLIR.BatchFieldForward
