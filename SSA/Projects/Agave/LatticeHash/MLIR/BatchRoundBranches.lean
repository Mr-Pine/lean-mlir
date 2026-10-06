/- Released under Apache 2.0 license as described in the file LICENSE. -/
import SSA.Projects.Agave.LatticeHash.MLIR.BatchRounds
import SSA.Projects.Agave.LatticeHash.MLIR.BatchRoundAdapters8
import SSA.Projects.Agave.LatticeHash.MLIR.BatchRoundBranchSupport
import SSA.Projects.Agave.LatticeHash.MLIR.BatchRoundLookups8

namespace AgaveLatticeHash.MLIR.BatchRoundBranches
open LeanMLIR SLLVM BatchRounds
set_option maxRecDepth 8192
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

def sourceTrue8 : Target sourceParts8.middle agave_compress_pre_8.cfgSigs :=
  ⟨1, rfl, (⟨72, rfl⟩ ::ₕ ⟨70, rfl⟩ ::ₕ ⟨69, rfl⟩ ::ₕ ⟨67, rfl⟩ ::ₕ ⟨50, rfl⟩ ::ₕ ⟨48, rfl⟩ ::ₕ ⟨47, rfl⟩ ::ₕ ⟨45, rfl⟩ ::ₕ ⟨28, rfl⟩ ::ₕ ⟨26, rfl⟩ ::ₕ ⟨25, rfl⟩ ::ₕ ⟨23, rfl⟩ ::ₕ ⟨6, rfl⟩ ::ₕ ⟨4, rfl⟩ ::ₕ ⟨3, rfl⟩ ::ₕ ⟨1, rfl⟩ ::ₕ .nil)⟩

def sourceFalse8 : Target sourceParts8.middle agave_compress_pre_8.cfgSigs :=
  ⟨0, rfl, (⟨177, rfl⟩ ::ₕ ⟨72, rfl⟩ ::ₕ ⟨50, rfl⟩ ::ₕ ⟨28, rfl⟩ ::ₕ ⟨6, rfl⟩ ::ₕ ⟨1, rfl⟩ ::ₕ ⟨67, rfl⟩ ::ₕ ⟨45, rfl⟩ ::ₕ ⟨23, rfl⟩ ::ₕ ⟨25, rfl⟩ ::ₕ ⟨3, rfl⟩ ::ₕ ⟨69, rfl⟩ ::ₕ ⟨47, rfl⟩ ::ₕ ⟨48, rfl⟩ ::ₕ ⟨26, rfl⟩ ::ₕ ⟨4, rfl⟩ ::ₕ ⟨70, rfl⟩ ::ₕ .nil)⟩

theorem sourceTail8_eq : sourceParts8.tail =
    .term (.condBr ⟨0, rfl⟩ sourceTrue8 sourceFalse8) := rfl

def true8_20 : Target parts8_20.middle agave_batch_8.cfgSigs :=
  ⟨21, rfl, (⟨188, rfl⟩ ::ₕ ⟨187, rfl⟩ ::ₕ ⟨186, rfl⟩ ::ₕ ⟨185, rfl⟩ ::ₕ ⟨184, rfl⟩ ::ₕ ⟨183, rfl⟩ ::ₕ ⟨182, rfl⟩ ::ₕ ⟨181, rfl⟩ ::ₕ ⟨180, rfl⟩ ::ₕ ⟨179, rfl⟩ ::ₕ ⟨178, rfl⟩ ::ₕ ⟨72, rfl⟩ ::ₕ ⟨70, rfl⟩ ::ₕ ⟨69, rfl⟩ ::ₕ ⟨67, rfl⟩ ::ₕ ⟨50, rfl⟩ ::ₕ ⟨48, rfl⟩ ::ₕ ⟨47, rfl⟩ ::ₕ ⟨45, rfl⟩ ::ₕ ⟨28, rfl⟩ ::ₕ ⟨26, rfl⟩ ::ₕ ⟨25, rfl⟩ ::ₕ ⟨23, rfl⟩ ::ₕ ⟨6, rfl⟩ ::ₕ ⟨4, rfl⟩ ::ₕ ⟨3, rfl⟩ ::ₕ ⟨1, rfl⟩ ::ₕ .nil)⟩

def false8_20 : Target parts8_20.middle agave_batch_8.cfgSigs :=
  ⟨20, rfl, (⟨177, rfl⟩ ::ₕ ⟨72, rfl⟩ ::ₕ ⟨50, rfl⟩ ::ₕ ⟨28, rfl⟩ ::ₕ ⟨6, rfl⟩ ::ₕ ⟨1, rfl⟩ ::ₕ ⟨67, rfl⟩ ::ₕ ⟨45, rfl⟩ ::ₕ ⟨23, rfl⟩ ::ₕ ⟨25, rfl⟩ ::ₕ ⟨3, rfl⟩ ::ₕ ⟨69, rfl⟩ ::ₕ ⟨47, rfl⟩ ::ₕ ⟨48, rfl⟩ ::ₕ ⟨26, rfl⟩ ::ₕ ⟨4, rfl⟩ ::ₕ ⟨70, rfl⟩ ::ₕ ⟨188, rfl⟩ ::ₕ ⟨187, rfl⟩ ::ₕ ⟨186, rfl⟩ ::ₕ ⟨185, rfl⟩ ::ₕ ⟨184, rfl⟩ ::ₕ ⟨183, rfl⟩ ::ₕ ⟨182, rfl⟩ ::ₕ ⟨181, rfl⟩ ::ₕ ⟨180, rfl⟩ ::ₕ ⟨179, rfl⟩ ::ₕ ⟨178, rfl⟩ ::ₕ .nil)⟩

theorem tail8_20_eq : parts8_20.tail =
    .term (.condBr ⟨0, rfl⟩ true8_20 false8_20) := rfl

/-- The actual branch transports both newly computed registers and all
live caller values; its condition retains the original poison behavior. -/
theorem tail8_20_continue {α : Type} (W : parts8_20.middle.Valuation)
    (K : (HVector TyDenote.toType ([] : List SLLVM.Ty) ⊕
      SuccArgs agave_batch_8.cfgSigs) → EffectM α) :
    (parts8_20.tail.denote W >>= fun r => K r.2) =
      (sourceParts8.tail.denote (W.comap finalMap8_20) >>= fun r =>
        K (r.2.map id (adapt8_20 (W.comap prefix8_20.contextHom)))) := by
  rw [tail8_20_eq, sourceTail8_eq]
  rw [BlockCom.denote_term, BlockCom.denote_term]
  simp only [bind_assoc, pure_bind]
  change (Terminator.denote (.condBr ⟨0, rfl⟩ true8_20 false8_20) W >>= K) =
    (Terminator.denote (.condBr ⟨0, rfl⟩ sourceTrue8 sourceFalse8)
      (W.comap finalMap8_20) >>= fun r =>
        K (r.map id (adapt8_20 (W.comap prefix8_20.contextHom))))
  exact condBr_transport (W.comap finalMap8_20) W ⟨0, rfl⟩ ⟨0, rfl⟩
    sourceTrue8 sourceFalse8 true8_20 false8_20
    (adapt8_20 (W.comap prefix8_20.contextHom)) (by rfl)
    (by simp only [sourceTrue8, true8_20, Target.denote, HVector.map, adapt8_20_exit, extras8_20, Ctxt.Valuation.comap, HVector.append, finalMap8_20_at1, finalMap8_20_at3, finalMap8_20_at4, finalMap8_20_at6, finalMap8_20_at23, finalMap8_20_at25, finalMap8_20_at26, finalMap8_20_at28, finalMap8_20_at45, finalMap8_20_at47, finalMap8_20_at48, finalMap8_20_at50, finalMap8_20_at67, finalMap8_20_at69, finalMap8_20_at70, finalMap8_20_at72, origin8_20_at0, origin8_20_at1, origin8_20_at2, origin8_20_at3, origin8_20_at4, origin8_20_at5, origin8_20_at6, origin8_20_at7, origin8_20_at8, origin8_20_at9, origin8_20_at10])
    (by simp only [sourceFalse8, false8_20, Target.denote, HVector.map, adapt8_20_loop, extras8_20, Ctxt.Valuation.comap, HVector.append, finalMap8_20_at1, finalMap8_20_at3, finalMap8_20_at4, finalMap8_20_at6, finalMap8_20_at23, finalMap8_20_at25, finalMap8_20_at26, finalMap8_20_at28, finalMap8_20_at45, finalMap8_20_at47, finalMap8_20_at48, finalMap8_20_at50, finalMap8_20_at67, finalMap8_20_at69, finalMap8_20_at70, finalMap8_20_at72, finalMap8_20_at177, origin8_20_at0, origin8_20_at1, origin8_20_at2, origin8_20_at3, origin8_20_at4, origin8_20_at5, origin8_20_at6, origin8_20_at7, origin8_20_at8, origin8_20_at9, origin8_20_at10]) K

def true8_23 : Target parts8_23.middle agave_batch_8.cfgSigs :=
  ⟨24, rfl, (⟨197, rfl⟩ ::ₕ ⟨196, rfl⟩ ::ₕ ⟨195, rfl⟩ ::ₕ ⟨194, rfl⟩ ::ₕ ⟨193, rfl⟩ ::ₕ ⟨192, rfl⟩ ::ₕ ⟨191, rfl⟩ ::ₕ ⟨190, rfl⟩ ::ₕ ⟨189, rfl⟩ ::ₕ ⟨188, rfl⟩ ::ₕ ⟨187, rfl⟩ ::ₕ ⟨186, rfl⟩ ::ₕ ⟨185, rfl⟩ ::ₕ ⟨184, rfl⟩ ::ₕ ⟨183, rfl⟩ ::ₕ ⟨182, rfl⟩ ::ₕ ⟨181, rfl⟩ ::ₕ ⟨180, rfl⟩ ::ₕ ⟨179, rfl⟩ ::ₕ ⟨178, rfl⟩ ::ₕ ⟨72, rfl⟩ ::ₕ ⟨70, rfl⟩ ::ₕ ⟨69, rfl⟩ ::ₕ ⟨67, rfl⟩ ::ₕ ⟨50, rfl⟩ ::ₕ ⟨48, rfl⟩ ::ₕ ⟨47, rfl⟩ ::ₕ ⟨45, rfl⟩ ::ₕ ⟨28, rfl⟩ ::ₕ ⟨26, rfl⟩ ::ₕ ⟨25, rfl⟩ ::ₕ ⟨23, rfl⟩ ::ₕ ⟨6, rfl⟩ ::ₕ ⟨4, rfl⟩ ::ₕ ⟨3, rfl⟩ ::ₕ ⟨1, rfl⟩ ::ₕ .nil)⟩

def false8_23 : Target parts8_23.middle agave_batch_8.cfgSigs :=
  ⟨23, rfl, (⟨177, rfl⟩ ::ₕ ⟨72, rfl⟩ ::ₕ ⟨50, rfl⟩ ::ₕ ⟨28, rfl⟩ ::ₕ ⟨6, rfl⟩ ::ₕ ⟨1, rfl⟩ ::ₕ ⟨67, rfl⟩ ::ₕ ⟨45, rfl⟩ ::ₕ ⟨23, rfl⟩ ::ₕ ⟨25, rfl⟩ ::ₕ ⟨3, rfl⟩ ::ₕ ⟨69, rfl⟩ ::ₕ ⟨47, rfl⟩ ::ₕ ⟨48, rfl⟩ ::ₕ ⟨26, rfl⟩ ::ₕ ⟨4, rfl⟩ ::ₕ ⟨70, rfl⟩ ::ₕ ⟨197, rfl⟩ ::ₕ ⟨196, rfl⟩ ::ₕ ⟨195, rfl⟩ ::ₕ ⟨194, rfl⟩ ::ₕ ⟨193, rfl⟩ ::ₕ ⟨192, rfl⟩ ::ₕ ⟨191, rfl⟩ ::ₕ ⟨190, rfl⟩ ::ₕ ⟨189, rfl⟩ ::ₕ ⟨188, rfl⟩ ::ₕ ⟨187, rfl⟩ ::ₕ ⟨186, rfl⟩ ::ₕ ⟨185, rfl⟩ ::ₕ ⟨184, rfl⟩ ::ₕ ⟨183, rfl⟩ ::ₕ ⟨182, rfl⟩ ::ₕ ⟨181, rfl⟩ ::ₕ ⟨180, rfl⟩ ::ₕ ⟨179, rfl⟩ ::ₕ ⟨178, rfl⟩ ::ₕ .nil)⟩

theorem tail8_23_eq : parts8_23.tail =
    .term (.condBr ⟨0, rfl⟩ true8_23 false8_23) := rfl

/-- The actual branch transports both newly computed registers and all
live caller values; its condition retains the original poison behavior. -/
theorem tail8_23_continue {α : Type} (W : parts8_23.middle.Valuation)
    (K : (HVector TyDenote.toType ([] : List SLLVM.Ty) ⊕
      SuccArgs agave_batch_8.cfgSigs) → EffectM α) :
    (parts8_23.tail.denote W >>= fun r => K r.2) =
      (sourceParts8.tail.denote (W.comap finalMap8_23) >>= fun r =>
        K (r.2.map id (adapt8_23 (W.comap prefix8_23.contextHom)))) := by
  rw [tail8_23_eq, sourceTail8_eq]
  rw [BlockCom.denote_term, BlockCom.denote_term]
  simp only [bind_assoc, pure_bind]
  change (Terminator.denote (.condBr ⟨0, rfl⟩ true8_23 false8_23) W >>= K) =
    (Terminator.denote (.condBr ⟨0, rfl⟩ sourceTrue8 sourceFalse8)
      (W.comap finalMap8_23) >>= fun r =>
        K (r.map id (adapt8_23 (W.comap prefix8_23.contextHom))))
  exact condBr_transport (W.comap finalMap8_23) W ⟨0, rfl⟩ ⟨0, rfl⟩
    sourceTrue8 sourceFalse8 true8_23 false8_23
    (adapt8_23 (W.comap prefix8_23.contextHom)) (by rfl)
    (by simp only [sourceTrue8, true8_23, Target.denote, HVector.map, adapt8_23_exit, extras8_23, Ctxt.Valuation.comap, HVector.append, finalMap8_23_at1, finalMap8_23_at3, finalMap8_23_at4, finalMap8_23_at6, finalMap8_23_at23, finalMap8_23_at25, finalMap8_23_at26, finalMap8_23_at28, finalMap8_23_at45, finalMap8_23_at47, finalMap8_23_at48, finalMap8_23_at50, finalMap8_23_at67, finalMap8_23_at69, finalMap8_23_at70, finalMap8_23_at72, origin8_23_at0, origin8_23_at1, origin8_23_at2, origin8_23_at3, origin8_23_at4, origin8_23_at5, origin8_23_at6, origin8_23_at7, origin8_23_at8, origin8_23_at9, origin8_23_at10, origin8_23_at11, origin8_23_at12, origin8_23_at13, origin8_23_at14, origin8_23_at15, origin8_23_at16, origin8_23_at17, origin8_23_at18, origin8_23_at19])
    (by simp only [sourceFalse8, false8_23, Target.denote, HVector.map, adapt8_23_loop, extras8_23, Ctxt.Valuation.comap, HVector.append, finalMap8_23_at1, finalMap8_23_at3, finalMap8_23_at4, finalMap8_23_at6, finalMap8_23_at23, finalMap8_23_at25, finalMap8_23_at26, finalMap8_23_at28, finalMap8_23_at45, finalMap8_23_at47, finalMap8_23_at48, finalMap8_23_at50, finalMap8_23_at67, finalMap8_23_at69, finalMap8_23_at70, finalMap8_23_at72, finalMap8_23_at177, origin8_23_at0, origin8_23_at1, origin8_23_at2, origin8_23_at3, origin8_23_at4, origin8_23_at5, origin8_23_at6, origin8_23_at7, origin8_23_at8, origin8_23_at9, origin8_23_at10, origin8_23_at11, origin8_23_at12, origin8_23_at13, origin8_23_at14, origin8_23_at15, origin8_23_at16, origin8_23_at17, origin8_23_at18, origin8_23_at19]) K

/-- Execute the actual inlined round block using any standalone round
continuation; all additional batch loop values are retained by the adapter. -/
theorem block8_20_transport {α : Type} (V : Input8_20.Valuation)
    (K : (HVector TyDenote.toType ([] : List SLLVM.Ty) ⊕
      SuccArgs agave_batch_8.cfgSigs) → EffectM α) :
    (agave_batch_8.cfgBlock_20.denote V >>= fun r => K r.2) =
      (agave_compress_pre_8.cfgBlock_0.denote (V.comap rename8_20) >>= fun r =>
        K (r.2.map id (adapt8_20 V))) :=
  BatchRounds.block8_20_continue V K
    (fun U r => K (r.map id (adapt8_20 U))) (fun W => tail8_20_continue W K)

/-- Execute the actual inlined round block using any standalone round
continuation; all additional batch loop values are retained by the adapter. -/
theorem block8_23_transport {α : Type} (V : Input8_23.Valuation)
    (K : (HVector TyDenote.toType ([] : List SLLVM.Ty) ⊕
      SuccArgs agave_batch_8.cfgSigs) → EffectM α) :
    (agave_batch_8.cfgBlock_23.denote V >>= fun r => K r.2) =
      (agave_compress_pre_8.cfgBlock_0.denote (V.comap rename8_23) >>= fun r =>
        K (r.2.map id (adapt8_23 V))) :=
  BatchRounds.block8_23_continue V K
    (fun U r => K (r.map id (adapt8_23 U))) (fun W => tail8_23_continue W K)

end AgaveLatticeHash.MLIR.BatchRoundBranches
