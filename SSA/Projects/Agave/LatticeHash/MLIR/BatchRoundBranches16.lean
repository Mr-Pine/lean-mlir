/- Released under Apache 2.0 license as described in the file LICENSE. -/
import SSA.Projects.Agave.LatticeHash.MLIR.BatchRounds
import SSA.Projects.Agave.LatticeHash.MLIR.BatchRoundAdapters16
import SSA.Projects.Agave.LatticeHash.MLIR.BatchRoundLookups16
import SSA.Projects.Agave.LatticeHash.MLIR.BatchRoundBranchSupport

namespace AgaveLatticeHash.MLIR.BatchRoundBranches
open LeanMLIR SLLVM
open BatchRounds (sourceParts16 parts16_7 parts16_10 finalMap16_7 finalMap16_10 prefix16_7 prefix16_10)
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

def sourceTrue16 : Target sourceParts16.middle agave_compress_pre_16.cfgSigs :=
  ⟨1, rfl, (⟨72, rfl⟩ ::ₕ
    ⟨70, rfl⟩ ::ₕ
    ⟨69, rfl⟩ ::ₕ
    ⟨67, rfl⟩ ::ₕ
    ⟨50, rfl⟩ ::ₕ
    ⟨48, rfl⟩ ::ₕ
    ⟨47, rfl⟩ ::ₕ
    ⟨45, rfl⟩ ::ₕ
    ⟨28, rfl⟩ ::ₕ
    ⟨26, rfl⟩ ::ₕ
    ⟨25, rfl⟩ ::ₕ
    ⟨23, rfl⟩ ::ₕ
    ⟨6, rfl⟩ ::ₕ
    ⟨4, rfl⟩ ::ₕ
    ⟨3, rfl⟩ ::ₕ
    ⟨1, rfl⟩ ::ₕ .nil)⟩

def sourceFalse16 : Target sourceParts16.middle agave_compress_pre_16.cfgSigs :=
  ⟨0, rfl, (⟨177, rfl⟩ ::ₕ
    ⟨72, rfl⟩ ::ₕ
    ⟨50, rfl⟩ ::ₕ
    ⟨28, rfl⟩ ::ₕ
    ⟨6, rfl⟩ ::ₕ
    ⟨1, rfl⟩ ::ₕ
    ⟨67, rfl⟩ ::ₕ
    ⟨45, rfl⟩ ::ₕ
    ⟨23, rfl⟩ ::ₕ
    ⟨25, rfl⟩ ::ₕ
    ⟨3, rfl⟩ ::ₕ
    ⟨69, rfl⟩ ::ₕ
    ⟨47, rfl⟩ ::ₕ
    ⟨48, rfl⟩ ::ₕ
    ⟨26, rfl⟩ ::ₕ
    ⟨4, rfl⟩ ::ₕ
    ⟨70, rfl⟩ ::ₕ .nil)⟩

theorem sourceTail16_eq : sourceParts16.tail =
    .term (.condBr ⟨0, rfl⟩ sourceTrue16 sourceFalse16) := by rfl

def true16_7 : Target parts16_7.middle agave_batch_16.cfgSigs :=
  ⟨8, rfl, (⟨204, rfl⟩ ::ₕ
    ⟨203, rfl⟩ ::ₕ
    ⟨202, rfl⟩ ::ₕ
    ⟨201, rfl⟩ ::ₕ
    ⟨200, rfl⟩ ::ₕ
    ⟨199, rfl⟩ ::ₕ
    ⟨198, rfl⟩ ::ₕ
    ⟨197, rfl⟩ ::ₕ
    ⟨196, rfl⟩ ::ₕ
    ⟨195, rfl⟩ ::ₕ
    ⟨194, rfl⟩ ::ₕ
    ⟨193, rfl⟩ ::ₕ
    ⟨192, rfl⟩ ::ₕ
    ⟨191, rfl⟩ ::ₕ
    ⟨190, rfl⟩ ::ₕ
    ⟨189, rfl⟩ ::ₕ
    ⟨188, rfl⟩ ::ₕ
    ⟨187, rfl⟩ ::ₕ
    ⟨186, rfl⟩ ::ₕ
    ⟨185, rfl⟩ ::ₕ
    ⟨184, rfl⟩ ::ₕ
    ⟨183, rfl⟩ ::ₕ
    ⟨182, rfl⟩ ::ₕ
    ⟨181, rfl⟩ ::ₕ
    ⟨180, rfl⟩ ::ₕ
    ⟨179, rfl⟩ ::ₕ
    ⟨178, rfl⟩ ::ₕ
    ⟨72, rfl⟩ ::ₕ
    ⟨70, rfl⟩ ::ₕ
    ⟨69, rfl⟩ ::ₕ
    ⟨67, rfl⟩ ::ₕ
    ⟨50, rfl⟩ ::ₕ
    ⟨48, rfl⟩ ::ₕ
    ⟨47, rfl⟩ ::ₕ
    ⟨45, rfl⟩ ::ₕ
    ⟨28, rfl⟩ ::ₕ
    ⟨26, rfl⟩ ::ₕ
    ⟨25, rfl⟩ ::ₕ
    ⟨23, rfl⟩ ::ₕ
    ⟨6, rfl⟩ ::ₕ
    ⟨4, rfl⟩ ::ₕ
    ⟨3, rfl⟩ ::ₕ
    ⟨1, rfl⟩ ::ₕ .nil)⟩

def false16_7 : Target parts16_7.middle agave_batch_16.cfgSigs :=
  ⟨7, rfl, (⟨177, rfl⟩ ::ₕ
    ⟨72, rfl⟩ ::ₕ
    ⟨50, rfl⟩ ::ₕ
    ⟨28, rfl⟩ ::ₕ
    ⟨6, rfl⟩ ::ₕ
    ⟨1, rfl⟩ ::ₕ
    ⟨67, rfl⟩ ::ₕ
    ⟨45, rfl⟩ ::ₕ
    ⟨23, rfl⟩ ::ₕ
    ⟨25, rfl⟩ ::ₕ
    ⟨3, rfl⟩ ::ₕ
    ⟨69, rfl⟩ ::ₕ
    ⟨47, rfl⟩ ::ₕ
    ⟨48, rfl⟩ ::ₕ
    ⟨26, rfl⟩ ::ₕ
    ⟨4, rfl⟩ ::ₕ
    ⟨70, rfl⟩ ::ₕ
    ⟨204, rfl⟩ ::ₕ
    ⟨203, rfl⟩ ::ₕ
    ⟨202, rfl⟩ ::ₕ
    ⟨201, rfl⟩ ::ₕ
    ⟨200, rfl⟩ ::ₕ
    ⟨199, rfl⟩ ::ₕ
    ⟨198, rfl⟩ ::ₕ
    ⟨197, rfl⟩ ::ₕ
    ⟨196, rfl⟩ ::ₕ
    ⟨195, rfl⟩ ::ₕ
    ⟨194, rfl⟩ ::ₕ
    ⟨193, rfl⟩ ::ₕ
    ⟨192, rfl⟩ ::ₕ
    ⟨191, rfl⟩ ::ₕ
    ⟨190, rfl⟩ ::ₕ
    ⟨189, rfl⟩ ::ₕ
    ⟨188, rfl⟩ ::ₕ
    ⟨187, rfl⟩ ::ₕ
    ⟨186, rfl⟩ ::ₕ
    ⟨185, rfl⟩ ::ₕ
    ⟨184, rfl⟩ ::ₕ
    ⟨183, rfl⟩ ::ₕ
    ⟨182, rfl⟩ ::ₕ
    ⟨181, rfl⟩ ::ₕ
    ⟨180, rfl⟩ ::ₕ
    ⟨179, rfl⟩ ::ₕ
    ⟨178, rfl⟩ ::ₕ .nil)⟩

theorem tail16_7_eq : parts16_7.tail =
    .term (.condBr ⟨0, rfl⟩ true16_7 false16_7) := by rfl

/-- The adapted branch retains every original caller value and every newly computed round register. -/
theorem true16_7_adapt (W : parts16_7.middle.Valuation) :
    adapt16_7 (W.comap prefix16_7.contextHom)
      (sourceTrue16.denote (W.comap finalMap16_7)) = true16_7.denote W := by
  simp only [sourceTrue16, true16_7, Target.denote, HVector.map, adapt16_7_exit, extras16_7,
    Ctxt.Valuation.comap, HVector.append,
    finalMap16_7_at1, finalMap16_7_at3, finalMap16_7_at4, finalMap16_7_at6, finalMap16_7_at23, finalMap16_7_at25, finalMap16_7_at26, finalMap16_7_at28, finalMap16_7_at45, finalMap16_7_at47, finalMap16_7_at48, finalMap16_7_at50, finalMap16_7_at67, finalMap16_7_at69, finalMap16_7_at70, finalMap16_7_at72, origin16_7_at0, origin16_7_at1, origin16_7_at2, origin16_7_at3, origin16_7_at4, origin16_7_at5, origin16_7_at6, origin16_7_at7, origin16_7_at8, origin16_7_at9, origin16_7_at10, origin16_7_at11, origin16_7_at12, origin16_7_at13, origin16_7_at14, origin16_7_at15, origin16_7_at16, origin16_7_at17, origin16_7_at18, origin16_7_at19, origin16_7_at20, origin16_7_at21, origin16_7_at22, origin16_7_at23, origin16_7_at24, origin16_7_at25, origin16_7_at26]

theorem false16_7_adapt (W : parts16_7.middle.Valuation) :
    adapt16_7 (W.comap prefix16_7.contextHom)
      (sourceFalse16.denote (W.comap finalMap16_7)) = false16_7.denote W := by
  simp only [sourceFalse16, false16_7, Target.denote, HVector.map, adapt16_7_loop, extras16_7,
    Ctxt.Valuation.comap, HVector.append,
    finalMap16_7_at1, finalMap16_7_at3, finalMap16_7_at4, finalMap16_7_at6, finalMap16_7_at23, finalMap16_7_at25, finalMap16_7_at26, finalMap16_7_at28, finalMap16_7_at45, finalMap16_7_at47, finalMap16_7_at48, finalMap16_7_at50, finalMap16_7_at67, finalMap16_7_at69, finalMap16_7_at70, finalMap16_7_at72, finalMap16_7_at177, origin16_7_at0, origin16_7_at1, origin16_7_at2, origin16_7_at3, origin16_7_at4, origin16_7_at5, origin16_7_at6, origin16_7_at7, origin16_7_at8, origin16_7_at9, origin16_7_at10, origin16_7_at11, origin16_7_at12, origin16_7_at13, origin16_7_at14, origin16_7_at15, origin16_7_at16, origin16_7_at17, origin16_7_at18, origin16_7_at19, origin16_7_at20, origin16_7_at21, origin16_7_at22, origin16_7_at23, origin16_7_at24, origin16_7_at25, origin16_7_at26]

/-- Transport the actual batch terminator, including poison and both branch payloads. -/
theorem tail16_7_continue {α : Type} (W : parts16_7.middle.Valuation)
    (K : (HVector TyDenote.toType ([] : List SLLVM.Ty) ⊕ SuccArgs agave_batch_16.cfgSigs) → EffectM α) :
    (parts16_7.tail.denote W >>= fun r => K r.2) =
      (sourceParts16.tail.denote (W.comap finalMap16_7) >>= fun r =>
        K (r.2.map id (adapt16_7 (W.comap prefix16_7.contextHom)))) := by
  rw [tail16_7_eq, sourceTail16_eq]
  simpa only [BlockCom.denote_term, bind_assoc, pure_bind] using
    condBr_transport (W.comap finalMap16_7) W ⟨0, rfl⟩ ⟨0, rfl⟩
      sourceTrue16 sourceFalse16 true16_7 false16_7
      (adapt16_7 (W.comap prefix16_7.contextHom)) (by rfl)
      (true16_7_adapt W) (false16_7_adapt W) K

def true16_10 : Target parts16_10.middle agave_batch_16.cfgSigs :=
  ⟨11, rfl, (⟨188, rfl⟩ ::ₕ
    ⟨187, rfl⟩ ::ₕ
    ⟨186, rfl⟩ ::ₕ
    ⟨185, rfl⟩ ::ₕ
    ⟨184, rfl⟩ ::ₕ
    ⟨183, rfl⟩ ::ₕ
    ⟨182, rfl⟩ ::ₕ
    ⟨181, rfl⟩ ::ₕ
    ⟨180, rfl⟩ ::ₕ
    ⟨179, rfl⟩ ::ₕ
    ⟨178, rfl⟩ ::ₕ
    ⟨72, rfl⟩ ::ₕ
    ⟨70, rfl⟩ ::ₕ
    ⟨69, rfl⟩ ::ₕ
    ⟨67, rfl⟩ ::ₕ
    ⟨50, rfl⟩ ::ₕ
    ⟨48, rfl⟩ ::ₕ
    ⟨47, rfl⟩ ::ₕ
    ⟨45, rfl⟩ ::ₕ
    ⟨28, rfl⟩ ::ₕ
    ⟨26, rfl⟩ ::ₕ
    ⟨25, rfl⟩ ::ₕ
    ⟨23, rfl⟩ ::ₕ
    ⟨6, rfl⟩ ::ₕ
    ⟨4, rfl⟩ ::ₕ
    ⟨3, rfl⟩ ::ₕ
    ⟨1, rfl⟩ ::ₕ .nil)⟩

def false16_10 : Target parts16_10.middle agave_batch_16.cfgSigs :=
  ⟨10, rfl, (⟨177, rfl⟩ ::ₕ
    ⟨72, rfl⟩ ::ₕ
    ⟨50, rfl⟩ ::ₕ
    ⟨28, rfl⟩ ::ₕ
    ⟨6, rfl⟩ ::ₕ
    ⟨1, rfl⟩ ::ₕ
    ⟨67, rfl⟩ ::ₕ
    ⟨45, rfl⟩ ::ₕ
    ⟨23, rfl⟩ ::ₕ
    ⟨25, rfl⟩ ::ₕ
    ⟨3, rfl⟩ ::ₕ
    ⟨69, rfl⟩ ::ₕ
    ⟨47, rfl⟩ ::ₕ
    ⟨48, rfl⟩ ::ₕ
    ⟨26, rfl⟩ ::ₕ
    ⟨4, rfl⟩ ::ₕ
    ⟨70, rfl⟩ ::ₕ
    ⟨188, rfl⟩ ::ₕ
    ⟨187, rfl⟩ ::ₕ
    ⟨186, rfl⟩ ::ₕ
    ⟨185, rfl⟩ ::ₕ
    ⟨184, rfl⟩ ::ₕ
    ⟨183, rfl⟩ ::ₕ
    ⟨182, rfl⟩ ::ₕ
    ⟨181, rfl⟩ ::ₕ
    ⟨180, rfl⟩ ::ₕ
    ⟨179, rfl⟩ ::ₕ
    ⟨178, rfl⟩ ::ₕ .nil)⟩

theorem tail16_10_eq : parts16_10.tail =
    .term (.condBr ⟨0, rfl⟩ true16_10 false16_10) := by rfl

/-- The adapted branch retains every original caller value and every newly computed round register. -/
theorem true16_10_adapt (W : parts16_10.middle.Valuation) :
    adapt16_10 (W.comap prefix16_10.contextHom)
      (sourceTrue16.denote (W.comap finalMap16_10)) = true16_10.denote W := by
  simp only [sourceTrue16, true16_10, Target.denote, HVector.map, adapt16_10_exit, extras16_10,
    Ctxt.Valuation.comap, HVector.append,
    finalMap16_10_at1, finalMap16_10_at3, finalMap16_10_at4, finalMap16_10_at6, finalMap16_10_at23, finalMap16_10_at25, finalMap16_10_at26, finalMap16_10_at28, finalMap16_10_at45, finalMap16_10_at47, finalMap16_10_at48, finalMap16_10_at50, finalMap16_10_at67, finalMap16_10_at69, finalMap16_10_at70, finalMap16_10_at72, origin16_10_at0, origin16_10_at1, origin16_10_at2, origin16_10_at3, origin16_10_at4, origin16_10_at5, origin16_10_at6, origin16_10_at7, origin16_10_at8, origin16_10_at9, origin16_10_at10]

theorem false16_10_adapt (W : parts16_10.middle.Valuation) :
    adapt16_10 (W.comap prefix16_10.contextHom)
      (sourceFalse16.denote (W.comap finalMap16_10)) = false16_10.denote W := by
  simp only [sourceFalse16, false16_10, Target.denote, HVector.map, adapt16_10_loop, extras16_10,
    Ctxt.Valuation.comap, HVector.append,
    finalMap16_10_at1, finalMap16_10_at3, finalMap16_10_at4, finalMap16_10_at6, finalMap16_10_at23, finalMap16_10_at25, finalMap16_10_at26, finalMap16_10_at28, finalMap16_10_at45, finalMap16_10_at47, finalMap16_10_at48, finalMap16_10_at50, finalMap16_10_at67, finalMap16_10_at69, finalMap16_10_at70, finalMap16_10_at72, finalMap16_10_at177, origin16_10_at0, origin16_10_at1, origin16_10_at2, origin16_10_at3, origin16_10_at4, origin16_10_at5, origin16_10_at6, origin16_10_at7, origin16_10_at8, origin16_10_at9, origin16_10_at10]

/-- Transport the actual batch terminator, including poison and both branch payloads. -/
theorem tail16_10_continue {α : Type} (W : parts16_10.middle.Valuation)
    (K : (HVector TyDenote.toType ([] : List SLLVM.Ty) ⊕ SuccArgs agave_batch_16.cfgSigs) → EffectM α) :
    (parts16_10.tail.denote W >>= fun r => K r.2) =
      (sourceParts16.tail.denote (W.comap finalMap16_10) >>= fun r =>
        K (r.2.map id (adapt16_10 (W.comap prefix16_10.contextHom)))) := by
  rw [tail16_10_eq, sourceTail16_eq]
  simpa only [BlockCom.denote_term, bind_assoc, pure_bind] using
    condBr_transport (W.comap finalMap16_10) W ⟨0, rfl⟩ ⟨0, rfl⟩
      sourceTrue16 sourceFalse16 true16_10 false16_10
      (adapt16_10 (W.comap prefix16_10.contextHom)) (by rfl)
      (true16_10_adapt W) (false16_10_adapt W) K

/-- The actual inlined batch round executes the standalone round body,
with every additional caller value preserved by the successor adapter. -/
theorem block16_7_transport {α : Type} (V : Input16_7.Valuation)
    (K : (HVector TyDenote.toType ([] : List SLLVM.Ty) ⊕
      SuccArgs agave_batch_16.cfgSigs) → EffectM α) :
    (agave_batch_16.cfgBlock_7.denote V >>= fun r => K r.2) =
      (agave_compress_pre_16.cfgBlock_0.denote (V.comap BatchRounds.rename16_7) >>= fun r =>
        K (r.2.map id (adapt16_7 V))) :=
  BatchRounds.block16_7_continue V K
    (fun U r => K (r.map id (adapt16_7 U))) (fun W => tail16_7_continue W K)

/-- The actual inlined batch round executes the standalone round body,
with every additional caller value preserved by the successor adapter. -/
theorem block16_10_transport {α : Type} (V : Input16_10.Valuation)
    (K : (HVector TyDenote.toType ([] : List SLLVM.Ty) ⊕
      SuccArgs agave_batch_16.cfgSigs) → EffectM α) :
    (agave_batch_16.cfgBlock_10.denote V >>= fun r => K r.2) =
      (agave_compress_pre_16.cfgBlock_0.denote (V.comap BatchRounds.rename16_10) >>= fun r =>
        K (r.2.map id (adapt16_10 V))) :=
  BatchRounds.block16_10_continue V K
    (fun U r => K (r.map id (adapt16_10 U))) (fun W => tail16_10_continue W K)

end
end AgaveLatticeHash.MLIR.BatchRoundBranches
