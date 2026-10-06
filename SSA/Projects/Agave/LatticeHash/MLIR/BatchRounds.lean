/- Released under Apache 2.0 license as described in the file LICENSE. -/
import SSA.Projects.Agave.LatticeHash.MLIR.BatchRoundData
namespace AgaveLatticeHash.MLIR.BatchRounds
open LeanMLIR SLLVM
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
theorem certificate8_20 : BlockPrefix.Renamed rename8_20
    sourcePrefix8 prefix8_20 finalMap8_20 := by
  repeat first
    | apply BlockPrefix.Renamed.var
    | refine BlockPrefix.Renamed.var_semantic _ _ (by rfl) (by exact id) ?_
    | exact BlockPrefix.Renamed.nil _

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
/-- Execution of the inlined round prefix transports arbitrary continuations. -/
theorem prefix8_20_continue {α : Type} (V : Input8_20.Valuation)
    (K : sourceParts8.middle.Valuation → EffectM α) :
    (prefix8_20.denote V >>= fun W => K (W.comap finalMap8_20)) =
      sourcePrefix8.denote (V.comap rename8_20) >>= K :=
  certificate8_20.denote_bind V K


set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
theorem certificate8_23 : BlockPrefix.Renamed rename8_23
    sourcePrefix8 prefix8_23 finalMap8_23 := by
  repeat first
    | apply BlockPrefix.Renamed.var
    | refine BlockPrefix.Renamed.var_semantic _ _ (by rfl) (by exact id) ?_
    | exact BlockPrefix.Renamed.nil _

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
/-- Execution of the inlined round prefix transports arbitrary continuations. -/
theorem prefix8_23_continue {α : Type} (V : Input8_23.Valuation)
    (K : sourceParts8.middle.Valuation → EffectM α) :
    (prefix8_23.denote V >>= fun W => K (W.comap finalMap8_23)) =
      sourcePrefix8.denote (V.comap rename8_23) >>= K :=
  certificate8_23.denote_bind V K


set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
theorem certificate16_7 : BlockPrefix.Renamed rename16_7
    sourcePrefix16 prefix16_7 finalMap16_7 := by
  repeat first
    | apply BlockPrefix.Renamed.var
    | refine BlockPrefix.Renamed.var_semantic _ _ (by rfl) (by exact id) ?_
    | exact BlockPrefix.Renamed.nil _

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
/-- Execution of the inlined round prefix transports arbitrary continuations. -/
theorem prefix16_7_continue {α : Type} (V : Input16_7.Valuation)
    (K : sourceParts16.middle.Valuation → EffectM α) :
    (prefix16_7.denote V >>= fun W => K (W.comap finalMap16_7)) =
      sourcePrefix16.denote (V.comap rename16_7) >>= K :=
  certificate16_7.denote_bind V K


set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
theorem certificate16_10 : BlockPrefix.Renamed rename16_10
    sourcePrefix16 prefix16_10 finalMap16_10 := by
  repeat first
    | apply BlockPrefix.Renamed.var
    | refine BlockPrefix.Renamed.var_semantic _ _ (by rfl) (by exact id) ?_
    | exact BlockPrefix.Renamed.nil _

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
/-- Execution of the inlined round prefix transports arbitrary continuations. -/
theorem prefix16_10_continue {α : Type} (V : Input16_10.Valuation)
    (K : sourceParts16.middle.Valuation → EffectM α) :
    (prefix16_10.denote V >>= fun W => K (W.comap finalMap16_10)) =
      sourcePrefix16.denote (V.comap rename16_10) >>= K :=
  certificate16_10.denote_bind V K



/-- Transport also preserves every incoming batch value needed by successor blocks. -/
theorem prefix8_20_continue_context {α : Type} (V : Input8_20.Valuation)
    (K : sourceParts8.middle.Valuation →
      Input8_20.Valuation → EffectM α) :
    (prefix8_20.denote V >>= fun W =>
      K (W.comap finalMap8_20) (W.comap prefix8_20.contextHom)) =
      (sourcePrefix8.denote (V.comap rename8_20) >>= fun W => K W V) :=
  certificate8_20.denote_bind_with_context V K


/-- Transport also preserves every incoming batch value needed by successor blocks. -/
theorem prefix8_23_continue_context {α : Type} (V : Input8_23.Valuation)
    (K : sourceParts8.middle.Valuation →
      Input8_23.Valuation → EffectM α) :
    (prefix8_23.denote V >>= fun W =>
      K (W.comap finalMap8_23) (W.comap prefix8_23.contextHom)) =
      (sourcePrefix8.denote (V.comap rename8_23) >>= fun W => K W V) :=
  certificate8_23.denote_bind_with_context V K


/-- Transport also preserves every incoming batch value needed by successor blocks. -/
theorem prefix16_7_continue_context {α : Type} (V : Input16_7.Valuation)
    (K : sourceParts16.middle.Valuation →
      Input16_7.Valuation → EffectM α) :
    (prefix16_7.denote V >>= fun W =>
      K (W.comap finalMap16_7) (W.comap prefix16_7.contextHom)) =
      (sourcePrefix16.denote (V.comap rename16_7) >>= fun W => K W V) :=
  certificate16_7.denote_bind_with_context V K


/-- Transport also preserves every incoming batch value needed by successor blocks. -/
theorem prefix16_10_continue_context {α : Type} (V : Input16_10.Valuation)
    (K : sourceParts16.middle.Valuation →
      Input16_10.Valuation → EffectM α) :
    (prefix16_10.denote V >>= fun W =>
      K (W.comap finalMap16_10) (W.comap prefix16_10.contextHom)) =
      (sourcePrefix16.denote (V.comap rename16_10) >>= fun W => K W V) :=
  certificate16_10.denote_bind_with_context V K






/-- The actual batch block inherits any standalone-round continuation theorem
once its successor argument lists are related by `htail`. -/
theorem block8_20_continue {α : Type} (V : Input8_20.Valuation)
    (k : (HVector TyDenote.toType ([] : List SLLVM.Ty) ⊕
      SuccArgs agave_batch_8.cfgSigs) → EffectM α)
    (K : Input8_20.Valuation → (HVector TyDenote.toType ([] : List SLLVM.Ty) ⊕
      SuccArgs agave_compress_pre_8.cfgSigs) → EffectM α)
    (htail : ∀ W : parts8_20.middle.Valuation,
      (parts8_20.tail.denote W >>= fun r => k r.2) =
      (sourceParts8.tail.denote (W.comap finalMap8_20) >>=
        fun r => K (W.comap prefix8_20.contextHom) r.2)) :
    (agave_batch_8.cfgBlock_20.denote V >>= fun r => k r.2) =
      (agave_compress_pre_8.cfgBlock_0.denote (V.comap rename8_20) >>=
        fun r => K V r.2) :=
  parts_continue agave_compress_pre_8.cfgBlock_0 agave_batch_8.cfgBlock_20
    sourceParts8 parts8_20 sourceParts8_append parts8_20_append
    rename8_20 finalMap8_20 certificate8_20 V k K htail


/-- The actual batch block inherits any standalone-round continuation theorem
once its successor argument lists are related by `htail`. -/
theorem block8_23_continue {α : Type} (V : Input8_23.Valuation)
    (k : (HVector TyDenote.toType ([] : List SLLVM.Ty) ⊕
      SuccArgs agave_batch_8.cfgSigs) → EffectM α)
    (K : Input8_23.Valuation → (HVector TyDenote.toType ([] : List SLLVM.Ty) ⊕
      SuccArgs agave_compress_pre_8.cfgSigs) → EffectM α)
    (htail : ∀ W : parts8_23.middle.Valuation,
      (parts8_23.tail.denote W >>= fun r => k r.2) =
      (sourceParts8.tail.denote (W.comap finalMap8_23) >>=
        fun r => K (W.comap prefix8_23.contextHom) r.2)) :
    (agave_batch_8.cfgBlock_23.denote V >>= fun r => k r.2) =
      (agave_compress_pre_8.cfgBlock_0.denote (V.comap rename8_23) >>=
        fun r => K V r.2) :=
  parts_continue agave_compress_pre_8.cfgBlock_0 agave_batch_8.cfgBlock_23
    sourceParts8 parts8_23 sourceParts8_append parts8_23_append
    rename8_23 finalMap8_23 certificate8_23 V k K htail



/-- The actual batch block inherits any standalone-round continuation theorem
once its successor argument lists are related by `htail`. -/
theorem block16_7_continue {α : Type} (V : Input16_7.Valuation)
    (k : (HVector TyDenote.toType ([] : List SLLVM.Ty) ⊕
      SuccArgs agave_batch_16.cfgSigs) → EffectM α)
    (K : Input16_7.Valuation → (HVector TyDenote.toType ([] : List SLLVM.Ty) ⊕
      SuccArgs agave_compress_pre_16.cfgSigs) → EffectM α)
    (htail : ∀ W : parts16_7.middle.Valuation,
      (parts16_7.tail.denote W >>= fun r => k r.2) =
      (sourceParts16.tail.denote (W.comap finalMap16_7) >>=
        fun r => K (W.comap prefix16_7.contextHom) r.2)) :
    (agave_batch_16.cfgBlock_7.denote V >>= fun r => k r.2) =
      (agave_compress_pre_16.cfgBlock_0.denote (V.comap rename16_7) >>=
        fun r => K V r.2) :=
  parts_continue agave_compress_pre_16.cfgBlock_0 agave_batch_16.cfgBlock_7
    sourceParts16 parts16_7 sourceParts16_append parts16_7_append
    rename16_7 finalMap16_7 certificate16_7 V k K htail


/-- The actual batch block inherits any standalone-round continuation theorem
once its successor argument lists are related by `htail`. -/
theorem block16_10_continue {α : Type} (V : Input16_10.Valuation)
    (k : (HVector TyDenote.toType ([] : List SLLVM.Ty) ⊕
      SuccArgs agave_batch_16.cfgSigs) → EffectM α)
    (K : Input16_10.Valuation → (HVector TyDenote.toType ([] : List SLLVM.Ty) ⊕
      SuccArgs agave_compress_pre_16.cfgSigs) → EffectM α)
    (htail : ∀ W : parts16_10.middle.Valuation,
      (parts16_10.tail.denote W >>= fun r => k r.2) =
      (sourceParts16.tail.denote (W.comap finalMap16_10) >>=
        fun r => K (W.comap prefix16_10.contextHom) r.2)) :
    (agave_batch_16.cfgBlock_10.denote V >>= fun r => k r.2) =
      (agave_compress_pre_16.cfgBlock_0.denote (V.comap rename16_10) >>=
        fun r => K V r.2) :=
  parts_continue agave_compress_pre_16.cfgBlock_0 agave_batch_16.cfgBlock_10
    sourceParts16 parts16_10 sourceParts16_append parts16_10_append
    rename16_10 finalMap16_10 certificate16_10 V k K htail

end
end AgaveLatticeHash.MLIR.BatchRounds
