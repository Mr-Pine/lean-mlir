/- Released under Apache 2.0 license as described in the file LICENSE. -/
import SSA.Projects.Agave.LatticeHash.MLIR.BatchInit8
import SSA.Projects.Agave.LatticeHash.MLIR.BatchUpdate
import SSA.Projects.Agave.LatticeHash.MLIR.BatchRoundAdapters8
import SSA.Projects.Agave.LatticeHash.MLIR.BatchRoundData
import SSA.Projects.Agave.LatticeHash.MLIR.RoundCore

namespace AgaveLatticeHash.MLIR.BatchNonrootRounds8
open LeanMLIR SLLVM Firedancer Blake3Compression
open InstCombine (LLVM)
open CompressionRound
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

abbrev Words8 := Vector Word 8
abbrev PackedTy : SLLVM.Ty := .arith (.vector 4 (.bitvec 64))
abbrev ExtraTypes : List SLLVM.Ty := [PackedTy, PackedTy, PackedTy, PackedTy,
  PackedTy, PackedTy, PackedTy, PackedTy, .arith (.vector 8 (.bitvec 64)),
  .arith (.vector 8 (.bitvec 64)), .arith (.vector 8 (.bitvec 1))]

def extras (cv : CV (Lanes 8)) (offsets advanced : Vector (BitVec 64) 8)
    (active : Fin 8 → Bool) : HVector TyDenote.toType ExtraTypes :=
  [(packCV8 (cv 7)).map PoisonOr.value, (packCV8 (cv 6)).map PoisonOr.value,
   (packCV8 (cv 5)).map PoisonOr.value, (packCV8 (cv 4)).map PoisonOr.value,
   (packCV8 (cv 3)).map PoisonOr.value, (packCV8 (cv 2)).map PoisonOr.value,
   (packCV8 (cv 1)).map PoisonOr.value, (packCV8 (cv 0)).map PoisonOr.value,
   offsets.map PoisonOr.value, advanced.map PoisonOr.value, BatchUpdate.active8 active]ₕ

def roundTarget (e : HVector TyDenote.toType ExtraTypes) (r : BitVec 64)
    (v : State Words8) : SuccArgs agave_batch_8.cfgSigs :=
  ⟨20, rfl, (CompressionRound.headerAt8 r v).args.append e⟩

def updateTarget (e : HVector TyDenote.toType ExtraTypes)
    (v : State Words8) : SuccArgs agave_batch_8.cfgSigs :=
  ⟨21, rfl, e.append (CompressionRound.exitAt8 v).args⟩

noncomputable def roundVal (B : agave_batch_8.cfgCtx.Valuation)
    (e : HVector TyDenote.toType ExtraTypes) (r : BitVec 64) (v : State Words8) :
    BatchRounds.Input8_20.Valuation :=
  Ctxt.Valuation.ofHVector (roundTarget e r v).args.reverse ++ B

noncomputable def updateVal (B : agave_batch_8.cfgCtx.Valuation)
    (e : HVector TyDenote.toType ExtraTypes) (v : State Words8) :
    BatchUpdate.Input8.Valuation :=
  Ctxt.Valuation.ofHVector (updateTarget e v).args.reverse ++ B

/-- Unused standalone bindings can depend on the current phi state. Its used
bindings are all immutable batch-entry values, as `sourceEnv_change` proves. -/
noncomputable def sourceVal (B : agave_batch_8.cfgCtx.Valuation)
    (e : HVector TyDenote.toType ExtraTypes) (r : BitVec 64) (v : State Words8) :
    agave_compress_pre_8.cfgCtx.Valuation :=
  fun _ x => ((roundVal B e r v).comap BatchRounds.rename8_20) (x.appendInr (Γ := Ctxt.ofList (CompressionRound.headerAt8 r v).ts.reverse))

theorem adapt_header (B : agave_batch_8.cfgCtx.Valuation)
    (cv : CV (Lanes 8)) (offsets advanced : Vector (BitVec 64) 8) (active : Fin 8 → Bool)
    (r r' : BitVec 64) (v v' : State Words8) :
    BatchRoundBranches.adapt8_20 (roundVal B (extras cv offsets advanced active) r v)
      (CompressionRound.headerAt8 r' v') = roundTarget (extras cv offsets advanced active) r' v' := rfl

theorem adapt_exit (B : agave_batch_8.cfgCtx.Valuation)
    (cv : CV (Lanes 8)) (offsets advanced : Vector (BitVec 64) 8) (active : Fin 8 → Bool)
    (r : BitVec 64) (v v' : State Words8) :
    BatchRoundBranches.adapt8_20 (roundVal B (extras cv offsets advanced active) r v)
      (CompressionRound.exitAt8 v') = updateTarget (extras cv offsets advanced active) v' := rfl

structure InitEnv (B : agave_batch_8.cfgCtx.Valuation) : Prop where
  zero64 : B ⟨65, rfl⟩ = PoisonOr.value 0#64
  zero32 : B ⟨61, rfl⟩ = Vector.replicate 8 (PoisonOr.value 0#32)
  iv0 : B ⟨48, rfl⟩ = Vector.replicate 8 (PoisonOr.value 0x6A09E667#32)
  iv1 : B ⟨47, rfl⟩ = Vector.replicate 8 (PoisonOr.value 0xBB67AE85#32)
  iv2 : B ⟨46, rfl⟩ = Vector.replicate 8 (PoisonOr.value 0x3C6EF372#32)
  iv3 : B ⟨45, rfl⟩ = Vector.replicate 8 (PoisonOr.value 0xA54FF53A#32)

def initial (cv : CV (Lanes 8)) (len flags : Words8) : State Words8 :=
  initState (fun w => Vector.ofFn (cv w)) (Vector.replicate 8)
    (Vector.replicate 8 0#32) (Vector.replicate 8 0#32) len flags

def initTarget (cv : CV (Lanes 8)) (len flags : Words8)
    (offsets advanced : Vector (BitVec 64) 8) (active : Fin 8 → Bool) :
    SuccArgs agave_batch_8.cfgSigs :=
  ⟨19, rfl, (extras cv offsets advanced active).append
    [flags.map PoisonOr.value, len.map PoisonOr.value]ₕ⟩

noncomputable def initVal (B : agave_batch_8.cfgCtx.Valuation)
    (cv : CV (Lanes 8)) (len flags : Words8)
    (offsets advanced : Vector (BitVec 64) 8) (active : Fin 8 → Bool) :
    BatchInit8.Input19.Valuation :=
  Ctxt.Valuation.ofHVector (initTarget cv len flags offsets advanced active).args.reverse ++ B

theorem next19_initial (B : agave_batch_8.cfgCtx.Valuation) (hB : InitEnv B)
    (cv : CV (Lanes 8)) (len flags : Words8)
    (offsets advanced : Vector (BitVec 64) 8) (active : Fin 8 → Bool) :
    BatchInit8.next19 (initVal B cv len flags offsets advanced active) =
      roundTarget (extras cv offsets advanced active) 0 (initial cv len flags) := by
  have hz : (initVal B cv len flags offsets advanced active) ⟨78, rfl⟩ =
      PoisonOr.value 0#64 := hB.zero64
  have hh : (initVal B cv len flags offsets advanced active) ⟨74, rfl⟩ =
      Vector.replicate 8 (PoisonOr.value 0#32) := hB.zero32
  have hi0 : (initVal B cv len flags offsets advanced active) ⟨61, rfl⟩ =
      Vector.replicate 8 (PoisonOr.value 0x6A09E667#32) := hB.iv0
  have hi1 : (initVal B cv len flags offsets advanced active) ⟨60, rfl⟩ =
      Vector.replicate 8 (PoisonOr.value 0xBB67AE85#32) := hB.iv1
  have hi2 : (initVal B cv len flags offsets advanced active) ⟨59, rfl⟩ =
      Vector.replicate 8 (PoisonOr.value 0x3C6EF372#32) := hB.iv2
  have hi3 : (initVal B cv len flags offsets advanced active) ⟨58, rfl⟩ =
      Vector.replicate 8 (PoisonOr.value 0xA54FF53A#32) := hB.iv3
  have hu0 : BatchInit8.unpackCV ((initVal B cv len flags offsets advanced active) ⟨5, rfl⟩) =
      (Vector.ofFn (cv 0)).map PoisonOr.value := BatchInit8.unpackCV_pack (cv 0)
  have hu1 : BatchInit8.unpackCV ((initVal B cv len flags offsets advanced active) ⟨6, rfl⟩) =
      (Vector.ofFn (cv 1)).map PoisonOr.value := BatchInit8.unpackCV_pack (cv 1)
  have hu2 : BatchInit8.unpackCV ((initVal B cv len flags offsets advanced active) ⟨7, rfl⟩) =
      (Vector.ofFn (cv 2)).map PoisonOr.value := BatchInit8.unpackCV_pack (cv 2)
  have hu3 : BatchInit8.unpackCV ((initVal B cv len flags offsets advanced active) ⟨8, rfl⟩) =
      (Vector.ofFn (cv 3)).map PoisonOr.value := BatchInit8.unpackCV_pack (cv 3)
  have hu4 : BatchInit8.unpackCV ((initVal B cv len flags offsets advanced active) ⟨9, rfl⟩) =
      (Vector.ofFn (cv 4)).map PoisonOr.value := BatchInit8.unpackCV_pack (cv 4)
  have hu5 : BatchInit8.unpackCV ((initVal B cv len flags offsets advanced active) ⟨10, rfl⟩) =
      (Vector.ofFn (cv 5)).map PoisonOr.value := BatchInit8.unpackCV_pack (cv 5)
  have hu6 : BatchInit8.unpackCV ((initVal B cv len flags offsets advanced active) ⟨11, rfl⟩) =
      (Vector.ofFn (cv 6)).map PoisonOr.value := BatchInit8.unpackCV_pack (cv 6)
  have hu7 : BatchInit8.unpackCV ((initVal B cv len flags offsets advanced active) ⟨12, rfl⟩) =
      (Vector.ofFn (cv 7)).map PoisonOr.value := BatchInit8.unpackCV_pack (cv 7)
  unfold BatchInit8.next19
  rw [hz, hh, hi0, hi1, hi2, hi3, hu0, hu1, hu2, hu3, hu4, hu5, hu6, hu7]
  congr 1
  apply HVector.ext
  intro i
  fin_cases i <;> first | rfl | exact Vector.map_replicate.symm



def upperCV (v : State Words8) : CV (Lanes 8) :=
  fun w lane => (v ⟨w.val + 8, by omega⟩)[lane]
def lowerCV (v : State Words8) : CV (Lanes 8) :=
  fun w lane => (v ⟨w.val, by omega⟩)[lane]

private theorem vector_eta (v : Words8) : (Vector.ofFn fun i : Fin 8 => v[i]) = v := by
  apply Vector.ext
  intro i hi
  simp only [Vector.getElem_ofFn, Fin.getElem_fin]

/-- The actual exit argument order meets the checked CV-update block's
representation, including the complete saved CV and per-lane mask/offsets. -/
theorem update_env (B : agave_batch_8.cfgCtx.Valuation)
    (hz : B ⟨28, rfl⟩ = Vector.replicate 32 (PoisonOr.value 0#8))
    (cv : CV (Lanes 8)) (offsets advanced : Vector (BitVec 64) 8) (active : Fin 8 → Bool)
    (v : State Words8) :
    BatchUpdate.Env8 (updateVal B (extras cv offsets advanced active) v)
      active cv (upperCV v) (lowerCV v) offsets advanced := by
  constructor <;> try (first | exact hz | rfl)
  all_goals
    apply congrArg (Vector.map PoisonOr.value)
    symm
    exact vector_eta _


end AgaveLatticeHash.MLIR.BatchNonrootRounds8
