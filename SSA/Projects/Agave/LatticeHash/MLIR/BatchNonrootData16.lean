/- Released under Apache 2.0 license as described in the file LICENSE. -/
import SSA.Projects.Agave.LatticeHash.MLIR.BatchNonrootRounds16
import SSA.Projects.Agave.LatticeHash.MLIR.CompressionSupport

namespace AgaveLatticeHash.MLIR.BatchNonrootRounds16
open LeanMLIR SLLVM Firedancer Blake3Compression CompressionRound
open InstCombine (LLVM)
set_option maxRecDepth 8192
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

def extras (cv : CV (Lanes 16)) (offsets : Vector (BitVec 64) 16)
    (active : Fin 16 → Bool) : HVector TyDenote.toType ExtraTypes :=
  (headerTarget16 cv offsets).args.append [BatchUpdate16.activeBytes16 active]ₕ

def initial (cv : CV (Lanes 16)) (len flags : Words16) : State Words16 :=
  initState (fun w => Vector.ofFn (cv w)) (Vector.replicate 16)
    (Vector.replicate 16 0#32) (Vector.replicate 16 0#32) len flags

def initTarget (cv : CV (Lanes 16))
    (packedLen packedFlags : Vector (LLVM.IntW 64) 8)
    (offsets : Vector (BitVec 64) 16) (active : Fin 16 → Bool) :
    SuccArgs agave_batch_16.cfgSigs :=
  ⟨6, rfl, (headerTarget16 cv offsets).args.append
    [packedFlags, packedLen, BatchUpdate16.activeBytes16 active]ₕ⟩

noncomputable def initVal (B : agave_batch_16.cfgCtx.Valuation)
    (cv : CV (Lanes 16)) (packedLen packedFlags : Vector (LLVM.IntW 64) 8)
    (offsets : Vector (BitVec 64) 16) (active : Fin 16 → Bool) :
    BatchPaths16.Input6.Valuation :=
  Ctxt.Valuation.ofHVector (initTarget cv packedLen packedFlags offsets active).args.reverse ++ B

structure InitEnv (B : agave_batch_16.cfgCtx.Valuation) : Prop where
  zero64 : B ⟨103, rfl⟩ = PoisonOr.value 0#64
  zero32 : B ⟨84, rfl⟩ = Vector.replicate 16 (PoisonOr.value 0#32)
  iv0 : B ⟨94, rfl⟩ = Vector.replicate 16 (PoisonOr.value 0x6A09E667#32)
  iv1 : B ⟨95, rfl⟩ = Vector.replicate 16 (PoisonOr.value 0xBB67AE85#32)
  iv2 : B ⟨96, rfl⟩ = Vector.replicate 16 (PoisonOr.value 0x3C6EF372#32)
  iv3 : B ⟨97, rfl⟩ = Vector.replicate 16 (PoisonOr.value 0xA54FF53A#32)

theorem next6_initial (B : agave_batch_16.cfgCtx.Valuation) (hB : InitEnv B)
    (cv : CV (Lanes 16)) (len flags : Words16)
    (packedLen packedFlags : Vector (LLVM.IntW 64) 8)
    (offsets : Vector (BitVec 64) 16) (active : Fin 16 → Bool)
    (hl : BatchPaths16.words16 packedLen = len.map PoisonOr.value)
    (hf : BatchPaths16.words16 packedFlags = flags.map PoisonOr.value) :
    BatchPaths16.next6 (initVal B cv packedLen packedFlags offsets active) =
      roundTarget (extras cv offsets active) 0 (initial cv len flags) := by
  have hz : (initVal B cv packedLen packedFlags offsets active) ⟨132, rfl⟩ =
      PoisonOr.value 0#64 := hB.zero64
  have hh : (initVal B cv packedLen packedFlags offsets active) ⟨113, rfl⟩ =
      Vector.replicate 16 (PoisonOr.value 0#32) := hB.zero32
  have hi0 : (initVal B cv packedLen packedFlags offsets active) ⟨123, rfl⟩ =
      Vector.replicate 16 (PoisonOr.value 0x6A09E667#32) := hB.iv0
  have hi1 : (initVal B cv packedLen packedFlags offsets active) ⟨124, rfl⟩ =
      Vector.replicate 16 (PoisonOr.value 0xBB67AE85#32) := hB.iv1
  have hi2 : (initVal B cv packedLen packedFlags offsets active) ⟨125, rfl⟩ =
      Vector.replicate 16 (PoisonOr.value 0x3C6EF372#32) := hB.iv2
  have hi3 : (initVal B cv packedLen packedFlags offsets active) ⟨126, rfl⟩ =
      Vector.replicate 16 (PoisonOr.value 0xA54FF53A#32) := hB.iv3
  have hlen : BatchPaths16.words16 ((initVal B cv packedLen packedFlags offsets active) ⟨1, rfl⟩) = len.map PoisonOr.value := hl
  have hflags : BatchPaths16.words16 ((initVal B cv packedLen packedFlags offsets active) ⟨2, rfl⟩) = flags.map PoisonOr.value := hf
  unfold BatchPaths16.next6
  rw [hz, hh, hi0, hi1, hi2, hi3, hlen, hflags]
  have hs0 : initial cv len flags 0 = Vector.ofFn (cv 0) := rfl
  have hs1 : initial cv len flags 1 = Vector.ofFn (cv 1) := rfl
  have hs2 : initial cv len flags 2 = Vector.ofFn (cv 2) := rfl
  have hs3 : initial cv len flags 3 = Vector.ofFn (cv 3) := rfl
  have hs4 : initial cv len flags 4 = Vector.ofFn (cv 4) := rfl
  have hs5 : initial cv len flags 5 = Vector.ofFn (cv 5) := rfl
  have hs6 : initial cv len flags 6 = Vector.ofFn (cv 6) := rfl
  have hs7 : initial cv len flags 7 = Vector.ofFn (cv 7) := rfl
  have hs8 : initial cv len flags 8 = Vector.replicate 16 0x6A09E667#32 := rfl
  have hs9 : initial cv len flags 9 = Vector.replicate 16 0xBB67AE85#32 := rfl
  have hs10 : initial cv len flags 10 = Vector.replicate 16 0x3C6EF372#32 := rfl
  have hs11 : initial cv len flags 11 = Vector.replicate 16 0xA54FF53A#32 := rfl
  have hs12 : initial cv len flags 12 = Vector.replicate 16 0#32 := rfl
  have hs13 : initial cv len flags 13 = Vector.replicate 16 0#32 := rfl
  have hs14 : initial cv len flags 14 = len := rfl
  have hs15 : initial cv len flags 15 = flags := rfl
  simp only [roundTarget, CompressionRound.headerAt16,
    hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hs12, hs13, hs14, hs15, Vector.map_ofFn, Vector.map_replicate]
  rfl

theorem init_env (entry : GlobalState) (src len out sched panic : Pointer)
    (lengthsLo lengthsHi : Vector (BitVec 64) 8) :
    InitEnv (BatchEntry16.entryVal16 entry src len out sched panic lengthsLo lengthsHi) := by
  constructor
  · rfl
  all_goals
    apply Vector.ext
    intro i hi
    rfl

def upperCV (v : State Words16) : CV (Lanes 16) :=
  fun w lane => (v ⟨w.val + 8, by omega⟩)[lane]
def lowerCV (v : State Words16) : CV (Lanes 16) :=
  fun w lane => (v ⟨w.val, by omega⟩)[lane]

private theorem vector_eta (v : Words16) : (Vector.ofFn fun i : Fin 16 => v[i]) = v := by
  apply Vector.ext
  intro i hi
  simp only [Vector.getElem_ofFn, Fin.getElem_fin]

theorem update_env (entry : GlobalState) (src len out sched panic : Pointer)
    (lengthsLo lengthsHi : Vector (BitVec 64) 8)
    (cv : CV (Lanes 16)) (offsets : Vector (BitVec 64) 16) (active : Fin 16 → Bool)
    (v : State Words16) :
    BatchUpdate16.Env16
      (updateVal (BatchEntry16.entryVal16 entry src len out sched panic lengthsLo lengthsHi)
        (extras cv offsets active) v)
      active cv (upperCV v) (lowerCV v) offsets := by
  constructor <;> try rfl
  case low =>
    change (Vector.ofFn fun i : Fin 8 => PoisonOr.value offsets[i.val]) = _
    apply Vector.ext
    intro i hi
    simp only [Vector.getElem_map, Vector.getElem_ofFn, Fin.getElem_fin]
  case high =>
    change (Vector.ofFn fun i : Fin 8 => PoisonOr.value offsets[i.val + 8]) = _
    apply Vector.ext
    intro i hi
    simp only [Vector.getElem_map, Vector.getElem_ofFn, Fin.getElem_fin]
  case old0 =>
    change (Vector.ofFn fun lane => PoisonOr.value (cv 0 lane)) = _
    apply Vector.ext
    intro i hi
    simp only [Vector.getElem_map, Vector.getElem_ofFn, Fin.getElem_fin]
  case old1 =>
    change (Vector.ofFn fun lane => PoisonOr.value (cv 1 lane)) = _
    apply Vector.ext
    intro i hi
    simp only [Vector.getElem_map, Vector.getElem_ofFn, Fin.getElem_fin]
  case old2 =>
    change (Vector.ofFn fun lane => PoisonOr.value (cv 2 lane)) = _
    apply Vector.ext
    intro i hi
    simp only [Vector.getElem_map, Vector.getElem_ofFn, Fin.getElem_fin]
  case old3 =>
    change (Vector.ofFn fun lane => PoisonOr.value (cv 3 lane)) = _
    apply Vector.ext
    intro i hi
    simp only [Vector.getElem_map, Vector.getElem_ofFn, Fin.getElem_fin]
  case old4 =>
    change (Vector.ofFn fun lane => PoisonOr.value (cv 4 lane)) = _
    apply Vector.ext
    intro i hi
    simp only [Vector.getElem_map, Vector.getElem_ofFn, Fin.getElem_fin]
  case old5 =>
    change (Vector.ofFn fun lane => PoisonOr.value (cv 5 lane)) = _
    apply Vector.ext
    intro i hi
    simp only [Vector.getElem_map, Vector.getElem_ofFn, Fin.getElem_fin]
  case old6 =>
    change (Vector.ofFn fun lane => PoisonOr.value (cv 6 lane)) = _
    apply Vector.ext
    intro i hi
    simp only [Vector.getElem_map, Vector.getElem_ofFn, Fin.getElem_fin]
  case old7 =>
    change (Vector.ofFn fun lane => PoisonOr.value (cv 7 lane)) = _
    apply Vector.ext
    intro i hi
    simp only [Vector.getElem_map, Vector.getElem_ofFn, Fin.getElem_fin]
  all_goals
    apply congrArg (Vector.map PoisonOr.value)
    symm
    exact vector_eta _

theorem round_env (entry : GlobalState) (src len out sched panic : Pointer)
    (lengthsLo lengthsHi : Vector (BitVec 64) 8)
    (cv : CV (Lanes 16)) (offsets : Vector (BitVec 64) 16)
    (active : Fin 16 → Bool) (r : BitVec 64) (v : State Words16) :
    RoundEnv16
      (sourceVal (BatchEntry16.entryVal16 entry src len out sched panic lengthsLo lengthsHi)
        (extras cv offsets active) r v) (BatchEntry16.scratch entry 0) sched := by
  constructor <;> first | rfl | (apply Vector.ext; intro i hi; rfl)

theorem initial_lane (cv : CV (Lanes 16)) (len flags : Words16) (lane : Fin 16) :
    (fun i => (initial cv len flags i)[lane]) =
      scalarInit (project cv lane) 0 len[lane] flags[lane] := by
  funext i
  fin_cases i <;> simp [initial, scalarInit, initState, project]

theorem seven_cv (cv : CV (Lanes 16)) (len flags : Words16) (m : State Words16)
    (lane : Fin 16) (word : Fin 8) :
    upperCV (sevenRounds gVectors (initial cv len flags) m) word lane ^^^
      lowerCV (sevenRounds gVectors (initial cv len flags) m) word lane =
    scalarCompressCV (project cv lane) (fun i => (m i)[lane]) 0 len[lane] flags[lane] word := by
  have hv : (fun i => (sevenRounds gVectors (initial cv len flags) m i)[lane]) =
      scalarCompressPre (project cv lane) (fun i => (m i)[lane]) 0 len[lane] flags[lane] := by
    rw [sevenRounds, rounds_vectors_lane, initial_lane]
    rfl
  have hlo := congrFun hv (word.castAdd 8)
  have hhi := congrFun hv ⟨word.val+8, by omega⟩
  unfold upperCV lowerCV
  change (sevenRounds gVectors (initial cv len flags) m ⟨word.val, by omega⟩)[lane] = _ at hlo
  rw [hhi, hlo]
  simp only [scalarCompressCV, scalarCompress, feedForward, Fin.val_castAdd, word.isLt, ↓reduceDIte]
  exact BitVec.xor_comm _ _

end AgaveLatticeHash.MLIR.BatchNonrootRounds16
