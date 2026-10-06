/- Released under Apache 2.0 license as described in the file LICENSE. -/
import SSA.Projects.Agave.LatticeHash.MLIR.BatchNonrootData8
import SSA.Projects.Agave.LatticeHash.MLIR.BatchReadInput8

namespace AgaveLatticeHash.MLIR.BatchNonrootSemantic8
open LeanMLIR SLLVM Firedancer Blake3Compression
open InstCombine (LLVM)
open BatchNonrootRounds8

set_option maxRecDepth 4096 in
theorem init_env (entry : GlobalState) (src len out sched panic : Pointer)
    (ms : Fin 8 → AgaveConcrete.Message) :
    InitEnv (BatchReadInput8.ambient entry src len out sched panic ms) := by
  constructor <;> rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
theorem round_env (entry : GlobalState) (src len out sched panic : Pointer)
    (ms : Fin 8 → AgaveConcrete.Message)
    (cv : CV (Lanes 8)) (offsets advanced : Vector (BitVec 64) 8)
    (active : Fin 8 → Bool) (r : BitVec 64) (v : State Words8) :
    CompressionRound.RoundEnv8
      (sourceVal (BatchReadInput8.ambient entry src len out sched panic ms)
        (extras cv offsets advanced active) r v) (BatchEntry.scratch entry 0) sched := by
  constructor <;> rfl

theorem nonroot_target (ms : Fin 8 → AgaveConcrete.Message) (t : Nat) :
    BatchInputSuccessor.nonrootAt ms t =
      initTarget (BatchUpdate.stateCV8 ms t) (BatchInputSuccessor.sizes ms t)
        (BatchInputSuccessor.flags ms t) (BatchUpdate.offsetsAt8 ms t)
        (BatchUpdate.advancedAt8 ms t) (BatchUpdate.activeAt8 ms t) := by
  unfold BatchInputSuccessor.nonrootAt initTarget extras BatchUpdate.active8
    BatchUpdate.activeAt8 BatchTransposePath.activeVector
  simp only [Vector.map_ofFn]
  rfl


theorem initial_lane (cv : CV (Lanes 8)) (len flags : Words8) (lane : Fin 8) :
    (fun i => (initial cv len flags i)[lane]) =
      scalarInit (project cv lane) 0 len[lane] flags[lane] := by
  funext i
  fin_cases i <;> simp [initial, scalarInit, initState, project]

theorem seven_cv (cv : CV (Lanes 8)) (len flags : Words8) (m : State Words8)
    (lane : Fin 8) (word : Fin 8) :
    upperCV (sevenRounds gVectors (initial cv len flags) m) word lane ^^^
      lowerCV (sevenRounds gVectors (initial cv len flags) m) word lane =
    scalarCompressCV (project cv lane) (fun i => (m i)[lane]) 0 len[lane] flags[lane] word := by
  have hv : (fun i => (sevenRounds gVectors (initial cv len flags) m i)[lane]) =
      scalarCompressPre (project cv lane) (fun i => (m i)[lane]) 0 len[lane] flags[lane] := by
    rw [sevenRounds, rounds_vectors_lane, initial_lane]
    rfl
  have hlo : (sevenRounds gVectors (initial cv len flags) m ⟨word.val, by omega⟩)[lane] =
      scalarCompressPre (project cv lane) (fun i => (m i)[lane]) 0 len[lane] flags[lane]
        ⟨word.val, by omega⟩ := congrFun hv (word.castAdd 8)
  have hhi := congrFun hv ⟨word.val+8, by omega⟩
  unfold upperCV lowerCV
  rw [hlo, hhi]
  simp only [scalarCompressCV, scalarCompress, feedForward, Fin.val_castAdd, word.isLt, ↓reduceDIte]
  exact BitVec.xor_comm _ _


def finalState (p : AgavePhysicalStaging.Store) (ms : Fin 8 → AgaveConcrete.Message)
    (t : Nat) : State Words8 :=
  sevenRounds gVectors
    (initial (BatchUpdate.stateCV8 ms t) (BatchInputSuccessor.sizes ms t) (BatchInputSuccessor.flags ms t))
    (BatchReadInput8.columns p ms t)

theorem compression_active (p : AgavePhysicalStaging.Store)
    (ms : Fin 8 → AgaveConcrete.Message) (t : Nat)
    (hstage : ∀ lane, AgaveBatchControl.ValidStaging (ms lane).length 1024
      (AgaveConcrete.bytes (ms lane)) (AgavePhysicalStaging.memoryAt p lane.val))
    (lane : Fin 8) (ha : t < AgaveBatchControl.rootIndex (ms lane).length) (word : Fin 8) :
    upperCV (finalState p ms t) word lane ^^^ lowerCV (finalState p ms t) word lane =
      AgaveConcrete.compress
        (AgaveBatchControl.stateAt AgaveConcrete.compress AgaveConcrete.iv
          (AgaveConcrete.bytes (ms lane)) (ms lane).length t).cv
        (AgaveBatchControl.scalarBlock (AgaveConcrete.bytes (ms lane)) (ms lane).length
          (min t (AgaveBatchControl.rootIndex (ms lane).length)))
        0 0 64 (if min t (AgaveBatchControl.rootIndex (ms lane).length) = 0 then 1 else 0) word := by
  unfold finalState
  rw [seven_cv]
  have hm : (fun i => (BatchReadInput8.columns p ms t i)[lane]) =
      AgaveConcrete.decodeBlock (AgaveBatchControl.scalarBlock (AgaveConcrete.bytes (ms lane))
        (ms lane).length (min t (AgaveBatchControl.rootIndex (ms lane).length))) := by
    funext i
    exact CallerMemory.columns8_scalarBlock p ms t hstage i lane
  rw [hm]
  have hj : min t (AgaveBatchControl.rootIndex (ms lane).length) = t := Nat.min_eq_left (Nat.le_of_lt ha)
  have hsize : AgaveBatchControl.blockSize (ms lane).length (batchOffset (ms lane).length t) = 64 := by
    simpa only [batchOffset, hj] using AgaveBatchControl.active_size (ms lane).length t ha
  have hflags : AgaveBatchControl.blockFlags (ms lane).length (batchOffset (ms lane).length t) =
      if t = 0 then 1 else 0 := by
    simpa only [batchOffset, hj] using AgaveBatchControl.active_flags (ms lane).length t ha
  simp only [BatchInputSuccessor.sizes, BatchInputSuccessor.flags,
    Fin.getElem_fin, Vector.getElem_ofFn, hsize, hflags, hj]
  rfl

end AgaveLatticeHash.MLIR.BatchNonrootSemantic8
