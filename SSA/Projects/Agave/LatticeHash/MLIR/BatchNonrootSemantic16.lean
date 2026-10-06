/- Released under Apache 2.0 license as described in the file LICENSE. -/
import SSA.Projects.Agave.LatticeHash.MLIR.BatchNonrootData16
import SSA.Projects.Agave.LatticeHash.MLIR.CallerBatch16

namespace AgaveLatticeHash.MLIR.BatchNonrootSemantic16
open LeanMLIR SLLVM Firedancer Blake3Compression
open InstCombine (LLVM)
open BatchNonrootRounds16
set_option maxRecDepth 8192
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

def sizes16 (ms : Fin 16 → AgaveConcrete.Message) (t : Nat) : Words16 :=
  Vector.ofFn fun lane => BitVec.ofNat 32
    (AgaveBatchControl.blockSize (ms lane).length (batchOffset (ms lane).length t))
def flags16 (ms : Fin 16 → AgaveConcrete.Message) (t : Nat) : Words16 :=
  Vector.ofFn fun lane => BitVec.ofNat 32
    (AgaveBatchControl.blockFlags (ms lane).length (batchOffset (ms lane).length t))

def finalState (p : AgavePhysicalStaging.Store) (ms : Fin 16 → AgaveConcrete.Message)
    (t : Nat) : State Words16 :=
  sevenRounds gVectors
    (initial (BatchUpdate16.stateCV16 ms t) (sizes16 ms t) (flags16 ms t))
    (BatchTranspose16.columns16 (CallerMemory.rows16 p ms t))

theorem compression_active (p : AgavePhysicalStaging.Store)
    (ms : Fin 16 → AgaveConcrete.Message) (t : Nat)
    (hstage : ∀ lane, AgaveBatchControl.ValidStaging (ms lane).length 1024
      (AgaveConcrete.bytes (ms lane)) (AgavePhysicalStaging.memoryAt p lane.val))
    (lane : Fin 16) (ha : t < AgaveBatchControl.rootIndex (ms lane).length) (word : Fin 8) :
    upperCV (finalState p ms t) word lane ^^^ lowerCV (finalState p ms t) word lane =
      AgaveConcrete.compress
        (AgaveBatchControl.stateAt AgaveConcrete.compress AgaveConcrete.iv
          (AgaveConcrete.bytes (ms lane)) (ms lane).length t).cv
        (AgaveBatchControl.scalarBlock (AgaveConcrete.bytes (ms lane)) (ms lane).length
          (min t (AgaveBatchControl.rootIndex (ms lane).length)))
        0 0 64 (if min t (AgaveBatchControl.rootIndex (ms lane).length) = 0 then 1 else 0) word := by
  unfold finalState
  rw [seven_cv]
  have hm : (fun i => (BatchTranspose16.columns16 (CallerMemory.rows16 p ms t) i)[lane]) =
      AgaveConcrete.decodeBlock (AgaveBatchControl.scalarBlock (AgaveConcrete.bytes (ms lane))
        (ms lane).length (min t (AgaveBatchControl.rootIndex (ms lane).length))) := by
    funext i
    exact CallerMemory.columns16_scalarBlock p ms t hstage i lane
  rw [hm]
  have hj : min t (AgaveBatchControl.rootIndex (ms lane).length) = t := Nat.min_eq_left (Nat.le_of_lt ha)
  have hsize : AgaveBatchControl.blockSize (ms lane).length (batchOffset (ms lane).length t) = 64 := by
    simpa only [batchOffset, hj] using AgaveBatchControl.active_size (ms lane).length t ha
  have hflags : AgaveBatchControl.blockFlags (ms lane).length (batchOffset (ms lane).length t) =
      if t = 0 then 1 else 0 := by
    simpa only [batchOffset, hj] using AgaveBatchControl.active_flags (ms lane).length t ha
  simp only [sizes16, flags16, Fin.getElem_fin, Vector.getElem_ofFn, hsize, hflags, hj]
  rfl

/-- The actual masked update returns to the next scalar-prefix header. -/
theorem update_run (entry current : GlobalState) (src len out sched panic : Pointer)
    (lengthsLo lengthsHi : Vector (BitVec 64) 8)
    (p : AgavePhysicalStaging.Store) (ms : Fin 16 → AgaveConcrete.Message) (t : Nat)
    (hms : ∀ lane, (ms lane).length ≤ 1024)
    (hstage : ∀ lane, AgaveBatchControl.ValidStaging (ms lane).length 1024
      (AgaveConcrete.bytes (ms lane)) (AgavePhysicalStaging.memoryAt p lane.val)) :
    let B := BatchEntry16.entryVal16 entry src len out sched panic lengthsLo lengthsHi
    let e := extras (BatchUpdate16.stateCV16 ms t) (BatchUpdate16.offsetsAt16 ms t)
      (BatchUpdate16.activeAt16 ms t)
    StateT.run (agave_batch_16.blocks.run B (updateTarget e (finalState p ms t))) current =
      StateT.run (agave_batch_16.blocks.run B (headerAt16 ms (t+1))) current := by
  dsimp only
  let B := BatchEntry16.entryVal16 entry src len out sched panic lengthsLo lengthsHi
  let e := extras (BatchUpdate16.stateCV16 ms t) (BatchUpdate16.offsetsAt16 ms t)
    (BatchUpdate16.activeAt16 ms t)
  have he := update_env entry src len out sched panic lengthsLo lengthsHi
    (BatchUpdate16.stateCV16 ms t) (BatchUpdate16.offsetsAt16 ms t)
    (BatchUpdate16.activeAt16 ms t) (finalState p ms t)
  have hrun := BatchUpdate16.update16_stateAt (updateVal B e (finalState p ms t)) current ms t
    (upperCV (finalState p ms t)) (lowerCV (finalState p ms t)) he hms
    (compression_active p ms t hstage)
  denote_enter_block
  apply EffectM.run_bind_of_value hrun

/-- Actual block 6 and all seven round iterations reach the actual update block. -/
theorem init_seven_rounds_run (B : agave_batch_16.cfgCtx.Valuation) (hB : InitEnv B)
    (cv : CV (Lanes 16)) (len flags : Words16)
    (packedLen packedFlags : Vector (LLVM.IntW 64) 8)
    (offsets : Vector (BitVec 64) 16) (active : Fin 16 → Bool)
    (hl : BatchPaths16.words16 packedLen = len.map PoisonOr.value)
    (hf : BatchPaths16.words16 packedFlags = flags.map PoisonOr.value)
    (msg sched : Pointer) (m : State Words16)
    (hA : CompressionRound.RoundEnv16
      (sourceVal B (extras cv offsets active) 0 (initial cv len flags)) msg sched)
    (s : GlobalState)
    (hsi : ∀ r i, Fits s.mem (CompressionRound.schedulePtr16 sched r i) 64)
    (hsv : ∀ r i, readWord? (CompressionRound.schedulePtr16 sched r i) 64 s.mem =
      some (BitVec.ofNat 64 (schedule r i).val))
    (hmi : ∀ i, Fits s.mem (CompressionRound.messagePtr16 msg i) 512)
    (hmv : ∀ i, readWord? (CompressionRound.messagePtr16 msg i) 512 s.mem = some (packBits (m i))) :
    StateT.run (agave_batch_16.blocks.run B
      (initTarget cv packedLen packedFlags offsets active)) s =
      StateT.run (agave_batch_16.blocks.run B
        (updateTarget (extras cv offsets active)
          (sevenRounds gVectors (initial cv len flags) m))) s := by
  change StateT.run (agave_batch_16.blocks.run B
    ⟨6, rfl, (initTarget cv packedLen packedFlags offsets active).args⟩) s = _
  rw [BatchPaths16.run6]
  change StateT.run (agave_batch_16.blocks.run B
    (BatchPaths16.next6 (initVal B cv packedLen packedFlags offsets active))) s = _
  rw [next6_initial B hB cv len flags packedLen packedFlags offsets active hl hf]
  exact seven_rounds_run B (extras cv offsets active) msg sched (initial cv len flags) m hA
    s hsi hsv hmi hmv

theorem initial_eq_laneInit (cv : CV (Lanes 16)) (len flags : Words16) :
    initial cv len flags = fun i => Vector.ofFn
      (laneInit cv (fun _ => 0) (fun lane => len[lane]) (fun lane => flags[lane]) i) := by
  funext i
  fin_cases i <;> apply Vector.ext <;> intro lane hlane <;>
    simp [initial, laneInit, initState, Fin.getElem_fin]

/-- Complete actual nonroot iteration, from block 6 through seven rounds and
masked CV update, preserving the current memory state. -/
theorem run (entry current : GlobalState) (src len out sched panic : Pointer)
    (lengthsLo lengthsHi : Vector (BitVec 64) 8)
    (p : AgavePhysicalStaging.Store) (ms : Fin 16 → AgaveConcrete.Message) (t : Nat)
    (packedLen packedFlags : Vector (LLVM.IntW 64) 8)
    (hms : ∀ lane, (ms lane).length ≤ 1024)
    (hstage : ∀ lane, AgaveBatchControl.ValidStaging (ms lane).length 1024
      (AgaveConcrete.bytes (ms lane)) (AgavePhysicalStaging.memoryAt p lane.val))
    (hl : BatchPaths16.words16 packedLen = (sizes16 ms t).map PoisonOr.value)
    (hf : BatchPaths16.words16 packedFlags = (flags16 ms t).map PoisonOr.value)
    (hsi : ∀ r i, Fits current.mem (CompressionRound.schedulePtr16 sched r i) 64)
    (hsv : ∀ r i, readWord? (CompressionRound.schedulePtr16 sched r i) 64 current.mem =
      some (BitVec.ofNat 64 (schedule r i).val))
    (hmi : ∀ i, Fits current.mem
      (CompressionRound.messagePtr16 (BatchEntry16.scratch entry 0) i) 512)
    (hmv : ∀ i, readWord? (CompressionRound.messagePtr16 (BatchEntry16.scratch entry 0) i)
      512 current.mem = some (packBits (BatchTranspose16.columns16 (CallerMemory.rows16 p ms t) i))) :
    let B := BatchEntry16.entryVal16 entry src len out sched panic lengthsLo lengthsHi
    StateT.run (agave_batch_16.blocks.run B
      (initTarget (BatchUpdate16.stateCV16 ms t) packedLen packedFlags
        (BatchUpdate16.offsetsAt16 ms t) (BatchUpdate16.activeAt16 ms t))) current =
      StateT.run (agave_batch_16.blocks.run B (headerAt16 ms (t+1))) current := by
  dsimp only
  rw [init_seven_rounds_run _ (init_env entry src len out sched panic lengthsLo lengthsHi)
    _ (sizes16 ms t) (flags16 ms t) _ _ _ _ hl hf
    (BatchEntry16.scratch entry 0) sched (BatchTranspose16.columns16 (CallerMemory.rows16 p ms t))
    (round_env entry src len out sched panic lengthsLo lengthsHi _ _ _ _ _)
    current hsi hsv hmi hmv]
  exact update_run entry current src len out sched panic lengthsLo lengthsHi p ms t hms hstage

end AgaveLatticeHash.MLIR.BatchNonrootSemantic16
