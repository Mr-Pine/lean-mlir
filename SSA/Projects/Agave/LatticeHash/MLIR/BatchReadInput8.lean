/- Released under Apache 2.0 license as described in the file LICENSE. -/
import SSA.Projects.Agave.LatticeHash.MLIR.CallerBatch8
import SSA.Projects.Agave.LatticeHash.MLIR.BatchInputSuccessor

namespace AgaveLatticeHash.MLIR.BatchReadInput8
open LeanMLIR SLLVM Firedancer Blake3Compression CompressionExit
open BatchInputSuccessor

noncomputable abbrev ambient (entry : GlobalState) (src len out sched panic : Pointer)
    (ms : Fin 8 → AgaveConcrete.Message) :=
  BatchEntry.entryVal8 entry src len out sched panic
    (Vector.ofFn fun lane => BitVec.ofNat 64 (ms lane).length)

def columns (p : AgavePhysicalStaging.Store) (ms : Fin 8 → AgaveConcrete.Message)
    (iteration : Nat) : State (Vector Word 8) :=
  BatchTranspose.columns8
    (BatchTransposePath.lowColumns (CallerMemory.rows8 p ms iteration 0))
    (CallerMemory.rows8 p ms iteration 1)

def afterInput (entry current : GlobalState) (p : AgavePhysicalStaging.Store)
    (ms : Fin 8 → AgaveConcrete.Message) (iteration : Nat) : GlobalState :=
  {current with mem := outputMem (BatchEntry.scratch entry 0) (columns p ms iteration) 16 current.mem}

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
/-- Execute the compiled header and complete input path from retained caller
bytes. The result uses only the scalar-prefix CV, header metadata and the
stored transposed message; no per-instruction or per-load assumptions remain. -/
theorem run {entry current : GlobalState} {src len out sched panic : Pointer}
    {p : AgavePhysicalStaging.Store} {a : AgaveStaging.Value}
    (hrep : CallerMemory.Represents entry 8 src len out sched panic p a)
    (hm : BatchMemory8 entry current) (ms : Fin 8 → AgaveConcrete.Message)
    (iteration : Nat) (hms : ∀ lane, (ms lane).length ≤ 1024) :
    StateT.run (agave_batch_8.blocks.run (ambient entry src len out sched panic ms)
      (headerAt8 ms iteration)) current =
    StateT.run (agave_batch_8.blocks.run (ambient entry src len out sched panic ms)
      (if ∀ lane, AgaveBatchControl.rootIndex (ms lane).length ≤ iteration
        then rootAt ms iteration else nonrootAt ms iteration))
      (afterInput entry current p ms iteration) := by
  obtain ⟨hfl, hrl, hfh, hrh⟩ := CallerMemory.represented_loads8 hrep hm ms iteration hms
  have hexec := BatchTransposePath.run entry current src len out sched panic ms iteration hms
    (CallerMemory.rows8 p ms iteration 0) (CallerMemory.rows8 p ms iteration 1)
    hfl hrl hfh hrh (fun k hk => compressionSlotFits8 (hm.scratch 0) k hk)
  let A := ambient entry src len out sched panic ms
  let W := headerAt8Val A ms iteration
  have hroot : BatchTranspose.rootTarget8 (BatchSecondHalf.transposeInput A ms iteration
      (CallerMemory.rows8 p ms iteration 0) (CallerMemory.rows8 p ms iteration 1)) = root W :=
    root_eq A W (CallerMemory.rows8 p ms iteration 0) (CallerMemory.rows8 p ms iteration 1)
  have hnonroot : BatchTranspose.nonrootTarget8 (BatchSecondHalf.transposeInput A ms iteration
      (CallerMemory.rows8 p ms iteration 0) (CallerMemory.rows8 p ms iteration 1)) = nonroot W :=
    nonroot_eq A W (CallerMemory.rows8 p ms iteration 0) (CallerMemory.rows8 p ms iteration 1)
  have hrootSem : root W = rootAt ms iteration :=
    root_represented entry src len out sched panic ms iteration hms
  have hnonrootSem : nonroot W = nonrootAt ms iteration :=
    nonroot_represented entry src len out sched panic ms iteration hms
  dsimp only at hexec
  rw [hroot, hnonroot, hrootSem, hnonrootSem] at hexec
  simp only [BatchTransposePath.mask_zero_iff] at hexec
  exact hexec

theorem memory {entry current : GlobalState} (hm : BatchMemory8 entry current)
    (p : AgavePhysicalStaging.Store) (ms : Fin 8 → AgaveConcrete.Message) (iteration : Nat) :
    BatchMemory8 entry (afterInput entry current p ms iteration) :=
  hm.transpose 0 (BatchTransposePath.lowColumns (CallerMemory.rows8 p ms iteration 0))
    (CallerMemory.rows8 p ms iteration 1)

theorem message {entry current : GlobalState} (hm : BatchMemory8 entry current)
    (p : AgavePhysicalStaging.Store) (ms : Fin 8 → AgaveConcrete.Message) (iteration : Nat) :
    CompressionMessage (afterInput entry current p ms iteration).mem
      (BatchEntry.scratch entry 0) (columns p ms iteration) := by
  dsimp only [afterInput, columns]
  exact hm.message (BatchTransposePath.lowColumns (CallerMemory.rows8 p ms iteration 0))
    (CallerMemory.rows8 p ms iteration 1)

end AgaveLatticeHash.MLIR.BatchReadInput8
