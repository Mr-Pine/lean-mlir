/- Released under Apache 2.0 license as described in the file LICENSE. -/
import SSA.Projects.Agave.LatticeHash.MLIR.BatchXofMemory16
import SSA.Projects.Agave.LatticeHash.MLIR.BatchRootScalar16

namespace AgaveLatticeHash.MLIR.BatchReadback16
open LeanMLIR SLLVM Firedancer Blake3Compression
open BatchXofLoop16 BatchReduction16
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] delta finalState scalarCompress rootCVAt16 rootSizes16 rootFlags16
  BatchTranspose16.columns16 CallerMemory.rows16 AgaveConcrete.oneChunkWords

/-- Completed 64-byte chunks determine every actual little-endian u16 read. -/
theorem chunks_read_halfword (final : GlobalState) (out : Pointer)
    (chunks : Nat → Vector (BitVec 16) 32)
    (hf : Fits final.mem out 16384) (hw : out.offset.toNat + 2048 ≤ 2^64)
    (hread : ∀ c, c < 32 → readWord? (outputPtr out c) 512 final.mem =
      some (packBits (chunks c))) (j : Fin 1024) :
    readWord? (out.withOffset (BitVec.ofNat 64 (2*j.val))) 16 final.mem =
      some ((chunks (j.val/32))[j.val%32]) := by
  have hj := j.isLt
  have hc : j.val/32 < 32 := by omega
  have op := outputPtr_offset out hw (j.val/32) hc
  have oq : (out.withOffset (BitVec.ofNat 64 (2*j.val))).offsetInBits =
      out.offsetInBits + 16*j.val := by
    rw [offsetInBits_withOffset_nat out (2*j.val) (by omega)]
    omega
  have fp : Fits final.mem (outputPtr out (j.val/32)) 512 := by
    obtain ⟨b, hb, hn⟩ := hf
    refine ⟨b, hb, ?_⟩
    rw [op]
    omega
  have hoff : (out.withOffset (BitVec.ofNat 64 (2*j.val))).offsetInBits =
      (outputPtr out (j.val/32)).offsetInBits + (j.val%32)*16 := by
    rw [oq, op]
    omega
  have hr := readWord?_extract _ fp (hread (j.val/32) hc)
    (q := out.withOffset (BitVec.ofNat 64 (2*j.val))) rfl hoff
    (show (j.val%32)*16+16 ≤ 512 by omega)
  rw [extract_packBits _ ⟨j.val%32, by omega⟩] at hr
  exact hr

/-- The sixteen scalar lane contributions use the exact global LtHash cell. -/
theorem delta_root (p : AgavePhysicalStaging.Store)
    (ms : Fin 16 → AgaveConcrete.Message) (t : Nat)
    (hstage : ∀ lane, AgaveBatchControl.ValidStaging (ms lane).length 1024
      (AgaveConcrete.bytes (ms lane)) (AgavePhysicalStaging.memoryAt p lane.val))
    (hdone : ∀ lane, AgaveBatchControl.rootIndex (ms lane).length ≤ t)
    (j : Fin 1024) :
    (delta (rootCVAt16 ms t) (rootSizes16 ms t) (rootFlags16 ms t)
      (BatchTranspose16.columns16 (CallerMemory.rows16 p ms t)) (j.val/32))[j.val%32] =
      sum16 (fun lane => AgaveConcrete.oneChunk (ms lane) j) := by
  have hj := j.isLt
  have hd := delta_scalar (rootCVAt16 ms t) (rootSizes16 ms t) (rootFlags16 ms t)
    (BatchTranspose16.columns16 (CallerMemory.rows16 p ms t)) (j.val/32)
    (show j.val/32 < 32 by omega) ⟨j.val%32, by omega⟩
  simp only [Fin.getElem_fin] at hd
  rw [hd]
  apply congrArg sum16
  funext lane
  have hr := rootCompression16_eq p ms t hstage hdone ⟨j.val/32, by omega⟩ lane
  simp only [Fin.getElem_fin] at hr
  rw [hr]
  unfold AgaveConcrete.oneChunk
  have hh : (⟨(j.val%32)%2, by omega⟩ : Fin 2) = ⟨j.val%2, by omega⟩ := by
    apply Fin.ext
    dsimp only
    omega
  rw [hh]

/-- The lane sum equals the retained-memory update with the actual AVX512 transpose. -/
theorem scalarSum_physical (p : AgavePhysicalStaging.Store) (a : AgaveStaging.Value)
    (ms : Fin 16 → AgaveConcrete.Message)
    (hlen : ∀ lane, AgavePhysicalStaging.lengthAt p lane.val = (ms lane).length)
    (hms : ∀ lane, (ms lane).length ≤ 1024)
    (hstage : ∀ lane, AgaveBatchControl.ValidStaging (ms lane).length 1024
      (AgaveConcrete.bytes (ms lane)) (AgavePhysicalStaging.memoryAt p lane.val))
    (j : Fin 1024) :
    a j + sum16 (fun lane => AgaveConcrete.oneChunk (ms lane) j) =
      AgavePhysicalStaging.physicalUpdate 16 (by decide)
        (AgaveLattice.transpose16 AgaveLattice.labels) p a j := by
  have hl : (fun lane : Fin 16 => AgavePhysicalStaging.lengthAt p lane.val) =
      (fun lane => (ms lane).length) := funext hlen
  unfold AgavePhysicalStaging.physicalUpdate
  rw [hl, AgavePhysicalStaging.retainedUpdate_eq_fold (by decide)
    AgaveLattice.avx512_isTranspose ms _ hms hstage a, AgaveConcrete.value_foldl_apply]
  simp [sum16, List.finRange_succ, BitVec.add_assoc]

attribute [local irreducible] AgavePhysicalStaging.physicalUpdate

/-- All completed root chunks imply the physical update at every real output address. -/
theorem finish_read (final : GlobalState) (out : Pointer)
    (p : AgavePhysicalStaging.Store) (a : AgaveStaging.Value)
    (ms : Fin 16 → AgaveConcrete.Message) (t : Nat)
    (hlen : ∀ lane, AgavePhysicalStaging.lengthAt p lane.val = (ms lane).length)
    (hms : ∀ lane, (ms lane).length ≤ 1024)
    (hstage : ∀ lane, AgaveBatchControl.ValidStaging (ms lane).length 1024
      (AgaveConcrete.bytes (ms lane)) (AgavePhysicalStaging.memoryAt p lane.val))
    (hdone : ∀ lane, AgaveBatchControl.rootIndex (ms lane).length ≤ t)
    (hf : Fits final.mem out 16384) (hw : out.offset.toNat + 2048 ≤ 2^64)
    (hread : ∀ c, c < 32 → readWord? (outputPtr out c) 512 final.mem =
      some (packBits (BatchOutput16.sums32
        (outputSlice (CallerMemory.accumulatorWords a) c)
        (delta (rootCVAt16 ms t) (rootSizes16 ms t) (rootFlags16 ms t)
          (BatchTranspose16.columns16 (CallerMemory.rows16 p ms t)) c))))
    (j : Fin 1024) :
    readWord? (out.withOffset (BitVec.ofNat 64 (2*j.val))) 16 final.mem =
      some (AgavePhysicalStaging.physicalUpdate 16 (by decide)
        (AgaveLattice.transpose16 AgaveLattice.labels) p a j) := by
  rw [chunks_read_halfword final out _ hf hw hread j]
  apply congrArg some
  simp only [BatchOutput16.sums32, Vector.getElem_ofFn, Fin.getElem_fin]
  rw [delta_root p ms t hstage hdone j, ← scalarSum_physical p a ms hlen hms hstage j]
  apply congrArg (fun x : BitVec 16 => x + sum16 (fun lane => AgaveConcrete.oneChunk (ms lane) j))
  have hj := j.isLt
  have hc : j.val/32 < 32 := by omega
  simp only [outputSlice, CallerMemory.accumulatorWords, Vector.getElem_ofFn, Nat.mod_eq_of_lt hc]
  congr 1
  apply Fin.ext
  dsimp only
  omega

end AgaveLatticeHash.MLIR.BatchReadback16
