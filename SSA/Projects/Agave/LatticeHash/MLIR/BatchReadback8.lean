/- Released under Apache 2.0 license as described in the file LICENSE. -/
import SSA.Projects.Agave.LatticeHash.MLIR.BatchExecution8

namespace AgaveLatticeHash.MLIR.BatchReadback8
open LeanMLIR SLLVM Firedancer Blake3Compression
open InstCombine (LLVM)
open BatchXofLoop BatchReduction
set_option maxRecDepth 4096
set_option maxHeartbeats 1500000

/-- Once every lane reaches its root, the emitted compression parameters
are precisely the scalar one-chunk XOF parameters. -/
theorem rootCompression_eq (p : AgavePhysicalStaging.Store)
    (ms : Fin 8 → AgaveConcrete.Message) (t : Nat)
    (hstage : ∀ lane, AgaveBatchControl.ValidStaging (ms lane).length 1024
      (AgaveConcrete.bytes (ms lane)) (AgavePhysicalStaging.memoryAt p lane.val))
    (hdone : ∀ lane, AgaveBatchControl.rootIndex (ms lane).length ≤ t)
    (counter : Fin 32) (lane : Fin 8) :
    scalarCompress (fun word => (BatchRootXof.rootCV ms t word)[lane])
      (fun word => (BatchReadInput8.columns p ms t word)[lane])
      (BitVec.ofNat 64 counter.val) (BatchInputSuccessor.sizes ms t)[lane]
      (BatchInputSuccessor.flags ms t)[lane] =
      AgaveConcrete.oneChunkWords (ms lane) counter := by
  have hm : (fun word => (BatchReadInput8.columns p ms t word)[lane]) =
      AgaveConcrete.decodeBlock (AgaveBatchControl.scalarBlock (AgaveConcrete.bytes (ms lane))
        (ms lane).length (AgaveBatchControl.rootIndex (ms lane).length)) := by
    funext word
    simpa only [BatchReadInput8.columns, Fin.getElem_fin, Nat.min_eq_right (hdone lane)] using
      CallerMemory.columns8_scalarBlock p ms t hstage word lane
  rw [hm]
  simp only [BatchRootXof.rootCV, BatchUpdate.stateCV8,
    BatchInputSuccessor.sizes, BatchInputSuccessor.flags, Fin.getElem_fin, Vector.getElem_ofFn,
    AgaveBatchControl.stateAt, batchOffset, Nat.min_eq_right (hdone lane),
    AgaveBatchControl.root_size, AgaveBatchControl.root_flags,
    AgaveConcrete.oneChunkWords, AgaveBatchControl.scalarXofAt, AgaveConcrete.xof,
    AgaveConcrete.counter, Nat.mul_zero, Nat.add_zero]

/-- Reading completed explicit output stores needs no assumptions about
schedule or message memory. -/
theorem completed_reads (s : GlobalState) (out : Pointer)
    (cv : CV Words8) (len flags : Words8) (m : State Words8)
    (lo hi : Nat → Vector (BitVec 16) 16)
    (hf : Fits s.mem out 16384) (hw : out.offset.toNat + 2048 ≤ 2^64)
    (num c : Nat) (hn : num ≤ 32) (hc : c < num) :
    readWord? (outputPtr out c) 256
        (accumulatedState s out (out.withOffset 32) cv len flags m lo hi num).mem =
      some (packBits (BatchOutput.sums16 (lo c) (lowerDelta cv len flags m c))) ∧
    readWord? (outputPtr (out.withOffset 32) c) 256
        (accumulatedState s out (out.withOffset 32) cv len flags m lo hi num).mem =
      some (packBits (BatchOutput.sums16 (hi c) (upperDelta cv len flags m c))) := by
  induction num with
  | zero => omega
  | succ k ih =>
    have hk : k < 32 := by omega
    have hc32 : c < 32 := by omega
    have kl := outputPtr_offset out hw k hk
    have kh := outputPtr_high_offset out hw k hk
    have cl := outputPtr_offset out hw c hc32
    have ch := outputPtr_high_offset out hw c hc32
    by_cases he : c = k
    · subst c
      have fl : Fits s.mem (outputPtr out k) 256 := by
        obtain ⟨b, hb, hn⟩ := hf
        refine ⟨b, hb, ?_⟩
        rw [kl]
        omega
      have fh : Fits s.mem (outputPtr (out.withOffset 32) k) 256 := by
        obtain ⟨b, hb, hn⟩ := hf
        refine ⟨b, hb, ?_⟩
        rw [kh]
        omega
      constructor
      · simp only [accumulatedState, accumulate]
        rw [readWord?_splice_disjoint _ (Or.inr (by rw [kl, kh]; omega))]
        exact readWord?_splice_self _ (fits_accumulatedState _ _ _ _ _ _ _ _ _ _ fl)
      · simp only [accumulatedState, accumulate]
        exact readWord?_splice_self _ (fits_splice (fits_accumulatedState _ _ _ _ _ _ _ _ _ _ fh))
    · obtain ⟨ihl, ihh⟩ := ih (by omega) (by omega)
      constructor
      · simp only [accumulatedState, accumulate]
        rw [readWord?_splice_disjoint _ (Or.inr (by rw [kh, cl]; omega)),
          readWord?_splice_disjoint _ (Or.inr (by rw [kl, cl]; omega))]
        exact ihl
      · simp only [accumulatedState, accumulate]
        rw [readWord?_splice_disjoint _ (Or.inr (by rw [kh, ch]; omega)),
          readWord?_splice_disjoint _ (Or.inr (by rw [kl, ch]; omega))]
        exact ihh

/-- Every concrete little-endian u16 cell is observed at its actual byte offset. -/
theorem read_halfword (s : GlobalState) (out : Pointer)
    (cv : CV Words8) (len flags : Words8) (m : State Words8)
    (lo hi : Nat → Vector (BitVec 16) 16)
    (hf : Fits s.mem out 16384) (hw : out.offset.toNat + 2048 ≤ 2^64)
    (j : Fin 1024) :
    readWord? (out.withOffset (BitVec.ofNat 64 (2*j.val))) 16
      (accumulatedState s out (out.withOffset 32) cv len flags m lo hi 32).mem =
      some (if j.val%32 < 16 then
        (lo (j.val/32))[j.val%16] + (lowerDelta cv len flags m (j.val/32))[j.val%16]
      else (hi (j.val/32))[j.val%16] + (upperDelta cv len flags m (j.val/32))[j.val%16]) := by
  have hj := j.isLt
  have hc : j.val/32 < 32 := by omega
  have ol := outputPtr_offset out hw (j.val/32) hc
  have oh := outputPtr_high_offset out hw (j.val/32) hc
  have oq : (out.withOffset (BitVec.ofNat 64 (2*j.val))).offsetInBits =
      out.offsetInBits + 16*j.val := by
    rw [offsetInBits_withOffset_nat out (2*j.val) (by omega)]
    omega
  have hfit := fits_accumulatedState s out (out.withOffset 32) cv len flags m lo hi 32 hf
  have hread := completed_reads s out cv len flags m lo hi hf hw 32 (j.val/32) (by omega) hc
  by_cases hl : j.val%32 < 16
  · simp only [hl, reduceIte]
    have fp : Fits (accumulatedState s out (out.withOffset 32) cv len flags m lo hi 32).mem
        (outputPtr out (j.val/32)) 256 := by
      obtain ⟨b, hb, hn⟩ := hfit
      refine ⟨b, hb, ?_⟩
      rw [ol]
      omega
    have hoff : (out.withOffset (BitVec.ofNat 64 (2*j.val))).offsetInBits =
        (outputPtr out (j.val/32)).offsetInBits + (j.val%16)*16 := by
      rw [oq, ol]
      omega
    have hr := readWord?_extract _ fp hread.1 (q := out.withOffset (BitVec.ofNat 64 (2*j.val)))
      rfl hoff (show (j.val%16)*16+16 ≤ 256 by omega)
    rw [extract_packBits _ ⟨j.val%16, by omega⟩] at hr
    simpa only [BatchOutput.sums16, Fin.getElem_fin, Vector.getElem_ofFn] using hr
  · simp only [hl, reduceIte]
    have fp : Fits (accumulatedState s out (out.withOffset 32) cv len flags m lo hi 32).mem
        (outputPtr (out.withOffset 32) (j.val/32)) 256 := by
      obtain ⟨b, hb, hn⟩ := hfit
      refine ⟨b, hb, ?_⟩
      rw [oh]
      omega
    have hoff : (out.withOffset (BitVec.ofNat 64 (2*j.val))).offsetInBits =
        (outputPtr (out.withOffset 32) (j.val/32)).offsetInBits + (j.val%16)*16 := by
      rw [oq, oh]
      omega
    have hr := readWord?_extract _ fp hread.2 (q := out.withOffset (BitVec.ofNat 64 (2*j.val)))
      rfl hoff (show (j.val%16)*16+16 ≤ 256 by omega)
    rw [extract_packBits _ ⟨j.val%16, by omega⟩] at hr
    simpa only [BatchOutput.sums16, Fin.getElem_fin, Vector.getElem_ofFn] using hr

theorem lowerDelta_root (p : AgavePhysicalStaging.Store)
    (ms : Fin 8 → AgaveConcrete.Message) (t : Nat)
    (hstage : ∀ lane, AgaveBatchControl.ValidStaging (ms lane).length 1024
      (AgaveConcrete.bytes (ms lane)) (AgavePhysicalStaging.memoryAt p lane.val))
    (hdone : ∀ lane, AgaveBatchControl.rootIndex (ms lane).length ≤ t)
    (j : Fin 1024) (hl : j.val%32 < 16) :
    (lowerDelta (BatchRootXof.rootCV ms t) (BatchInputSuccessor.sizes ms t)
      (BatchInputSuccessor.flags ms t) (BatchReadInput8.columns p ms t) (j.val/32))[j.val%16] =
      sum8 (fun lane => AgaveConcrete.oneChunk (ms lane) j) := by
  have hj := j.isLt
  have hd := lowerDelta_scalar (BatchRootXof.rootCV ms t) (BatchInputSuccessor.sizes ms t)
    (BatchInputSuccessor.flags ms t) (BatchReadInput8.columns p ms t) (j.val/32)
    (show j.val/32 < 32 by omega) ⟨j.val%16, by omega⟩
  simp only [Fin.getElem_fin] at hd
  rw [hd]
  apply congrArg sum8
  funext lane
  have hr := rootCompression_eq p ms t hstage hdone ⟨j.val/32, by omega⟩ lane
  simp only [Fin.getElem_fin] at hr
  rw [hr]
  unfold AgaveConcrete.oneChunk
  have hw : (⟨(j.val%16)/2, by omega⟩ : Fin 16) = ⟨j.val%32/2, by omega⟩ := by
    apply Fin.ext
    dsimp only
    omega
  have hh : (⟨(j.val%16)%2, by omega⟩ : Fin 2) = ⟨j.val%2, by omega⟩ := by
    apply Fin.ext
    dsimp only
    omega
  rw [hw, hh]

theorem upperDelta_root (p : AgavePhysicalStaging.Store)
    (ms : Fin 8 → AgaveConcrete.Message) (t : Nat)
    (hstage : ∀ lane, AgaveBatchControl.ValidStaging (ms lane).length 1024
      (AgaveConcrete.bytes (ms lane)) (AgavePhysicalStaging.memoryAt p lane.val))
    (hdone : ∀ lane, AgaveBatchControl.rootIndex (ms lane).length ≤ t)
    (j : Fin 1024) (hl : ¬j.val%32 < 16) :
    (upperDelta (BatchRootXof.rootCV ms t) (BatchInputSuccessor.sizes ms t)
      (BatchInputSuccessor.flags ms t) (BatchReadInput8.columns p ms t) (j.val/32))[j.val%16] =
      sum8 (fun lane => AgaveConcrete.oneChunk (ms lane) j) := by
  have hj := j.isLt
  have hd := upperDelta_scalar (BatchRootXof.rootCV ms t) (BatchInputSuccessor.sizes ms t)
    (BatchInputSuccessor.flags ms t) (BatchReadInput8.columns p ms t) (j.val/32)
    (show j.val/32 < 32 by omega) ⟨j.val%16, by omega⟩
  simp only [Fin.getElem_fin] at hd
  rw [hd]
  apply congrArg sum8
  funext lane
  have hr := rootCompression_eq p ms t hstage hdone ⟨j.val/32, by omega⟩ lane
  simp only [Fin.getElem_fin] at hr
  rw [hr]
  unfold AgaveConcrete.oneChunk
  have hw : (⟨(j.val%16)/2+8, by omega⟩ : Fin 16) = ⟨j.val%32/2, by omega⟩ := by
    apply Fin.ext
    dsimp only
    omega
  have hh : (⟨(j.val%16)%2, by omega⟩ : Fin 2) = ⟨j.val%2, by omega⟩ := by
    apply Fin.ext
    dsimp only
    omega
  rw [hw, hh]

theorem scalarSum_physical (p : AgavePhysicalStaging.Store) (a : AgaveStaging.Value)
    (ms : Fin 8 → AgaveConcrete.Message)
    (hlen : ∀ lane, AgavePhysicalStaging.lengthAt p lane.val = (ms lane).length)
    (hms : ∀ lane, (ms lane).length ≤ 1024)
    (hstage : ∀ lane, AgaveBatchControl.ValidStaging (ms lane).length 1024
      (AgaveConcrete.bytes (ms lane)) (AgavePhysicalStaging.memoryAt p lane.val))
    (j : Fin 1024) :
    a j + sum8 (fun lane => AgaveConcrete.oneChunk (ms lane) j) =
      AgavePhysicalStaging.physicalUpdate 8 (by decide)
        (AgaveLattice.transpose8 AgaveLattice.labels) p a j := by
  have hl : (fun lane : Fin 8 => AgavePhysicalStaging.lengthAt p lane.val) =
      (fun lane => (ms lane).length) := funext hlen
  unfold AgavePhysicalStaging.physicalUpdate
  rw [hl, AgavePhysicalStaging.retainedUpdate_eq_fold (by decide)
    AgaveLattice.avx2_isTranspose ms _ hms hstage a, AgaveConcrete.value_foldl_apply]
  simp [sum8, List.finRange_succ, BitVec.add_assoc]

/-- The exact final state of the compiled batch yields the retained-memory
LtHash update at every actual output address. -/
theorem finish_read {entry current : GlobalState} {src len out sched panic : Pointer}
    {p : AgavePhysicalStaging.Store} {a : AgaveStaging.Value}
    (hrep : CallerMemory.Represents entry 8 src len out sched panic p a)
    (hm : BatchMemory8 entry current) (ms : Fin 8 → AgaveConcrete.Message) (t : Nat)
    (hlen : ∀ lane, AgavePhysicalStaging.lengthAt p lane.val = (ms lane).length)
    (hms : ∀ lane, (ms lane).length ≤ 1024)
    (hstage : ∀ lane, AgaveBatchControl.ValidStaging (ms lane).length 1024
      (AgaveConcrete.bytes (ms lane)) (AgavePhysicalStaging.memoryAt p lane.val))
    (hdone : ∀ lane, AgaveBatchControl.rootIndex (ms lane).length ≤ t)
    (bytes : BitVec 4096) (j : Fin 1024) :
    readWord? (out.withOffset (BitVec.ofNat 64 (2*j.val))) 16
      (BatchExecution8.finishState entry current out p a ms t bytes).mem =
      some (AgavePhysicalStaging.physicalUpdate 8 (by decide)
        (AgaveLattice.transpose8 AgaveLattice.labels) p a j) := by
  have hf : Fits (current.mem.splice (BatchEntry.scratch entry 1) bytes) out 16384 :=
    fits_splice (hm.fits hrep.wf hrep.accumulator.2.1)
  have hw : out.offset.toNat + 2048 ≤ 2^64 := by simp [hrep.out_zero]
  have hj := j.isLt
  have hc : j.val/32 < 32 := by omega
  unfold BatchExecution8.finishState
  rw [read_halfword _ _ _ _ _ _ _ _ hf hw j]
  apply congrArg some
  rw [← scalarSum_physical p a ms hlen hms hstage j]
  by_cases hl : j.val%32 < 16
  · simp only [hl, reduceIte]
    rw [lowerDelta_root p ms t hstage hdone j hl]
    congr 1
    simp only [lowerSlice, CallerMemory.accumulatorWords, Vector.getElem_ofFn, Nat.mod_eq_of_lt hc]
    congr 1
    apply Fin.ext
    dsimp only
    omega
  · simp only [hl, reduceIte]
    rw [upperDelta_root p ms t hstage hdone j hl]
    congr 1
    simp only [upperSlice, CallerMemory.accumulatorWords, Vector.getElem_ofFn, Nat.mod_eq_of_lt hc]
    congr 1
    apply Fin.ext
    dsimp only
    omega

end AgaveLatticeHash.MLIR.BatchReadback8
