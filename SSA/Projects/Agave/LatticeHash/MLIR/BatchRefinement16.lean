/- Released under Apache 2.0 license as described in the file LICENSE. -/
import SSA.Projects.Agave.LatticeHash.MLIR.BatchDispatch16
import SSA.Projects.Agave.LatticeHash.MLIR.BatchTransposeRun16
import SSA.Projects.Agave.LatticeHash.MLIR.BatchInvariantMask16
import SSA.Projects.Agave.LatticeHash.MLIR.BatchMemory16

namespace AgaveLatticeHash.MLIR.BatchRefinement16
open LeanMLIR SLLVM Firedancer Blake3Compression CompressionExit
open InstCombine (LLVM)

/-- The exact valuation at the compiled transpose after the header and guards. -/
noncomputable def transposeInput (A : agave_batch_16.cfgCtx.Valuation)
    (V : BatchHeader16.Input16.Valuation) : BatchTranspose16.InCtx16.Valuation :=
  BatchTransposeRun16.input2 A
    (BatchGuards16.next1 (input1 A (BatchHeader16.next16 V).args)).args

attribute [local irreducible] BatchHeader16.values16

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
/-- Threaded arguments preserve all sixteen computed load addresses and the
activity mask; scratch pointers remain in the shared ambient valuation. -/
theorem transpose_env (A : agave_batch_16.cfgCtx.Valuation)
    (V : BatchHeader16.Input16.Valuation) (out : Pointer)
    (inputs : Fin 16 → Pointer) (mask : BitVec 16)
    (hi0 : BatchHeader16.values16 V ⟨15, rfl⟩ = PoisonOr.value (inputs 0))
    (hi1 : BatchHeader16.values16 V ⟨14, rfl⟩ = PoisonOr.value (inputs 1))
    (hi2 : BatchHeader16.values16 V ⟨13, rfl⟩ = PoisonOr.value (inputs 2))
    (hi3 : BatchHeader16.values16 V ⟨12, rfl⟩ = PoisonOr.value (inputs 3))
    (hi4 : BatchHeader16.values16 V ⟨11, rfl⟩ = PoisonOr.value (inputs 4))
    (hi5 : BatchHeader16.values16 V ⟨10, rfl⟩ = PoisonOr.value (inputs 5))
    (hi6 : BatchHeader16.values16 V ⟨9, rfl⟩ = PoisonOr.value (inputs 6))
    (hi7 : BatchHeader16.values16 V ⟨8, rfl⟩ = PoisonOr.value (inputs 7))
    (hi8 : BatchHeader16.values16 V ⟨7, rfl⟩ = PoisonOr.value (inputs 8))
    (hi9 : BatchHeader16.values16 V ⟨6, rfl⟩ = PoisonOr.value (inputs 9))
    (hi10 : BatchHeader16.values16 V ⟨5, rfl⟩ = PoisonOr.value (inputs 10))
    (hi11 : BatchHeader16.values16 V ⟨4, rfl⟩ = PoisonOr.value (inputs 11))
    (hi12 : BatchHeader16.values16 V ⟨3, rfl⟩ = PoisonOr.value (inputs 12))
    (hi13 : BatchHeader16.values16 V ⟨2, rfl⟩ = PoisonOr.value (inputs 13))
    (hi14 : BatchHeader16.values16 V ⟨1, rfl⟩ = PoisonOr.value (inputs 14))
    (hi15 : BatchHeader16.values16 V ⟨0, rfl⟩ = PoisonOr.value (inputs 15))
    (hp0 : A ⟨34, rfl⟩ = PoisonOr.value (out.withOffset 0))
    (hp1 : A ⟨17, rfl⟩ = PoisonOr.value (out.withOffset 64))
    (hp2 : A ⟨16, rfl⟩ = PoisonOr.value (out.withOffset 128))
    (hp3 : A ⟨15, rfl⟩ = PoisonOr.value (out.withOffset 192))
    (hp4 : A ⟨14, rfl⟩ = PoisonOr.value (out.withOffset 256))
    (hp5 : A ⟨13, rfl⟩ = PoisonOr.value (out.withOffset 320))
    (hp6 : A ⟨12, rfl⟩ = PoisonOr.value (out.withOffset 384))
    (hp7 : A ⟨11, rfl⟩ = PoisonOr.value (out.withOffset 448))
    (hp8 : A ⟨10, rfl⟩ = PoisonOr.value (out.withOffset 512))
    (hp9 : A ⟨9, rfl⟩ = PoisonOr.value (out.withOffset 576))
    (hp10 : A ⟨8, rfl⟩ = PoisonOr.value (out.withOffset 640))
    (hp11 : A ⟨7, rfl⟩ = PoisonOr.value (out.withOffset 704))
    (hp12 : A ⟨6, rfl⟩ = PoisonOr.value (out.withOffset 768))
    (hp13 : A ⟨5, rfl⟩ = PoisonOr.value (out.withOffset 832))
    (hp14 : A ⟨4, rfl⟩ = PoisonOr.value (out.withOffset 896))
    (hp15 : A ⟨3, rfl⟩ = PoisonOr.value (out.withOffset 960))
    (ha : bitcast (.vector 16 (.bitvec (.concrete 1))) (.bitvec (.concrete 16))
      (vtrunc 1 (BatchHeader16.values16 V ⟨33, rfl⟩)) = PoisonOr.value mask)
    (hz : A ⟨85, rfl⟩ = PoisonOr.value 0#16) :
    BatchTranspose16.Env16 (transposeInput A V) out inputs mask := by
  constructor
  · change BatchHeader16.values16 V ⟨15, rfl⟩ = _
    exact hi0
  · change BatchHeader16.values16 V ⟨14, rfl⟩ = _
    exact hi1
  · change BatchHeader16.values16 V ⟨13, rfl⟩ = _
    exact hi2
  · change BatchHeader16.values16 V ⟨12, rfl⟩ = _
    exact hi3
  · change BatchHeader16.values16 V ⟨11, rfl⟩ = _
    exact hi4
  · change BatchHeader16.values16 V ⟨10, rfl⟩ = _
    exact hi5
  · change BatchHeader16.values16 V ⟨9, rfl⟩ = _
    exact hi6
  · change BatchHeader16.values16 V ⟨8, rfl⟩ = _
    exact hi7
  · change BatchHeader16.values16 V ⟨7, rfl⟩ = _
    exact hi8
  · change BatchHeader16.values16 V ⟨6, rfl⟩ = _
    exact hi9
  · change BatchHeader16.values16 V ⟨5, rfl⟩ = _
    exact hi10
  · change BatchHeader16.values16 V ⟨4, rfl⟩ = _
    exact hi11
  · change BatchHeader16.values16 V ⟨3, rfl⟩ = _
    exact hi12
  · change BatchHeader16.values16 V ⟨2, rfl⟩ = _
    exact hi13
  · change BatchHeader16.values16 V ⟨1, rfl⟩ = _
    exact hi14
  · change BatchHeader16.values16 V ⟨0, rfl⟩ = _
    exact hi15
  · change A ⟨34, rfl⟩ = _
    exact hp0
  · change A ⟨17, rfl⟩ = _
    exact hp1
  · change A ⟨16, rfl⟩ = _
    exact hp2
  · change A ⟨15, rfl⟩ = _
    exact hp3
  · change A ⟨14, rfl⟩ = _
    exact hp4
  · change A ⟨13, rfl⟩ = _
    exact hp5
  · change A ⟨12, rfl⟩ = _
    exact hp6
  · change A ⟨11, rfl⟩ = _
    exact hp7
  · change A ⟨10, rfl⟩ = _
    exact hp8
  · change A ⟨9, rfl⟩ = _
    exact hp9
  · change A ⟨8, rfl⟩ = _
    exact hp10
  · change A ⟨7, rfl⟩ = _
    exact hp11
  · change A ⟨6, rfl⟩ = _
    exact hp12
  · change A ⟨5, rfl⟩ = _
    exact hp13
  · change A ⟨4, rfl⟩ = _
    exact hp14
  · change A ⟨3, rfl⟩ = _
    exact hp15
  · change bitcast (.vector 16 (.bitvec (.concrete 1))) (.bitvec (.concrete 16))
      (vtrunc 1 (BatchHeader16.values16 V ⟨33, rfl⟩)) = _
    exact ha
  · change A ⟨85, rfl⟩ = _
    exact hz


attribute [local semireducible] BatchHeader16.values16

private theorem word_shift (j : Nat) (hj : j ≤ 15) :
    LLVM.lshr (.value (BitVec.ofNat 64 (64*j))) (.value 2#64) =
      .value (BitVec.ofNat 64 (16*j)) := by
  interval_cases j <;> rfl

private theorem source_gep (src : Pointer) (base j : Nat) (hj : j ≤ 15) :
    gep (.value (src.withOffset (BitVec.ofNat 64 base))) 4 0
      (LLVM.lshr (.value (BitVec.ofNat 64 (64*j))) (.value 2#64)) =
    PoisonOr.value (src.withOffset (BitVec.ofNat 64 (base+64*j))) := by
  rw [word_shift j hj]
  simp [gep, ptradd, Pointer.withOffset, LLVM.add, LLVM.mul, LLVM.const?,
    LLVM.add?, LLVM.mul?, BitVec.add_assoc, ← BitVec.ofNat_mul, ← BitVec.ofNat_add,
    Nat.mul_comm, Nat.mul_left_comm]

def sourcePtr16 (src : Pointer) (ms : Fin 16 → AgaveConcrete.Message)
    (iteration : Nat) (lane : Fin 16) : Pointer :=
  src.withOffset (BitVec.ofNat 64 (1024*lane.val + batchOffset (ms lane).length iteration))

def activeMask16 (ms : Fin 16 → AgaveConcrete.Message) (iteration : Nat) : BitVec 16 :=
  packBits ((activeBytes16 ms iteration).map (·.truncate 1))

set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
/-- The transpose contract follows from the scalar-state header and ambient
allocation addresses; it assumes no load or branch outcome. -/
theorem header_transpose_env (s : GlobalState) (src len out sched panic : Pointer)
    (ms : Fin 16 → AgaveConcrete.Message) (iteration : Nat)
    (hms : ∀ lane, (ms lane).length ≤ 1024) :
    BatchTranspose16.Env16
      (transposeInput (BatchEntry16.entryVal16 s src len out sched panic
        (Vector.ofFn fun i : Fin 8 => BitVec.ofNat 64 (ms ⟨i.val, by omega⟩).length)
        (Vector.ofFn fun i : Fin 8 => BitVec.ofNat 64 (ms ⟨i.val+8, by omega⟩).length))
        (headerAt16Val (BatchEntry16.entryVal16 s src len out sched panic
          (Vector.ofFn fun i : Fin 8 => BitVec.ofNat 64 (ms ⟨i.val, by omega⟩).length)
          (Vector.ofFn fun i : Fin 8 => BitVec.ofNat 64 (ms ⟨i.val+8, by omega⟩).length)) ms iteration))
      (BatchEntry16.scratch s 0) (sourcePtr16 src ms iteration) (activeMask16 ms iteration) := by
  apply transpose_env
  · change gep (.value src) 4 0
      (LLVM.lshr (.value ((Vector.ofFn fun lane : Fin 16 =>
        BitVec.ofNat 64 (batchOffset (ms lane).length iteration))[0])) (.value 2#64)) = _
    simp only [Vector.getElem_ofFn]
    have hj : min iteration (AgaveBatchControl.rootIndex (ms 0).length) ≤ 15 := by
      have h := batchOffset_le_960 (ms 0).length iteration (hms 0)
      unfold batchOffset at h
      omega
    simpa [sourcePtr16, batchOffset, Pointer.withOffset] using
      source_gep src 0 (min iteration (AgaveBatchControl.rootIndex (ms 0).length)) hj
  · change gep (.value (src.withOffset 1024)) 4 0
      (LLVM.lshr (.value ((Vector.ofFn fun lane : Fin 16 =>
        BitVec.ofNat 64 (batchOffset (ms lane).length iteration))[1])) (.value 2#64)) = _
    simp only [Vector.getElem_ofFn]
    have hj : min iteration (AgaveBatchControl.rootIndex (ms 1).length) ≤ 15 := by
      have h := batchOffset_le_960 (ms 1).length iteration (hms 1)
      unfold batchOffset at h
      omega
    simpa [sourcePtr16, batchOffset, Pointer.withOffset] using
      source_gep src 1024 (min iteration (AgaveBatchControl.rootIndex (ms 1).length)) hj
  · change gep (.value (src.withOffset 2048)) 4 0
      (LLVM.lshr (.value ((Vector.ofFn fun lane : Fin 16 =>
        BitVec.ofNat 64 (batchOffset (ms lane).length iteration))[2])) (.value 2#64)) = _
    simp only [Vector.getElem_ofFn]
    have hj : min iteration (AgaveBatchControl.rootIndex (ms 2).length) ≤ 15 := by
      have h := batchOffset_le_960 (ms 2).length iteration (hms 2)
      unfold batchOffset at h
      omega
    simpa [sourcePtr16, batchOffset, Pointer.withOffset] using
      source_gep src 2048 (min iteration (AgaveBatchControl.rootIndex (ms 2).length)) hj
  · change gep (.value (src.withOffset 3072)) 4 0
      (LLVM.lshr (.value ((Vector.ofFn fun lane : Fin 16 =>
        BitVec.ofNat 64 (batchOffset (ms lane).length iteration))[3])) (.value 2#64)) = _
    simp only [Vector.getElem_ofFn]
    have hj : min iteration (AgaveBatchControl.rootIndex (ms 3).length) ≤ 15 := by
      have h := batchOffset_le_960 (ms 3).length iteration (hms 3)
      unfold batchOffset at h
      omega
    simpa [sourcePtr16, batchOffset, Pointer.withOffset] using
      source_gep src 3072 (min iteration (AgaveBatchControl.rootIndex (ms 3).length)) hj
  · change gep (.value (src.withOffset 4096)) 4 0
      (LLVM.lshr (.value ((Vector.ofFn fun lane : Fin 16 =>
        BitVec.ofNat 64 (batchOffset (ms lane).length iteration))[4])) (.value 2#64)) = _
    simp only [Vector.getElem_ofFn]
    have hj : min iteration (AgaveBatchControl.rootIndex (ms 4).length) ≤ 15 := by
      have h := batchOffset_le_960 (ms 4).length iteration (hms 4)
      unfold batchOffset at h
      omega
    simpa [sourcePtr16, batchOffset, Pointer.withOffset] using
      source_gep src 4096 (min iteration (AgaveBatchControl.rootIndex (ms 4).length)) hj
  · change gep (.value (src.withOffset 5120)) 4 0
      (LLVM.lshr (.value ((Vector.ofFn fun lane : Fin 16 =>
        BitVec.ofNat 64 (batchOffset (ms lane).length iteration))[5])) (.value 2#64)) = _
    simp only [Vector.getElem_ofFn]
    have hj : min iteration (AgaveBatchControl.rootIndex (ms 5).length) ≤ 15 := by
      have h := batchOffset_le_960 (ms 5).length iteration (hms 5)
      unfold batchOffset at h
      omega
    simpa [sourcePtr16, batchOffset, Pointer.withOffset] using
      source_gep src 5120 (min iteration (AgaveBatchControl.rootIndex (ms 5).length)) hj
  · change gep (.value (src.withOffset 6144)) 4 0
      (LLVM.lshr (.value ((Vector.ofFn fun lane : Fin 16 =>
        BitVec.ofNat 64 (batchOffset (ms lane).length iteration))[6])) (.value 2#64)) = _
    simp only [Vector.getElem_ofFn]
    have hj : min iteration (AgaveBatchControl.rootIndex (ms 6).length) ≤ 15 := by
      have h := batchOffset_le_960 (ms 6).length iteration (hms 6)
      unfold batchOffset at h
      omega
    simpa [sourcePtr16, batchOffset, Pointer.withOffset] using
      source_gep src 6144 (min iteration (AgaveBatchControl.rootIndex (ms 6).length)) hj
  · change gep (.value (src.withOffset 7168)) 4 0
      (LLVM.lshr (.value ((Vector.ofFn fun lane : Fin 16 =>
        BitVec.ofNat 64 (batchOffset (ms lane).length iteration))[7])) (.value 2#64)) = _
    simp only [Vector.getElem_ofFn]
    have hj : min iteration (AgaveBatchControl.rootIndex (ms 7).length) ≤ 15 := by
      have h := batchOffset_le_960 (ms 7).length iteration (hms 7)
      unfold batchOffset at h
      omega
    simpa [sourcePtr16, batchOffset, Pointer.withOffset] using
      source_gep src 7168 (min iteration (AgaveBatchControl.rootIndex (ms 7).length)) hj
  · change gep (.value (src.withOffset 8192)) 4 0
      (LLVM.lshr (.value ((Vector.ofFn fun lane : Fin 16 =>
        BitVec.ofNat 64 (batchOffset (ms lane).length iteration))[8])) (.value 2#64)) = _
    simp only [Vector.getElem_ofFn]
    have hj : min iteration (AgaveBatchControl.rootIndex (ms 8).length) ≤ 15 := by
      have h := batchOffset_le_960 (ms 8).length iteration (hms 8)
      unfold batchOffset at h
      omega
    simpa [sourcePtr16, batchOffset, Pointer.withOffset] using
      source_gep src 8192 (min iteration (AgaveBatchControl.rootIndex (ms 8).length)) hj
  · change gep (.value (src.withOffset 9216)) 4 0
      (LLVM.lshr (.value ((Vector.ofFn fun lane : Fin 16 =>
        BitVec.ofNat 64 (batchOffset (ms lane).length iteration))[9])) (.value 2#64)) = _
    simp only [Vector.getElem_ofFn]
    have hj : min iteration (AgaveBatchControl.rootIndex (ms 9).length) ≤ 15 := by
      have h := batchOffset_le_960 (ms 9).length iteration (hms 9)
      unfold batchOffset at h
      omega
    simpa [sourcePtr16, batchOffset, Pointer.withOffset] using
      source_gep src 9216 (min iteration (AgaveBatchControl.rootIndex (ms 9).length)) hj
  · change gep (.value (src.withOffset 10240)) 4 0
      (LLVM.lshr (.value ((Vector.ofFn fun lane : Fin 16 =>
        BitVec.ofNat 64 (batchOffset (ms lane).length iteration))[10])) (.value 2#64)) = _
    simp only [Vector.getElem_ofFn]
    have hj : min iteration (AgaveBatchControl.rootIndex (ms 10).length) ≤ 15 := by
      have h := batchOffset_le_960 (ms 10).length iteration (hms 10)
      unfold batchOffset at h
      omega
    simpa [sourcePtr16, batchOffset, Pointer.withOffset] using
      source_gep src 10240 (min iteration (AgaveBatchControl.rootIndex (ms 10).length)) hj
  · change gep (.value (src.withOffset 11264)) 4 0
      (LLVM.lshr (.value ((Vector.ofFn fun lane : Fin 16 =>
        BitVec.ofNat 64 (batchOffset (ms lane).length iteration))[11])) (.value 2#64)) = _
    simp only [Vector.getElem_ofFn]
    have hj : min iteration (AgaveBatchControl.rootIndex (ms 11).length) ≤ 15 := by
      have h := batchOffset_le_960 (ms 11).length iteration (hms 11)
      unfold batchOffset at h
      omega
    simpa [sourcePtr16, batchOffset, Pointer.withOffset] using
      source_gep src 11264 (min iteration (AgaveBatchControl.rootIndex (ms 11).length)) hj
  · change gep (.value (src.withOffset 12288)) 4 0
      (LLVM.lshr (.value ((Vector.ofFn fun lane : Fin 16 =>
        BitVec.ofNat 64 (batchOffset (ms lane).length iteration))[12])) (.value 2#64)) = _
    simp only [Vector.getElem_ofFn]
    have hj : min iteration (AgaveBatchControl.rootIndex (ms 12).length) ≤ 15 := by
      have h := batchOffset_le_960 (ms 12).length iteration (hms 12)
      unfold batchOffset at h
      omega
    simpa [sourcePtr16, batchOffset, Pointer.withOffset] using
      source_gep src 12288 (min iteration (AgaveBatchControl.rootIndex (ms 12).length)) hj
  · change gep (.value (src.withOffset 13312)) 4 0
      (LLVM.lshr (.value ((Vector.ofFn fun lane : Fin 16 =>
        BitVec.ofNat 64 (batchOffset (ms lane).length iteration))[13])) (.value 2#64)) = _
    simp only [Vector.getElem_ofFn]
    have hj : min iteration (AgaveBatchControl.rootIndex (ms 13).length) ≤ 15 := by
      have h := batchOffset_le_960 (ms 13).length iteration (hms 13)
      unfold batchOffset at h
      omega
    simpa [sourcePtr16, batchOffset, Pointer.withOffset] using
      source_gep src 13312 (min iteration (AgaveBatchControl.rootIndex (ms 13).length)) hj
  · change gep (.value (src.withOffset 14336)) 4 0
      (LLVM.lshr (.value ((Vector.ofFn fun lane : Fin 16 =>
        BitVec.ofNat 64 (batchOffset (ms lane).length iteration))[14])) (.value 2#64)) = _
    simp only [Vector.getElem_ofFn]
    have hj : min iteration (AgaveBatchControl.rootIndex (ms 14).length) ≤ 15 := by
      have h := batchOffset_le_960 (ms 14).length iteration (hms 14)
      unfold batchOffset at h
      omega
    simpa [sourcePtr16, batchOffset, Pointer.withOffset] using
      source_gep src 14336 (min iteration (AgaveBatchControl.rootIndex (ms 14).length)) hj
  · change gep (.value (src.withOffset 15360)) 4 0
      (LLVM.lshr (.value ((Vector.ofFn fun lane : Fin 16 =>
        BitVec.ofNat 64 (batchOffset (ms lane).length iteration))[15])) (.value 2#64)) = _
    simp only [Vector.getElem_ofFn]
    have hj : min iteration (AgaveBatchControl.rootIndex (ms 15).length) ≤ 15 := by
      have h := batchOffset_le_960 (ms 15).length iteration (hms 15)
      unfold batchOffset at h
      omega
    simpa [sourcePtr16, batchOffset, Pointer.withOffset] using
      source_gep src 15360 (min iteration (AgaveBatchControl.rootIndex (ms 15).length)) hj
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact (congrArg (fun v : Vector (LLVM.IntW 8) 16 =>
      bitcast (.vector 16 (.bitvec (.concrete 1))) (.bitvec (.concrete 16)) (vtrunc 1 v))
      (header_active_bytes16 s src len out sched panic ms iteration hms)).trans
        (BatchTranspose16.bitcast_active16_bytes _)
  · rfl


/-- Ambient entry values with the sixteen logical message lengths. -/
noncomputable def ambient16 (s : GlobalState) (src len out sched panic : Pointer)
    (ms : Fin 16 → AgaveConcrete.Message) : agave_batch_16.cfgCtx.Valuation :=
  BatchEntry16.entryVal16 s src len out sched panic
    (Vector.ofFn fun i : Fin 8 => BitVec.ofNat 64 (ms ⟨i.val, by omega⟩).length)
    (Vector.ofFn fun i : Fin 8 => BitVec.ofNat 64 (ms ⟨i.val+8, by omega⟩).length)

noncomputable def transposeAt16 (A : agave_batch_16.cfgCtx.Valuation)
    (ms : Fin 16 → AgaveConcrete.Message) (iteration : Nat) :=
  transposeInput A (headerAt16Val A ms iteration)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
/-- The actual header, fifteen-lane guard, sixteen loads, shuffle network and
sixteen stores execute to precisely the mask-selected successor. -/
theorem header_to_transpose (s u : GlobalState) (src len out sched panic : Pointer)
    (ms : Fin 16 → AgaveConcrete.Message) (iteration : Nat)
    (hms : ∀ lane, (ms lane).length ≤ 1024) (rows : Vector (Vector Word 16) 16)
    (hf : ∀ i, Fits u.mem (sourcePtr16 src ms iteration i) 512)
    (hr : ∀ i, readWord? (sourcePtr16 src ms iteration i) 512 u.mem = some (packBits rows[i]))
    (hfit : ∀ k < 16, Fits u.mem ((BatchEntry16.scratch s 0).withOffset (BitVec.ofNat 64 (64*k))) 512) :
    StateT.run (agave_batch_16.blocks.run (ambient16 s src len out sched panic ms) (headerAt16 ms iteration)) u =
      StateT.run (agave_batch_16.blocks.run (ambient16 s src len out sched panic ms)
        (if activeMask16 ms iteration = 0 then
          BatchTranspose16.rootTarget16 (transposeAt16 (ambient16 s src len out sched panic ms) ms iteration)
        else BatchTranspose16.nonrootTarget16 (transposeAt16 (ambient16 s src len out sched panic ms) ms iteration)))
        {u with mem := outputMem (BatchEntry16.scratch s 0) (BatchTranspose16.columns16 rows) 16 u.mem} := by
  let A := ambient16 s src len out sched panic ms
  let V := headerAt16Val A ms iteration
  have henv := header_transpose_env s src len out sched panic ms iteration hms
  have h := BatchTransposeRun16.run2 A
    (BatchGuards16.next1 (input1 A (BatchHeader16.next16 V).args)).args
    (BatchEntry16.scratch s 0) (sourcePtr16 src ms iteration) rows (activeMask16 ms iteration) u
    henv hf hr hfit
  have heta (W : BatchGuards16.Input1.Valuation) :
      (⟨2, rfl, (BatchGuards16.next1 W).args⟩ : SuccArgs agave_batch_16.cfgSigs) =
        BatchGuards16.next1 W := rfl
  rw [heta] at h
  exact (header_to_loads s u src len out sched panic
    (Vector.ofFn fun i : Fin 8 => BitVec.ofNat 64 (ms ⟨i.val, by omega⟩).length)
    (Vector.ofFn fun i : Fin 8 => BitVec.ofNat 64 (ms ⟨i.val+8, by omega⟩).length)
    ms iteration hms).trans h

/-- Complete physical 64-byte rows at the represented source offsets. -/
def sourceRows16 (p : AgavePhysicalStaging.Store)
    (ms : Fin 16 → AgaveConcrete.Message) (iteration : Nat) : Vector (Vector Word 16) 16 :=
  Vector.ofFn fun lane => CallerMemory.wordsLE 16 (fun i =>
    AgavePhysicalStaging.memoryAt p lane.val (batchOffset (ms lane).length iteration+i))

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
/-- The path's load and store premises follow from the physical caller image
and the loop memory frame, including retained suffix bytes in every row. -/
theorem header_to_transpose_physical (s u : GlobalState) (src len out sched panic : Pointer)
    (p : AgavePhysicalStaging.Store) (a : AgaveStaging.Value)
    (hc : CallerMemory.Represents s 16 src len out sched panic p a)
    (hm : BatchMemory16 s u)
    (ms : Fin 16 → AgaveConcrete.Message) (iteration : Nat)
    (hms : ∀ lane, (ms lane).length ≤ 1024) :
    StateT.run (agave_batch_16.blocks.run (ambient16 s src len out sched panic ms) (headerAt16 ms iteration)) u =
      StateT.run (agave_batch_16.blocks.run (ambient16 s src len out sched panic ms)
        (if activeMask16 ms iteration = 0 then
          BatchTranspose16.rootTarget16 (transposeAt16 (ambient16 s src len out sched panic ms) ms iteration)
        else BatchTranspose16.nonrootTarget16 (transposeAt16 (ambient16 s src len out sched panic ms) ms iteration)))
        {u with mem := outputMem (BatchEntry16.scratch s 0) (BatchTranspose16.columns16 (sourceRows16 p ms iteration)) 16 u.mem} := by
  apply header_to_transpose s u src len out sched panic ms iteration hms
  · intro lane
    exact (hm.source_row hc lane (ms lane).length iteration (hms lane)).1
  · intro lane
    simpa only [sourcePtr16, sourceRows16, Fin.getElem_fin, Vector.getElem_ofFn] using
      (hm.source_row hc lane (ms lane).length iteration (hms lane)).2
  · intro k hk
    have ho : (BitVec.ofNat 64 (64*k)).toNat = 64*k := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]; omega
    apply Fits.mono (remainingFits u.mem (BatchEntry16.scratch s 0) (hm.scratch 0)
      (BitVec.ofNat 64 (64*k)) ?_)
    · rw [ho]; omega
    · rw [ho]; omega

end AgaveLatticeHash.MLIR.BatchRefinement16
