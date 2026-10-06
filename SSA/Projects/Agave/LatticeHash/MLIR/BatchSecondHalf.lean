/- Released under Apache 2.0 license as described in the file LICENSE. -/
import SSA.Projects.Agave.LatticeHash.MLIR.BatchFirstHalf
import SSA.Projects.Agave.LatticeHash.MLIR.BatchSecondLoadPath

namespace AgaveLatticeHash.MLIR.BatchSecondHalf
open LeanMLIR SLLVM Firedancer
open InstCombine (LLVM)
open BatchLoads BatchSecondLoadPath
open BatchFirstHalf (wordAt firstRows sourceAt transposeInput)

noncomputable def startTarget (A : agave_batch_8.cfgCtx.Valuation)
    (ms : Fin 8 → AgaveConcrete.Message) (iteration : Nat)
    (lo : Vector (Vector (BitVec 32) 8) 8) : SuccArgs agave_batch_8.cfgSigs :=
  BatchFirstTranspose.next8 (transposeInput A ms iteration lo)
    (BatchFirstTranspose.transposeRows8 (lo.map (·.map PoisonOr.value)))
    (BatchFirstTranspose.nextOffset8 (transposeInput A ms iteration lo))

theorem wordAt_bound (ms : Fin 8 → AgaveConcrete.Message) (iteration : Nat)
    (lane : Fin 8) (hms : (ms lane).length ≤ 1024) :
    (wordAt ms iteration lane).toNat ≤ 240 := by
  have h := batchOffset_le_960 (ms lane).length iteration hms
  unfold batchOffset at h
  have hj : min iteration (AgaveBatchControl.rootIndex (ms lane).length) ≤ 15 := by omega
  simp only [wordAt, BitVec.toNat_ofNat]
  exact Nat.le_trans (Nat.mod_le ..) (by omega)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
/-- Concrete second-half load facts, including both emitted no-wrap flags. -/
noncomputable def ready2 (s u : GlobalState) (src len out sched panic : Pointer)
    (lengths : Vector (BitVec 64) 8) (ms : Fin 8 → AgaveConcrete.Message)
    (iteration : Nat) (hms : ∀ lane, (ms lane).length ≤ 1024)
    (lo hi : Vector (Vector (BitVec 32) 8) 8)
    (hf : Fits u.mem (rowPtr src (wordAt ms iteration 0 + 8)) 256)
    (hr : readWord? (rowPtr src (wordAt ms iteration 0 + 8)) 256 u.mem = some (packBits hi[0])) :
    Ready2 (input2 (BatchEntry.entryVal8 s src len out sched panic lengths) (startTarget (BatchEntry.entryVal8 s src len out sched panic lengths) ms iteration lo).args) u hi[0] := by
  refine ⟨src, wordAt ms iteration 0 + 8,
    BitVec.ofNat 64 (batchOffset (ms 1).length iteration), ?_, ?_, ?_, ?_, ?_, hf, hr⟩
  · rfl
  · change LLVM.add
      (LLVM.lshr (((Vector.ofFn fun lane : Fin 8 =>
        BitVec.ofNat 64 (batchOffset (ms lane).length iteration)).map PoisonOr.value)[0])
        (.value 2#64)) (.value 8#64) {nsw := true, nuw := true} = _
    simp only [Vector.getElem_map, Vector.getElem_ofFn]
    have hj : min iteration (AgaveBatchControl.rootIndex (ms 0).length) ≤ 15 := by
      have h := batchOffset_le_960 (ms 0).length iteration (hms 0)
      unfold batchOffset at h
      omega
    have hs : LLVM.lshr (.value (BitVec.ofNat 64 (batchOffset (ms 0).length iteration)))
        (.value 2#64) = .value (wordAt ms iteration 0) := BatchLoadPath.word_shift _ hj
    change LLVM.add
      (LLVM.lshr (.value (BitVec.ofNat 64 (batchOffset (ms 0).length iteration))) (.value 2#64))
      (.value 8#64) {nsw := true, nuw := true} = _
    rw [hs]
    exact addEight_safe _ (wordAt_bound ms iteration 0 (hms 0))
  · change (((Vector.ofFn fun lane : Fin 8 =>
      BitVec.ofNat 64 (batchOffset (ms lane).length iteration)).map PoisonOr.value)[1]) = _
    simp
  · rfl
  · simp only [BitVec.toNat_ofNat]
    exact Nat.le_trans (Nat.mod_le ..) (batchOffset_le_960 _ _ (hms 1))

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
/-- Concrete second-half load facts, including both emitted no-wrap flags. -/
noncomputable def ready3 (s u : GlobalState) (src len out sched panic : Pointer)
    (lengths : Vector (BitVec 64) 8) (ms : Fin 8 → AgaveConcrete.Message)
    (iteration : Nat) (hms : ∀ lane, (ms lane).length ≤ 1024)
    (lo hi : Vector (Vector (BitVec 32) 8) 8)
    (hf : Fits u.mem (rowPtr (src.withOffset 1024) (wordAt ms iteration 1 + 8)) 256)
    (hr : readWord? (rowPtr (src.withOffset 1024) (wordAt ms iteration 1 + 8)) 256 u.mem = some (packBits hi[1])) :
    Ready3 (input3 (BatchEntry.entryVal8 s src len out sched panic lengths) (args3 (BatchEntry.entryVal8 s src len out sched panic lengths) (startTarget (BatchEntry.entryVal8 s src len out sched panic lengths) ms iteration lo).args (firstRows hi))) u hi[1] := by
  refine ⟨(src.withOffset 1024), wordAt ms iteration 1 + 8,
    BitVec.ofNat 64 (batchOffset (ms 2).length iteration), ?_, ?_, ?_, ?_, ?_, hf, hr⟩
  · rfl
  · change LLVM.add
      (LLVM.lshr (((Vector.ofFn fun lane : Fin 8 =>
        BitVec.ofNat 64 (batchOffset (ms lane).length iteration)).map PoisonOr.value)[1])
        (.value 2#64)) (.value 8#64) {nsw := true, nuw := true} = _
    simp only [Vector.getElem_map, Vector.getElem_ofFn]
    have hj : min iteration (AgaveBatchControl.rootIndex (ms 1).length) ≤ 15 := by
      have h := batchOffset_le_960 (ms 1).length iteration (hms 1)
      unfold batchOffset at h
      omega
    have hs : LLVM.lshr (.value (BitVec.ofNat 64 (batchOffset (ms 1).length iteration)))
        (.value 2#64) = .value (wordAt ms iteration 1) := BatchLoadPath.word_shift _ hj
    change LLVM.add
      (LLVM.lshr (.value (BitVec.ofNat 64 (batchOffset (ms 1).length iteration))) (.value 2#64))
      (.value 8#64) {nsw := true, nuw := true} = _
    rw [hs]
    exact addEight_safe _ (wordAt_bound ms iteration 1 (hms 1))
  · change (((Vector.ofFn fun lane : Fin 8 =>
      BitVec.ofNat 64 (batchOffset (ms lane).length iteration)).map PoisonOr.value)[2]) = _
    simp
  · rfl
  · simp only [BitVec.toNat_ofNat]
    exact Nat.le_trans (Nat.mod_le ..) (batchOffset_le_960 _ _ (hms 2))

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
/-- Concrete second-half load facts, including both emitted no-wrap flags. -/
noncomputable def ready4 (s u : GlobalState) (src len out sched panic : Pointer)
    (lengths : Vector (BitVec 64) 8) (ms : Fin 8 → AgaveConcrete.Message)
    (iteration : Nat) (hms : ∀ lane, (ms lane).length ≤ 1024)
    (lo hi : Vector (Vector (BitVec 32) 8) 8)
    (hf : Fits u.mem (rowPtr (src.withOffset 2048) (wordAt ms iteration 2 + 8)) 256)
    (hr : readWord? (rowPtr (src.withOffset 2048) (wordAt ms iteration 2 + 8)) 256 u.mem = some (packBits hi[2])) :
    Ready4 (input4 (BatchEntry.entryVal8 s src len out sched panic lengths) (args4 (BatchEntry.entryVal8 s src len out sched panic lengths) (startTarget (BatchEntry.entryVal8 s src len out sched panic lengths) ms iteration lo).args (firstRows hi))) u hi[2] := by
  refine ⟨(src.withOffset 2048), wordAt ms iteration 2 + 8,
    BitVec.ofNat 64 (batchOffset (ms 3).length iteration), ?_, ?_, ?_, ?_, ?_, hf, hr⟩
  · rfl
  · change LLVM.add
      (LLVM.lshr (((Vector.ofFn fun lane : Fin 8 =>
        BitVec.ofNat 64 (batchOffset (ms lane).length iteration)).map PoisonOr.value)[2])
        (.value 2#64)) (.value 8#64) {nsw := true, nuw := true} = _
    simp only [Vector.getElem_map, Vector.getElem_ofFn]
    have hj : min iteration (AgaveBatchControl.rootIndex (ms 2).length) ≤ 15 := by
      have h := batchOffset_le_960 (ms 2).length iteration (hms 2)
      unfold batchOffset at h
      omega
    have hs : LLVM.lshr (.value (BitVec.ofNat 64 (batchOffset (ms 2).length iteration)))
        (.value 2#64) = .value (wordAt ms iteration 2) := BatchLoadPath.word_shift _ hj
    change LLVM.add
      (LLVM.lshr (.value (BitVec.ofNat 64 (batchOffset (ms 2).length iteration))) (.value 2#64))
      (.value 8#64) {nsw := true, nuw := true} = _
    rw [hs]
    exact addEight_safe _ (wordAt_bound ms iteration 2 (hms 2))
  · change (((Vector.ofFn fun lane : Fin 8 =>
      BitVec.ofNat 64 (batchOffset (ms lane).length iteration)).map PoisonOr.value)[3]) = _
    simp
  · rfl
  · simp only [BitVec.toNat_ofNat]
    exact Nat.le_trans (Nat.mod_le ..) (batchOffset_le_960 _ _ (hms 3))

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
/-- Concrete second-half load facts, including both emitted no-wrap flags. -/
noncomputable def ready5 (s u : GlobalState) (src len out sched panic : Pointer)
    (lengths : Vector (BitVec 64) 8) (ms : Fin 8 → AgaveConcrete.Message)
    (iteration : Nat) (hms : ∀ lane, (ms lane).length ≤ 1024)
    (lo hi : Vector (Vector (BitVec 32) 8) 8)
    (hf : Fits u.mem (rowPtr (src.withOffset 3072) (wordAt ms iteration 3 + 8)) 256)
    (hr : readWord? (rowPtr (src.withOffset 3072) (wordAt ms iteration 3 + 8)) 256 u.mem = some (packBits hi[3])) :
    Ready5 (input5 (BatchEntry.entryVal8 s src len out sched panic lengths) (args5 (BatchEntry.entryVal8 s src len out sched panic lengths) (startTarget (BatchEntry.entryVal8 s src len out sched panic lengths) ms iteration lo).args (firstRows hi))) u hi[3] := by
  refine ⟨(src.withOffset 3072), wordAt ms iteration 3 + 8,
    BitVec.ofNat 64 (batchOffset (ms 4).length iteration), ?_, ?_, ?_, ?_, ?_, hf, hr⟩
  · rfl
  · change LLVM.add
      (LLVM.lshr (((Vector.ofFn fun lane : Fin 8 =>
        BitVec.ofNat 64 (batchOffset (ms lane).length iteration)).map PoisonOr.value)[3])
        (.value 2#64)) (.value 8#64) {nsw := true, nuw := true} = _
    simp only [Vector.getElem_map, Vector.getElem_ofFn]
    have hj : min iteration (AgaveBatchControl.rootIndex (ms 3).length) ≤ 15 := by
      have h := batchOffset_le_960 (ms 3).length iteration (hms 3)
      unfold batchOffset at h
      omega
    have hs : LLVM.lshr (.value (BitVec.ofNat 64 (batchOffset (ms 3).length iteration)))
        (.value 2#64) = .value (wordAt ms iteration 3) := BatchLoadPath.word_shift _ hj
    change LLVM.add
      (LLVM.lshr (.value (BitVec.ofNat 64 (batchOffset (ms 3).length iteration))) (.value 2#64))
      (.value 8#64) {nsw := true, nuw := true} = _
    rw [hs]
    exact addEight_safe _ (wordAt_bound ms iteration 3 (hms 3))
  · change (((Vector.ofFn fun lane : Fin 8 =>
      BitVec.ofNat 64 (batchOffset (ms lane).length iteration)).map PoisonOr.value)[4]) = _
    simp
  · rfl
  · simp only [BitVec.toNat_ofNat]
    exact Nat.le_trans (Nat.mod_le ..) (batchOffset_le_960 _ _ (hms 4))

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
/-- Concrete second-half load facts, including both emitted no-wrap flags. -/
noncomputable def ready6 (s u : GlobalState) (src len out sched panic : Pointer)
    (lengths : Vector (BitVec 64) 8) (ms : Fin 8 → AgaveConcrete.Message)
    (iteration : Nat) (hms : ∀ lane, (ms lane).length ≤ 1024)
    (lo hi : Vector (Vector (BitVec 32) 8) 8)
    (hf : Fits u.mem (rowPtr (src.withOffset 4096) (wordAt ms iteration 4 + 8)) 256)
    (hr : readWord? (rowPtr (src.withOffset 4096) (wordAt ms iteration 4 + 8)) 256 u.mem = some (packBits hi[4])) :
    Ready6 (input6 (BatchEntry.entryVal8 s src len out sched panic lengths) (args6 (BatchEntry.entryVal8 s src len out sched panic lengths) (startTarget (BatchEntry.entryVal8 s src len out sched panic lengths) ms iteration lo).args (firstRows hi))) u hi[4] := by
  refine ⟨(src.withOffset 4096), wordAt ms iteration 4 + 8,
    BitVec.ofNat 64 (batchOffset (ms 5).length iteration), ?_, ?_, ?_, ?_, ?_, hf, hr⟩
  · rfl
  · change LLVM.add
      (LLVM.lshr (((Vector.ofFn fun lane : Fin 8 =>
        BitVec.ofNat 64 (batchOffset (ms lane).length iteration)).map PoisonOr.value)[4])
        (.value 2#64)) (.value 8#64) {nsw := true, nuw := true} = _
    simp only [Vector.getElem_map, Vector.getElem_ofFn]
    have hj : min iteration (AgaveBatchControl.rootIndex (ms 4).length) ≤ 15 := by
      have h := batchOffset_le_960 (ms 4).length iteration (hms 4)
      unfold batchOffset at h
      omega
    have hs : LLVM.lshr (.value (BitVec.ofNat 64 (batchOffset (ms 4).length iteration)))
        (.value 2#64) = .value (wordAt ms iteration 4) := BatchLoadPath.word_shift _ hj
    change LLVM.add
      (LLVM.lshr (.value (BitVec.ofNat 64 (batchOffset (ms 4).length iteration))) (.value 2#64))
      (.value 8#64) {nsw := true, nuw := true} = _
    rw [hs]
    exact addEight_safe _ (wordAt_bound ms iteration 4 (hms 4))
  · change (((Vector.ofFn fun lane : Fin 8 =>
      BitVec.ofNat 64 (batchOffset (ms lane).length iteration)).map PoisonOr.value)[5]) = _
    simp
  · rfl
  · simp only [BitVec.toNat_ofNat]
    exact Nat.le_trans (Nat.mod_le ..) (batchOffset_le_960 _ _ (hms 5))

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
/-- Concrete second-half load facts, including both emitted no-wrap flags. -/
noncomputable def ready7 (s u : GlobalState) (src len out sched panic : Pointer)
    (lengths : Vector (BitVec 64) 8) (ms : Fin 8 → AgaveConcrete.Message)
    (iteration : Nat) (hms : ∀ lane, (ms lane).length ≤ 1024)
    (lo hi : Vector (Vector (BitVec 32) 8) 8)
    (hf : Fits u.mem (rowPtr (src.withOffset 5120) (wordAt ms iteration 5 + 8)) 256)
    (hr : readWord? (rowPtr (src.withOffset 5120) (wordAt ms iteration 5 + 8)) 256 u.mem = some (packBits hi[5])) :
    Ready7 (input7 (BatchEntry.entryVal8 s src len out sched panic lengths) (args7 (BatchEntry.entryVal8 s src len out sched panic lengths) (startTarget (BatchEntry.entryVal8 s src len out sched panic lengths) ms iteration lo).args (firstRows hi))) u hi[5] := by
  refine ⟨(src.withOffset 5120), wordAt ms iteration 5 + 8,
    BitVec.ofNat 64 (batchOffset (ms 6).length iteration), ?_, ?_, ?_, ?_, ?_, hf, hr⟩
  · rfl
  · change LLVM.add
      (LLVM.lshr (((Vector.ofFn fun lane : Fin 8 =>
        BitVec.ofNat 64 (batchOffset (ms lane).length iteration)).map PoisonOr.value)[5])
        (.value 2#64)) (.value 8#64) {nsw := true, nuw := true} = _
    simp only [Vector.getElem_map, Vector.getElem_ofFn]
    have hj : min iteration (AgaveBatchControl.rootIndex (ms 5).length) ≤ 15 := by
      have h := batchOffset_le_960 (ms 5).length iteration (hms 5)
      unfold batchOffset at h
      omega
    have hs : LLVM.lshr (.value (BitVec.ofNat 64 (batchOffset (ms 5).length iteration)))
        (.value 2#64) = .value (wordAt ms iteration 5) := BatchLoadPath.word_shift _ hj
    change LLVM.add
      (LLVM.lshr (.value (BitVec.ofNat 64 (batchOffset (ms 5).length iteration))) (.value 2#64))
      (.value 8#64) {nsw := true, nuw := true} = _
    rw [hs]
    exact addEight_safe _ (wordAt_bound ms iteration 5 (hms 5))
  · change (((Vector.ofFn fun lane : Fin 8 =>
      BitVec.ofNat 64 (batchOffset (ms lane).length iteration)).map PoisonOr.value)[6]) = _
    simp
  · rfl
  · simp only [BitVec.toNat_ofNat]
    exact Nat.le_trans (Nat.mod_le ..) (batchOffset_le_960 _ _ (hms 6))

noncomputable def guardArgs (A : agave_batch_8.cfgCtx.Valuation)
    (ms : Fin 8 → AgaveConcrete.Message) (iteration : Nat)
    (lo hi : Vector (Vector (BitVec 32) 8) 8) :=
  args8 A (startTarget A ms iteration lo).args (firstRows hi)

noncomputable def transposeInput (A : agave_batch_8.cfgCtx.Valuation)
    (ms : Fin 8 → AgaveConcrete.Message) (iteration : Nat)
    (lo hi : Vector (Vector (BitVec 32) 8) 8) : BatchTranspose.InCtx8.Valuation :=
  Ctxt.Valuation.ofHVector (BatchLoads.next8 (input8 A (guardArgs A ms iteration lo hi))).args.reverse ++ A

/-- The six source reads of the second half execute at concrete lane addresses. -/
theorem six_run (s u : GlobalState) (src len out sched panic : Pointer)
    (lengths : Vector (BitVec 64) 8) (ms : Fin 8 → AgaveConcrete.Message)
    (iteration : Nat) (hms : ∀ lane, (ms lane).length ≤ 1024)
    (lo hi : Vector (Vector (BitVec 32) 8) 8)
    (hf : ∀ lane, Fits u.mem (rowPtr (sourceAt src lane) (wordAt ms iteration lane + 8)) 256)
    (hr : ∀ lane, readWord? (rowPtr (sourceAt src lane) (wordAt ms iteration lane + 8)) 256 u.mem =
      some (packBits hi[lane.val])) :
    StateT.run (agave_batch_8.blocks.run (BatchEntry.entryVal8 s src len out sched panic lengths)
      (startTarget (BatchEntry.entryVal8 s src len out sched panic lengths) ms iteration lo)) u =
    StateT.run (agave_batch_8.blocks.run (BatchEntry.entryVal8 s src len out sched panic lengths)
      ⟨8, rfl, guardArgs (BatchEntry.entryVal8 s src len out sched panic lengths) ms iteration lo hi⟩) u := by
  apply BatchSecondLoadPath.six_run
  · exact ready2 s u src len out sched panic lengths ms iteration hms lo hi (hf 0) (hr 0)
  · exact ready3 s u src len out sched panic lengths ms iteration hms lo hi (hf 1) (hr 1)
  · exact ready4 s u src len out sched panic lengths ms iteration hms lo hi (hf 2) (hr 2)
  · exact ready5 s u src len out sched panic lengths ms iteration hms lo hi (hf 3) (hr 3)
  · exact ready6 s u src len out sched panic lengths ms iteration hms lo hi (hf 4) (hr 4)
  · exact ready7 s u src len out sched panic lengths ms iteration hms lo hi (hf 5) (hr 5)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
/-- The last second-half guard is false for every legal lane-seven offset. -/
theorem guard_run (s u : GlobalState) (src len out sched panic : Pointer)
    (lengths : Vector (BitVec 64) 8) (ms : Fin 8 → AgaveConcrete.Message)
    (iteration : Nat) (hms : ∀ lane, (ms lane).length ≤ 1024)
    (lo hi : Vector (Vector (BitVec 32) 8) 8) :
    StateT.run (agave_batch_8.blocks.run (BatchEntry.entryVal8 s src len out sched panic lengths)
      ⟨8, rfl, guardArgs (BatchEntry.entryVal8 s src len out sched panic lengths) ms iteration lo hi⟩) u =
    StateT.run (agave_batch_8.blocks.run (BatchEntry.entryVal8 s src len out sched panic lengths)
      (BatchLoads.next8 (input8 (BatchEntry.entryVal8 s src len out sched panic lengths)
        (guardArgs (BatchEntry.entryVal8 s src len out sched panic lengths) ms iteration lo hi)))) u := by
  apply run8 _ _ u (BitVec.ofNat 64 (batchOffset (ms 7).length iteration))
  · change (((Vector.ofFn fun lane : Fin 8 =>
      BitVec.ofNat 64 (batchOffset (ms lane).length iteration)).map PoisonOr.value)[7]) = _
    simp
  · rfl
  · simp only [BitVec.toNat_ofNat]
    exact Nat.le_trans (Nat.mod_le ..) (batchOffset_le_960 _ _ (hms 7))

end AgaveLatticeHash.MLIR.BatchSecondHalf
