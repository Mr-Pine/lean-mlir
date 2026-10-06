/- Released under Apache 2.0 license as described in the file LICENSE. -/
import SSA.Projects.Agave.LatticeHash.MLIR.BatchFieldForward

namespace AgaveLatticeHash.MLIR.BatchTransposePath
open LeanMLIR SLLVM Firedancer
open InstCombine (LLVM)
open BatchLoads CompressionExit
open BatchFirstHalf (wordAt firstRows sourceAt)
open BatchSecondHalf (transposeInput guardArgs)

def lowColumns (lo : Vector (Vector (BitVec 32) 8) 8) : Vector (Vector (BitVec 32) 8) 8 :=
  Vector.ofFn fun col => Vector.ofFn fun lane => lo[lane][col]

theorem lowColumns_defined (lo : Vector (Vector (BitVec 32) 8) 8) :
    BatchFirstTranspose.transposeRows8 (lo.map (·.map PoisonOr.value)) =
      (lowColumns lo).map (·.map PoisonOr.value) := by
  apply Vector.ext
  intro i hi
  apply Vector.ext
  intro j hj
  simp [BatchFirstTranspose.transposeRows8, lowColumns, Fin.getElem_fin]

def activeVector (ms : Fin 8 → AgaveConcrete.Message) (iteration : Nat) : Vector (BitVec 1) 8 :=
  Vector.ofFn fun lane => BitVec.ofBool (decide (iteration < AgaveBatchControl.rootIndex (ms lane).length))

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
theorem active_final (s : GlobalState) (src len out sched panic : Pointer)
    (ms : Fin 8 → AgaveConcrete.Message) (iteration : Nat)
    (hms : ∀ lane, (ms lane).length ≤ 1024)
    (lo hi : Vector (Vector (BitVec 32) 8) 8) :
    SLLVM.bitcast (.vector 8 (.bitvec (.concrete 1))) (.bitvec (.concrete 8))
      (transposeInput (BatchEntry.entryVal8 s src len out sched panic
        (Vector.ofFn fun lane => BitVec.ofNat 64 (ms lane).length)) ms iteration lo hi ⟨18, rfl⟩) =
      .value (packBits (activeVector ms iteration)) := by
  let A := BatchEntry.entryVal8 s src len out sched panic
    (Vector.ofFn fun lane => BitVec.ofNat 64 (ms lane).length)
  have forward : transposeInput A ms iteration lo hi ⟨18, rfl⟩ =
      BatchHeader.values8 (headerAt8Val A ms iteration) ⟨24, rfl⟩ :=
    BatchFieldForward.all_mask A (headerAt8Val A ms iteration) lo hi
  rw [forward]
  have ha : (show Vector (LLVM.IntW 1) 8 from
      BatchHeader.values8 (headerAt8Val A ms iteration) ⟨24, rfl⟩) =
      (activeVector ms iteration).map PoisonOr.value := by
    apply Vector.ext
    intro i hi
    simp only [activeVector, Vector.getElem_map, Vector.getElem_ofFn]
    exact BatchHeader.active_lane s src len out sched panic ms iteration ⟨i, hi⟩ hms
  exact (congrArg (fun (v : Vector (LLVM.IntW 1) 8) =>
    SLLVM.bitcast (.vector 8 (.bitvec (.concrete 1))) (.bitvec (.concrete 8)) v) ha).trans
      (BatchTranspose.bitcast_active8 _)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
/-- All load, transpose, scratch-pointer and mask operands of the final input
block follow from the existing scalar-state header and the loaded rows. -/
theorem env (s : GlobalState) (src len out sched panic : Pointer)
    (ms : Fin 8 → AgaveConcrete.Message) (iteration : Nat)
    (hms : ∀ lane, (ms lane).length ≤ 1024)
    (lo hi : Vector (Vector (BitVec 32) 8) 8) :
    BatchTranspose.Env8
      (transposeInput (BatchEntry.entryVal8 s src len out sched panic
        (Vector.ofFn fun lane => BitVec.ofNat 64 (ms lane).length)) ms iteration lo hi)
      (BatchEntry.scratch s 0)
      (rowPtr (src.withOffset 6144) (wordAt ms iteration 6 + 8))
      (rowPtr (src.withOffset 7168) (wordAt ms iteration 7 + 8))
      (lowColumns lo) hi (packBits (activeVector ms iteration)) := by
  let A := BatchEntry.entryVal8 s src len out sched panic
    (Vector.ofFn fun lane => BitVec.ofNat 64 (ms lane).length)
  let V := transposeInput A ms iteration lo hi
  constructor
  · have hp : V ⟨46, rfl⟩ = PoisonOr.value (src.withOffset 6144) := by rfl
    have hw : V ⟨1, rfl⟩ = PoisonOr.value (wordAt ms iteration 6 + 8) := by
      change LLVM.add
        (LLVM.lshr (((Vector.ofFn fun lane : Fin 8 =>
          BitVec.ofNat 64 (batchOffset (ms lane).length iteration)).map PoisonOr.value)[6])
          (.value 2#64)) (.value 8#64) {nsw := true, nuw := true} = _
      simp only [Vector.getElem_map, Vector.getElem_ofFn]
      have hj : min iteration (AgaveBatchControl.rootIndex (ms 6).length) ≤ 15 := by
        have h := batchOffset_le_960 (ms 6).length iteration (hms 6)
        unfold batchOffset at h
        omega
      have hs : LLVM.lshr (.value (BitVec.ofNat 64 (batchOffset (ms 6).length iteration)))
          (.value 2#64) = .value (wordAt ms iteration 6) := BatchLoadPath.word_shift _ hj
      change LLVM.add
        (LLVM.lshr (.value (BitVec.ofNat 64 (batchOffset (ms 6).length iteration))) (.value 2#64))
        (.value 8#64) {nsw := true, nuw := true} = _
      rw [hs]
      exact addEight_safe _ (BatchSecondHalf.wordAt_bound ms iteration 6 (hms 6))
    change gep (V ⟨46, rfl⟩) 4 0 (V ⟨1, rfl⟩) = _
    rw [hp, hw]
    simp [gep, ptradd, rowPtr, Pointer.withOffset, LLVM.add, LLVM.mul,
      LLVM.const?, LLVM.add?, LLVM.mul?]
  · have hp : V ⟨45, rfl⟩ = PoisonOr.value (src.withOffset 7168) := by rfl
    have hw : V ⟨0, rfl⟩ = PoisonOr.value (wordAt ms iteration 7 + 8) := by
      change LLVM.add
        (LLVM.lshr (((Vector.ofFn fun lane : Fin 8 =>
          BitVec.ofNat 64 (batchOffset (ms lane).length iteration)).map PoisonOr.value)[7])
          (.value 2#64)) (.value 8#64) {nsw := true, nuw := true} = _
      simp only [Vector.getElem_map, Vector.getElem_ofFn]
      have hj : min iteration (AgaveBatchControl.rootIndex (ms 7).length) ≤ 15 := by
        have h := batchOffset_le_960 (ms 7).length iteration (hms 7)
        unfold batchOffset at h
        omega
      have hs : LLVM.lshr (.value (BitVec.ofNat 64 (batchOffset (ms 7).length iteration)))
          (.value 2#64) = .value (wordAt ms iteration 7) := BatchLoadPath.word_shift _ hj
      change LLVM.add
        (LLVM.lshr (.value (BitVec.ofNat 64 (batchOffset (ms 7).length iteration))) (.value 2#64))
        (.value 8#64) {nsw := true, nuw := true} = _
      rw [hs]
      exact addEight_safe _ (BatchSecondHalf.wordAt_bound ms iteration 7 (hms 7))
    change gep (V ⟨45, rfl⟩) 4 0 (V ⟨0, rfl⟩) = _
    rw [hp, hw]
    simp [gep, ptradd, rowPtr, Pointer.withOffset, LLVM.add, LLVM.mul,
      LLVM.const?, LLVM.add?, LLVM.mul?]
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · change (BatchFirstTranspose.transposeRows8 (lo.map (·.map PoisonOr.value)))[0] = _
    rw [lowColumns_defined]
    simp
  · change (BatchFirstTranspose.transposeRows8 (lo.map (·.map PoisonOr.value)))[1] = _
    rw [lowColumns_defined]
    simp
  · change (BatchFirstTranspose.transposeRows8 (lo.map (·.map PoisonOr.value)))[2] = _
    rw [lowColumns_defined]
    simp
  · change (BatchFirstTranspose.transposeRows8 (lo.map (·.map PoisonOr.value)))[3] = _
    rw [lowColumns_defined]
    simp
  · change (BatchFirstTranspose.transposeRows8 (lo.map (·.map PoisonOr.value)))[4] = _
    rw [lowColumns_defined]
    simp
  · change (BatchFirstTranspose.transposeRows8 (lo.map (·.map PoisonOr.value)))[5] = _
    rw [lowColumns_defined]
    simp
  · change (BatchFirstTranspose.transposeRows8 (lo.map (·.map PoisonOr.value)))[6] = _
    rw [lowColumns_defined]
    simp
  · change (BatchFirstTranspose.transposeRows8 (lo.map (·.map PoisonOr.value)))[7] = _
    rw [lowColumns_defined]
    simp
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
  · exact active_final s src len out sched panic ms iteration hms lo hi
  · rfl

noncomputable def input9 (A : agave_batch_8.cfgCtx.Valuation)
    (args : HVector TyDenote.toType (agave_batch_8.cfgSigs[9]'(by decide))) :
    BatchTranspose.InCtx8.Valuation := Ctxt.Valuation.ofHVector args.reverse ++ A

theorem block9_run (A : agave_batch_8.cfgCtx.Valuation)
    (args : HVector TyDenote.toType (agave_batch_8.cfgSigs[9]'(by decide)))
    (dst p6 p7 : Pointer) (lo hi : Vector (Vector (BitVec 32) 8) 8) (mask : BitVec 8)
    (hV : BatchTranspose.Env8 (input9 A args) dst p6 p7 lo hi mask) (s : GlobalState)
    (hf6 : Fits s.mem p6 256) (hr6 : readWord? p6 256 s.mem = some (packBits hi[6]))
    (hf7 : Fits s.mem p7 256) (hr7 : readWord? p7 256 s.mem = some (packBits hi[7]))
    (hfit : ∀ k < 16, Fits s.mem (dst.withOffset (BitVec.ofNat 64 (32*k))) 256) :
    StateT.run (agave_batch_8.blocks.run A ⟨9, rfl, args⟩) s =
      StateT.run (agave_batch_8.blocks.run A
        (if mask = 0 then BatchTranspose.rootTarget8 (input9 A args)
          else BatchTranspose.nonrootTarget8 (input9 A args)))
        {s with mem := outputMem dst (BatchTranspose.columns8 lo hi) 16 s.mem} := by
  denote_enter_block
  obtain ⟨V', h⟩ := BatchTranspose.transpose8_run
    (input9 A args) dst p6 p7 lo hi mask hV s hf6 hr6 hf7 hr7 hfit
  apply EffectM.run_bind_of_value h

theorem mask_zero_iff (ms : Fin 8 → AgaveConcrete.Message) (iteration : Nat) :
    packBits (activeVector ms iteration) = 0 ↔
      ∀ lane, AgaveBatchControl.rootIndex (ms lane).length ≤ iteration := by
  rw [BatchTranspose.active8_zero_iff]
  constructor
  · intro h lane
    have hh := h lane
    by_cases ha : iteration < AgaveBatchControl.rootIndex (ms lane).length
    · simp [activeVector, Fin.getElem_fin, ha] at hh
    · omega
  · intro h lane
    have hn : ¬iteration < AgaveBatchControl.rootIndex (ms lane).length := by
      have := h lane
      omega
    simp [activeVector, Fin.getElem_fin, hn]

/-- No legal batch can take another compression backedge after test fifteen. -/
theorem mask_zero_at15 (ms : Fin 8 → AgaveConcrete.Message)
    (hms : ∀ lane, (ms lane).length ≤ 1024) :
    packBits (activeVector ms 15) = 0 := by
  apply (mask_zero_iff ms 15).mpr
  intro lane
  have := AgaveBatchControl.rootIndex_lt16 (ms lane).length (hms lane)
  omega

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
/-- The complete actual load/transpose path from the loop header writes all
sixteen scratch vectors and dispatches with the scalar active-lane mask.
Every panic edge on the path is excluded by legal message lengths. -/
theorem run (s u : GlobalState) (src len out sched panic : Pointer)
    (ms : Fin 8 → AgaveConcrete.Message) (iteration : Nat)
    (hms : ∀ lane, (ms lane).length ≤ 1024)
    (lo hi : Vector (Vector (BitVec 32) 8) 8)
    (hfl : ∀ lane, Fits u.mem (rowPtr (sourceAt src lane) (wordAt ms iteration lane)) 256)
    (hrl : ∀ lane, readWord? (rowPtr (sourceAt src lane) (wordAt ms iteration lane)) 256 u.mem =
      some (packBits lo[lane.val]))
    (hfh : ∀ lane, Fits u.mem (rowPtr (sourceAt src lane) (wordAt ms iteration lane + 8)) 256)
    (hrh : ∀ lane, readWord? (rowPtr (sourceAt src lane) (wordAt ms iteration lane + 8)) 256 u.mem =
      some (packBits hi[lane.val]))
    (hfit : ∀ k < 16, Fits u.mem ((BatchEntry.scratch s 0).withOffset (BitVec.ofNat 64 (32*k))) 256) :
    let A := BatchEntry.entryVal8 s src len out sched panic
      (Vector.ofFn fun lane => BitVec.ofNat 64 (ms lane).length)
    let V := transposeInput A ms iteration lo hi
    StateT.run (agave_batch_8.blocks.run A (headerAt8 ms iteration)) u =
    StateT.run (agave_batch_8.blocks.run A
      (if packBits (activeVector ms iteration) = 0 then BatchTranspose.rootTarget8 V
        else BatchTranspose.nonrootTarget8 V))
      {u with mem := outputMem (BatchEntry.scratch s 0) (BatchTranspose.columns8 (lowColumns lo) hi) 16 u.mem} := by
  dsimp only
  let A := BatchEntry.entryVal8 s src len out sched panic
    (Vector.ofFn fun lane => BitVec.ofNat 64 (ms lane).length)
  calc
    _ = StateT.run (agave_batch_8.blocks.run A (BatchSecondHalf.startTarget A ms iteration lo)) u := by
      apply BatchFirstHalf.run s u src len out sched panic _ ms iteration hms lo hfl hrl
    _ = StateT.run (agave_batch_8.blocks.run A ⟨8, rfl, guardArgs A ms iteration lo hi⟩) u := by
      apply BatchSecondHalf.six_run s u src len out sched panic _ ms iteration hms lo hi hfh hrh
    _ = StateT.run (agave_batch_8.blocks.run A
        (BatchLoads.next8 (BatchSecondLoadPath.input8 A (guardArgs A ms iteration lo hi)))) u := by
      apply BatchSecondHalf.guard_run s u src len out sched panic _ ms iteration hms lo hi
    _ = _ := by
      apply block9_run A _ (BatchEntry.scratch s 0)
        (rowPtr (src.withOffset 6144) (wordAt ms iteration 6 + 8))
        (rowPtr (src.withOffset 7168) (wordAt ms iteration 7 + 8))
        (lowColumns lo) hi (packBits (activeVector ms iteration))
        (env s src len out sched panic ms iteration hms lo hi) u (hfh 6) (hrh 6) (hfh 7) (hrh 7) hfit

end AgaveLatticeHash.MLIR.BatchTransposePath
