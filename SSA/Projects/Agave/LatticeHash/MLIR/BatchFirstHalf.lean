/- Released under Apache 2.0 license as described in the file LICENSE. -/
import SSA.Projects.Agave.LatticeHash.MLIR.BatchLoadPath

namespace AgaveLatticeHash.MLIR.BatchFirstHalf
open LeanMLIR SLLVM Firedancer
open InstCombine (LLVM)
open BatchLoads BatchLoadPath

noncomputable def input16 (A : agave_batch_8.cfgCtx.Valuation)
    (args : HVector TyDenote.toType (agave_batch_8.cfgSigs[16]'(by decide))) : Guard8Ctx.Valuation :=
  Ctxt.Valuation.ofHVector args.reverse ++ A

theorem run16 (A : agave_batch_8.cfgCtx.Valuation)
    (args : HVector TyDenote.toType (agave_batch_8.cfgSigs[16]'(by decide))) (s : GlobalState)
    (off : BitVec 64)
    (ho : input16 A args ⟨7, rfl⟩ = .value off)
    (hl : input16 A args ⟨87, rfl⟩ = .value 1027#64)
    (hb : off.toNat ≤ 960) :
    StateT.run (agave_batch_8.blocks.run A ⟨16, rfl, args⟩) s =
      StateT.run (agave_batch_8.blocks.run A (firstHalfGuardNext8 (input16 A args))) s := by
  denote_enter_block
  apply agave_batch_8_last_load_guard_continue (input16 A args) s off ho hl hb

noncomputable def firstTransposeInput (A : agave_batch_8.cfgCtx.Valuation)
    (args : HVector TyDenote.toType (agave_batch_8.cfgSigs[16]'(by decide))) :
    BatchFirstTranspose.InCtx8.Valuation :=
  Ctxt.Valuation.ofHVector (firstHalfGuardNext8 (input16 A args)).args.reverse ++ A

theorem firstTranspose_run (A : agave_batch_8.cfgCtx.Valuation)
    (args : HVector TyDenote.toType (agave_batch_8.cfgSigs[16]'(by decide)))
    (p6 p7 : Pointer) (rows : Vector (Vector (BitVec 32) 8) 8) (off : BitVec 64)
    (hV : BatchFirstTranspose.Env8 (firstTransposeInput A args) p6 p7 rows off)
    (hb : off.toNat ≤ 960) (s : GlobalState)
    (hf6 : Fits s.mem p6 256) (hr6 : readWord? p6 256 s.mem = some (packBits rows[6]))
    (hf7 : Fits s.mem p7 256) (hr7 : readWord? p7 256 s.mem = some (packBits rows[7])) :
    StateT.run (agave_batch_8.blocks.run A (firstHalfGuardNext8 (input16 A args))) s =
      StateT.run (agave_batch_8.blocks.run A
        (BatchFirstTranspose.next8 (firstTransposeInput A args)
          (BatchFirstTranspose.transposeRows8 (rows.map (·.map PoisonOr.value)))
          (BatchFirstTranspose.nextOffset8 (firstTransposeInput A args)))) s := by
  denote_enter_block
  obtain ⟨V', h⟩ := BatchFirstTranspose.first8_run
    (firstTransposeInput A args) p6 p7 rows off hV hb s hf6 hr6 hf7 hr7
  apply EffectM.run_bind_of_value h

def firstRows (rows : Vector (Vector (BitVec 32) 8) 8) (i : Fin 6) := rows[i.val]'(by omega)
noncomputable def guardArgs (A : agave_batch_8.cfgCtx.Valuation)
    (ms : Fin 8 → AgaveConcrete.Message) (iteration : Nat)
    (rows : Vector (Vector (BitVec 32) 8) 8) :=
  args16 A (BatchHeader.next8 (headerAt8Val A ms iteration)).args (firstRows rows)

noncomputable def transposeInput (A : agave_batch_8.cfgCtx.Valuation)
    (ms : Fin 8 → AgaveConcrete.Message) (iteration : Nat)
    (rows : Vector (Vector (BitVec 32) 8) 8) :=
  firstTransposeInput A (guardArgs A ms iteration rows)

def wordAt (ms : Fin 8 → AgaveConcrete.Message) (iteration : Nat) (lane : Fin 8) :=
  BitVec.ofNat 64 (16 * min iteration (AgaveBatchControl.rootIndex (ms lane).length))

set_option maxRecDepth 4096 in
/-- Actual first-half transpose inputs after the six checked source loads. -/
theorem transpose_env (s : GlobalState) (src len out sched panic : Pointer)
    (lengths : Vector (BitVec 64) 8) (ms : Fin 8 → AgaveConcrete.Message)
    (iteration : Nat) (hms : ∀ lane, (ms lane).length ≤ 1024)
    (rows : Vector (Vector (BitVec 32) 8) 8) :
    BatchFirstTranspose.Env8
      (transposeInput (BatchEntry.entryVal8 s src len out sched panic lengths) ms iteration rows)
      (rowPtr (src.withOffset 6144) (wordAt ms iteration 6))
      (rowPtr (src.withOffset 7168) (wordAt ms iteration 7)) rows
      (BitVec.ofNat 64 (batchOffset (ms 0).length iteration)) := by
  let V := transposeInput (BatchEntry.entryVal8 s src len out sched panic lengths) ms iteration rows
  constructor
  · have hp : V ⟨52, rfl⟩ = PoisonOr.value (src.withOffset 6144) := by rfl
    have hw : V ⟨8, rfl⟩ = PoisonOr.value (wordAt ms iteration 6) := by
      dsimp only [V]
      change LLVM.lshr (((Vector.ofFn fun lane : Fin 8 =>
        BitVec.ofNat 64 (batchOffset (ms lane).length iteration)).map PoisonOr.value)[6])
        (.value 2#64) = _
      simp only [Vector.getElem_map, Vector.getElem_ofFn]
      have hj : min iteration (AgaveBatchControl.rootIndex (ms 6).length) ≤ 15 := by
        have h := batchOffset_le_960 (ms 6).length iteration (hms 6)
        unfold batchOffset at h
        omega
      exact word_shift _ hj
    change gep (V ⟨52, rfl⟩) 4 0 (V ⟨8, rfl⟩) = _
    rw [hp, hw]
    simp [gep, ptradd, rowPtr, Pointer.withOffset, LLVM.add, LLVM.mul,
      LLVM.const?, LLVM.add?, LLVM.mul?]
  · have hp : V ⟨51, rfl⟩ = PoisonOr.value (src.withOffset 7168) := by rfl
    have hw : V ⟨6, rfl⟩ = PoisonOr.value (wordAt ms iteration 7) := by
      dsimp only [V]
      change LLVM.lshr (((Vector.ofFn fun lane : Fin 8 =>
        BitVec.ofNat 64 (batchOffset (ms lane).length iteration)).map PoisonOr.value)[7])
        (.value 2#64) = _
      simp only [Vector.getElem_map, Vector.getElem_ofFn]
      have hj : min iteration (AgaveBatchControl.rootIndex (ms 7).length) ≤ 15 := by
        have h := batchOffset_le_960 (ms 7).length iteration (hms 7)
        unfold batchOffset at h
        omega
      exact word_shift _ hj
    change gep (V ⟨51, rfl⟩) 4 0 (V ⟨6, rfl⟩) = _
    rw [hp, hw]
    simp [gep, ptradd, rowPtr, Pointer.withOffset, LLVM.add, LLVM.mul,
      LLVM.const?, LLVM.add?, LLVM.mul?]
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · change (((Vector.ofFn fun lane : Fin 8 =>
      BitVec.ofNat 64 (batchOffset (ms lane).length iteration)).map PoisonOr.value)[0]) = _
    simp
  · rfl

set_option maxRecDepth 4096 in
theorem guard_run (s u : GlobalState) (src len out sched panic : Pointer)
    (lengths : Vector (BitVec 64) 8) (ms : Fin 8 → AgaveConcrete.Message)
    (iteration : Nat) (hms : ∀ lane, (ms lane).length ≤ 1024)
    (rows : Vector (Vector (BitVec 32) 8) 8) :
    StateT.run (agave_batch_8.blocks.run (BatchEntry.entryVal8 s src len out sched panic lengths)
      ⟨16, rfl, guardArgs (BatchEntry.entryVal8 s src len out sched panic lengths) ms iteration rows⟩) u =
    StateT.run (agave_batch_8.blocks.run (BatchEntry.entryVal8 s src len out sched panic lengths)
      (firstHalfGuardNext8 (input16 (BatchEntry.entryVal8 s src len out sched panic lengths)
        (guardArgs (BatchEntry.entryVal8 s src len out sched panic lengths) ms iteration rows)))) u := by
  apply run16 _ _ u (BitVec.ofNat 64 (batchOffset (ms 7).length iteration))
  · change (((Vector.ofFn fun lane : Fin 8 =>
      BitVec.ofNat 64 (batchOffset (ms lane).length iteration)).map PoisonOr.value)[7]) = _
    simp
  · rfl
  · simp only [BitVec.toNat_ofNat]
    exact Nat.le_trans (Nat.mod_le ..) (batchOffset_le_960 _ _ (hms 7))

def sourceAt (src : Pointer) (lane : Fin 8) : Pointer :=
  if lane.val = 0 then src else src.withOffset (BitVec.ofNat 64 (1024 * lane.val))

/-- Execute the entire first-half load path of the actual batch loop: header,
six scalar guarded loads, the last guard, and the compiled transpose block. -/
theorem run (s u : GlobalState) (src len out sched panic : Pointer)
    (lengths : Vector (BitVec 64) 8) (ms : Fin 8 → AgaveConcrete.Message)
    (iteration : Nat) (hms : ∀ lane, (ms lane).length ≤ 1024)
    (rows : Vector (Vector (BitVec 32) 8) 8)
    (hf : ∀ lane, Fits u.mem (rowPtr (sourceAt src lane) (wordAt ms iteration lane)) 256)
    (hr : ∀ lane, readWord? (rowPtr (sourceAt src lane) (wordAt ms iteration lane)) 256 u.mem =
      some (packBits rows[lane.val])) :
    StateT.run (agave_batch_8.blocks.run (BatchEntry.entryVal8 s src len out sched panic lengths)
      (headerAt8 ms iteration)) u =
    StateT.run (agave_batch_8.blocks.run (BatchEntry.entryVal8 s src len out sched panic lengths)
      (BatchFirstTranspose.next8
        (transposeInput (BatchEntry.entryVal8 s src len out sched panic lengths) ms iteration rows)
        (BatchFirstTranspose.transposeRows8 (rows.map (·.map PoisonOr.value)))
        (BatchFirstTranspose.nextOffset8
          (transposeInput (BatchEntry.entryVal8 s src len out sched panic lengths) ms iteration rows)))) u := by
  calc
    _ = StateT.run (agave_batch_8.blocks.run (BatchEntry.entryVal8 s src len out sched panic lengths)
        ⟨16, rfl, guardArgs (BatchEntry.entryVal8 s src len out sched panic lengths) ms iteration rows⟩) u := by
      apply header_firstSix_run s u src len out sched panic lengths ms iteration hms (firstRows rows)
      · intro lane
        exact hf ⟨lane.val, by omega⟩
      · intro lane
        exact hr ⟨lane.val, by omega⟩
    _ = StateT.run (agave_batch_8.blocks.run (BatchEntry.entryVal8 s src len out sched panic lengths)
        (firstHalfGuardNext8 (input16 (BatchEntry.entryVal8 s src len out sched panic lengths)
          (guardArgs (BatchEntry.entryVal8 s src len out sched panic lengths) ms iteration rows)))) u :=
      guard_run s u src len out sched panic lengths ms iteration hms rows
    _ = _ := by
      apply firstTranspose_run _ _ _ _ rows (BitVec.ofNat 64 (batchOffset (ms 0).length iteration))
        (transpose_env s src len out sched panic lengths ms iteration hms rows) _ u (hf 6) (hr 6) (hf 7) (hr 7)
      simp only [BitVec.toNat_ofNat]
      exact Nat.le_trans (Nat.mod_le ..) (batchOffset_le_960 _ _ (hms 0))

end AgaveLatticeHash.MLIR.BatchFirstHalf
