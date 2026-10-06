/- Released under Apache 2.0 license as described in the file LICENSE. -/
import SSA.Projects.Agave.LatticeHash.MLIR.BatchHeader
import SSA.Projects.Agave.LatticeHash.MLIR.BatchLoads
import SSA.Projects.Agave.LatticeHash.MLIR.BatchFirstTranspose

namespace AgaveLatticeHash.MLIR.BatchLoadPath
open LeanMLIR SLLVM Firedancer
open InstCombine (LLVM)
open BatchLoads

noncomputable def input10 (A : agave_batch_8.cfgCtx.Valuation)
    (args : HVector TyDenote.toType (agave_batch_8.cfgSigs[10]'(by decide))) : Input10.Valuation :=
  Ctxt.Valuation.ofHVector args.reverse ++ A

/-- Execute source load block 10 in its actual dispatcher context. -/
theorem run10 (A : agave_batch_8.cfgCtx.Valuation)
    (args : HVector TyDenote.toType (agave_batch_8.cfgSigs[10]'(by decide)))
    (s : GlobalState)
    (p : Pointer) (word off : BitVec 64) (row : Vector (BitVec 32) 8)
    (hp : (input10 A args) ⟨128, rfl⟩ = PoisonOr.value p)
    (hi : (input10 A args) ⟨14, rfl⟩ = PoisonOr.value word)
    (ho : (input10 A args) ⟨13, rfl⟩ = PoisonOr.value off)
    (hl : (input10 A args) ⟨81, rfl⟩ = PoisonOr.value 1027#64)
    (hb : off.toNat ≤ 960)
    (hf : Fits s.mem (rowPtr p word) 256)
    (hr : readWord? (rowPtr p word) 256 s.mem = some (packBits row))
 :
    StateT.run (agave_batch_8.blocks.run A ⟨10, rfl, args⟩) s =
      StateT.run (agave_batch_8.blocks.run A (next10 (input10 A args) row)) s := by
  denote_enter_block
  apply block10_continue (input10 A args) s p word off row hp hi ho hl hb hf hr

noncomputable def input11 (A : agave_batch_8.cfgCtx.Valuation)
    (args : HVector TyDenote.toType (agave_batch_8.cfgSigs[11]'(by decide))) : Input11.Valuation :=
  Ctxt.Valuation.ofHVector args.reverse ++ A

/-- Execute source load block 11 in its actual dispatcher context. -/
theorem run11 (A : agave_batch_8.cfgCtx.Valuation)
    (args : HVector TyDenote.toType (agave_batch_8.cfgSigs[11]'(by decide)))
    (s : GlobalState)
    (p : Pointer) (word off : BitVec 64) (row : Vector (BitVec 32) 8)
    (hp : (input11 A args) ⟨52, rfl⟩ = PoisonOr.value p)
    (hi : (input11 A args) ⟨13, rfl⟩ = PoisonOr.value word)
    (ho : (input11 A args) ⟨12, rfl⟩ = PoisonOr.value off)
    (hl : (input11 A args) ⟨82, rfl⟩ = PoisonOr.value 1027#64)
    (hb : off.toNat ≤ 960)
    (hf : Fits s.mem (rowPtr p word) 256)
    (hr : readWord? (rowPtr p word) 256 s.mem = some (packBits row))
 :
    StateT.run (agave_batch_8.blocks.run A ⟨11, rfl, args⟩) s =
      StateT.run (agave_batch_8.blocks.run A (next11 (input11 A args) row)) s := by
  denote_enter_block
  apply block11_continue (input11 A args) s p word off row hp hi ho hl hb hf hr

noncomputable def input12 (A : agave_batch_8.cfgCtx.Valuation)
    (args : HVector TyDenote.toType (agave_batch_8.cfgSigs[12]'(by decide))) : Input12.Valuation :=
  Ctxt.Valuation.ofHVector args.reverse ++ A

/-- Execute source load block 12 in its actual dispatcher context. -/
theorem run12 (A : agave_batch_8.cfgCtx.Valuation)
    (args : HVector TyDenote.toType (agave_batch_8.cfgSigs[12]'(by decide)))
    (s : GlobalState)
    (p : Pointer) (word off : BitVec 64) (row : Vector (BitVec 32) 8)
    (hp : (input12 A args) ⟨52, rfl⟩ = PoisonOr.value p)
    (hi : (input12 A args) ⟨12, rfl⟩ = PoisonOr.value word)
    (ho : (input12 A args) ⟨11, rfl⟩ = PoisonOr.value off)
    (hl : (input12 A args) ⟨83, rfl⟩ = PoisonOr.value 1027#64)
    (hb : off.toNat ≤ 960)
    (hf : Fits s.mem (rowPtr p word) 256)
    (hr : readWord? (rowPtr p word) 256 s.mem = some (packBits row))
 :
    StateT.run (agave_batch_8.blocks.run A ⟨12, rfl, args⟩) s =
      StateT.run (agave_batch_8.blocks.run A (next12 (input12 A args) row)) s := by
  denote_enter_block
  apply block12_continue (input12 A args) s p word off row hp hi ho hl hb hf hr

noncomputable def input13 (A : agave_batch_8.cfgCtx.Valuation)
    (args : HVector TyDenote.toType (agave_batch_8.cfgSigs[13]'(by decide))) : Input13.Valuation :=
  Ctxt.Valuation.ofHVector args.reverse ++ A

/-- Execute source load block 13 in its actual dispatcher context. -/
theorem run13 (A : agave_batch_8.cfgCtx.Valuation)
    (args : HVector TyDenote.toType (agave_batch_8.cfgSigs[13]'(by decide)))
    (s : GlobalState)
    (p : Pointer) (word off : BitVec 64) (row : Vector (BitVec 32) 8)
    (hp : (input13 A args) ⟨52, rfl⟩ = PoisonOr.value p)
    (hi : (input13 A args) ⟨11, rfl⟩ = PoisonOr.value word)
    (ho : (input13 A args) ⟨10, rfl⟩ = PoisonOr.value off)
    (hl : (input13 A args) ⟨84, rfl⟩ = PoisonOr.value 1027#64)
    (hb : off.toNat ≤ 960)
    (hf : Fits s.mem (rowPtr p word) 256)
    (hr : readWord? (rowPtr p word) 256 s.mem = some (packBits row))
 :
    StateT.run (agave_batch_8.blocks.run A ⟨13, rfl, args⟩) s =
      StateT.run (agave_batch_8.blocks.run A (next13 (input13 A args) row)) s := by
  denote_enter_block
  apply block13_continue (input13 A args) s p word off row hp hi ho hl hb hf hr

noncomputable def input14 (A : agave_batch_8.cfgCtx.Valuation)
    (args : HVector TyDenote.toType (agave_batch_8.cfgSigs[14]'(by decide))) : Input14.Valuation :=
  Ctxt.Valuation.ofHVector args.reverse ++ A

/-- Execute source load block 14 in its actual dispatcher context. -/
theorem run14 (A : agave_batch_8.cfgCtx.Valuation)
    (args : HVector TyDenote.toType (agave_batch_8.cfgSigs[14]'(by decide)))
    (s : GlobalState)
    (p : Pointer) (word off : BitVec 64) (row : Vector (BitVec 32) 8)
    (hp : (input14 A args) ⟨52, rfl⟩ = PoisonOr.value p)
    (hi : (input14 A args) ⟨10, rfl⟩ = PoisonOr.value word)
    (ho : (input14 A args) ⟨9, rfl⟩ = PoisonOr.value off)
    (hl : (input14 A args) ⟨85, rfl⟩ = PoisonOr.value 1027#64)
    (hb : off.toNat ≤ 960)
    (hf : Fits s.mem (rowPtr p word) 256)
    (hr : readWord? (rowPtr p word) 256 s.mem = some (packBits row))
 :
    StateT.run (agave_batch_8.blocks.run A ⟨14, rfl, args⟩) s =
      StateT.run (agave_batch_8.blocks.run A (next14 (input14 A args) row)) s := by
  denote_enter_block
  apply block14_continue (input14 A args) s p word off row hp hi ho hl hb hf hr

noncomputable def input15 (A : agave_batch_8.cfgCtx.Valuation)
    (args : HVector TyDenote.toType (agave_batch_8.cfgSigs[15]'(by decide))) : Input15.Valuation :=
  Ctxt.Valuation.ofHVector args.reverse ++ A

/-- Execute source load block 15 in its actual dispatcher context. -/
theorem run15 (A : agave_batch_8.cfgCtx.Valuation)
    (args : HVector TyDenote.toType (agave_batch_8.cfgSigs[15]'(by decide)))
    (s : GlobalState)
    (p : Pointer) (word off : BitVec 64) (row : Vector (BitVec 32) 8)
    (hp : (input15 A args) ⟨52, rfl⟩ = PoisonOr.value p)
    (hi : (input15 A args) ⟨9, rfl⟩ = PoisonOr.value word)
    (ho : (input15 A args) ⟨8, rfl⟩ = PoisonOr.value off)
    (hl : (input15 A args) ⟨86, rfl⟩ = PoisonOr.value 1027#64)
    (hb : off.toNat ≤ 960)
    (hf : Fits s.mem (rowPtr p word) 256)
    (hr : readWord? (rowPtr p word) 256 s.mem = some (packBits row))
 :
    StateT.run (agave_batch_8.blocks.run A ⟨15, rfl, args⟩) s =
      StateT.run (agave_batch_8.blocks.run A (next15 (input15 A args) row)) s := by
  denote_enter_block
  apply block15_continue (input15 A args) s p word off row hp hi ho hl hb hf hr

structure Ready10 (V : Input10.Valuation) (s : GlobalState) (row : Vector (BitVec 32) 8) where
  p : Pointer
  word : BitVec 64
  off : BitVec 64
  pointer : V ⟨128, rfl⟩ = PoisonOr.value p
  index : V ⟨14, rfl⟩ = PoisonOr.value word
  offset : V ⟨13, rfl⟩ = PoisonOr.value off
  limit : V ⟨81, rfl⟩ = PoisonOr.value 1027#64
  bound : off.toNat ≤ 960
  fits : Fits s.mem (rowPtr p word) 256
  read : readWord? (rowPtr p word) 256 s.mem = some (packBits row)

structure Ready11 (V : Input11.Valuation) (s : GlobalState) (row : Vector (BitVec 32) 8) where
  p : Pointer
  word : BitVec 64
  off : BitVec 64
  pointer : V ⟨52, rfl⟩ = PoisonOr.value p
  index : V ⟨13, rfl⟩ = PoisonOr.value word
  offset : V ⟨12, rfl⟩ = PoisonOr.value off
  limit : V ⟨82, rfl⟩ = PoisonOr.value 1027#64
  bound : off.toNat ≤ 960
  fits : Fits s.mem (rowPtr p word) 256
  read : readWord? (rowPtr p word) 256 s.mem = some (packBits row)

structure Ready12 (V : Input12.Valuation) (s : GlobalState) (row : Vector (BitVec 32) 8) where
  p : Pointer
  word : BitVec 64
  off : BitVec 64
  pointer : V ⟨52, rfl⟩ = PoisonOr.value p
  index : V ⟨12, rfl⟩ = PoisonOr.value word
  offset : V ⟨11, rfl⟩ = PoisonOr.value off
  limit : V ⟨83, rfl⟩ = PoisonOr.value 1027#64
  bound : off.toNat ≤ 960
  fits : Fits s.mem (rowPtr p word) 256
  read : readWord? (rowPtr p word) 256 s.mem = some (packBits row)

structure Ready13 (V : Input13.Valuation) (s : GlobalState) (row : Vector (BitVec 32) 8) where
  p : Pointer
  word : BitVec 64
  off : BitVec 64
  pointer : V ⟨52, rfl⟩ = PoisonOr.value p
  index : V ⟨11, rfl⟩ = PoisonOr.value word
  offset : V ⟨10, rfl⟩ = PoisonOr.value off
  limit : V ⟨84, rfl⟩ = PoisonOr.value 1027#64
  bound : off.toNat ≤ 960
  fits : Fits s.mem (rowPtr p word) 256
  read : readWord? (rowPtr p word) 256 s.mem = some (packBits row)

structure Ready14 (V : Input14.Valuation) (s : GlobalState) (row : Vector (BitVec 32) 8) where
  p : Pointer
  word : BitVec 64
  off : BitVec 64
  pointer : V ⟨52, rfl⟩ = PoisonOr.value p
  index : V ⟨10, rfl⟩ = PoisonOr.value word
  offset : V ⟨9, rfl⟩ = PoisonOr.value off
  limit : V ⟨85, rfl⟩ = PoisonOr.value 1027#64
  bound : off.toNat ≤ 960
  fits : Fits s.mem (rowPtr p word) 256
  read : readWord? (rowPtr p word) 256 s.mem = some (packBits row)

structure Ready15 (V : Input15.Valuation) (s : GlobalState) (row : Vector (BitVec 32) 8) where
  p : Pointer
  word : BitVec 64
  off : BitVec 64
  pointer : V ⟨52, rfl⟩ = PoisonOr.value p
  index : V ⟨9, rfl⟩ = PoisonOr.value word
  offset : V ⟨8, rfl⟩ = PoisonOr.value off
  limit : V ⟨86, rfl⟩ = PoisonOr.value 1027#64
  bound : off.toNat ≤ 960
  fits : Fits s.mem (rowPtr p word) 256
  read : readWord? (rowPtr p word) 256 s.mem = some (packBits row)

noncomputable def args11 (A : agave_batch_8.cfgCtx.Valuation)
    (args : HVector TyDenote.toType (agave_batch_8.cfgSigs[10]'(by decide)))
    (rows : Fin 6 → Vector (BitVec 32) 8) :
    HVector TyDenote.toType (agave_batch_8.cfgSigs[11]'(by decide)) :=
  (next10 (input10 A args) (rows 0)).args

noncomputable def args12 (A : agave_batch_8.cfgCtx.Valuation)
    (args : HVector TyDenote.toType (agave_batch_8.cfgSigs[10]'(by decide)))
    (rows : Fin 6 → Vector (BitVec 32) 8) :
    HVector TyDenote.toType (agave_batch_8.cfgSigs[12]'(by decide)) :=
  (next11 (input11 A (args11 A args rows)) (rows 1)).args

noncomputable def args13 (A : agave_batch_8.cfgCtx.Valuation)
    (args : HVector TyDenote.toType (agave_batch_8.cfgSigs[10]'(by decide)))
    (rows : Fin 6 → Vector (BitVec 32) 8) :
    HVector TyDenote.toType (agave_batch_8.cfgSigs[13]'(by decide)) :=
  (next12 (input12 A (args12 A args rows)) (rows 2)).args

noncomputable def args14 (A : agave_batch_8.cfgCtx.Valuation)
    (args : HVector TyDenote.toType (agave_batch_8.cfgSigs[10]'(by decide)))
    (rows : Fin 6 → Vector (BitVec 32) 8) :
    HVector TyDenote.toType (agave_batch_8.cfgSigs[14]'(by decide)) :=
  (next13 (input13 A (args13 A args rows)) (rows 3)).args

noncomputable def args15 (A : agave_batch_8.cfgCtx.Valuation)
    (args : HVector TyDenote.toType (agave_batch_8.cfgSigs[10]'(by decide)))
    (rows : Fin 6 → Vector (BitVec 32) 8) :
    HVector TyDenote.toType (agave_batch_8.cfgSigs[15]'(by decide)) :=
  (next14 (input14 A (args14 A args rows)) (rows 4)).args

noncomputable def args16 (A : agave_batch_8.cfgCtx.Valuation)
    (args : HVector TyDenote.toType (agave_batch_8.cfgSigs[10]'(by decide)))
    (rows : Fin 6 → Vector (BitVec 32) 8) :
    HVector TyDenote.toType (agave_batch_8.cfgSigs[16]'(by decide)) :=
  (next15 (input15 A (args15 A args rows)) (rows 5)).args

/-- Six consecutive actual load/guard blocks execute without changing memory.
The hypotheses describe bytes and bounds at the typed intermediate program points. -/
theorem firstSix_run (A : agave_batch_8.cfgCtx.Valuation)
    (args : HVector TyDenote.toType (agave_batch_8.cfgSigs[10]'(by decide)))
    (rows : Fin 6 → Vector (BitVec 32) 8) (s : GlobalState)
    (h10 : Ready10 (input10 A args) s (rows 0))
    (h11 : Ready11 (input11 A (args11 A args rows)) s (rows 1))
    (h12 : Ready12 (input12 A (args12 A args rows)) s (rows 2))
    (h13 : Ready13 (input13 A (args13 A args rows)) s (rows 3))
    (h14 : Ready14 (input14 A (args14 A args rows)) s (rows 4))
    (h15 : Ready15 (input15 A (args15 A args rows)) s (rows 5))
    : StateT.run (agave_batch_8.blocks.run A ⟨10, rfl, args⟩) s =
      StateT.run (agave_batch_8.blocks.run A ⟨16, rfl, args16 A args rows⟩) s := by
  calc
    _ = StateT.run (agave_batch_8.blocks.run A ⟨11, rfl, args11 A args rows⟩) s := by
      apply run10 A args s h10.p h10.word h10.off (rows 0)
      · exact h10.pointer
      · exact h10.index
      · exact h10.offset
      · exact h10.limit
      · exact h10.bound
      · exact h10.fits
      · exact h10.read
    _ = StateT.run (agave_batch_8.blocks.run A ⟨12, rfl, args12 A args rows⟩) s := by
      apply run11 A (args11 A args rows) s h11.p h11.word h11.off (rows 1)
      · exact h11.pointer
      · exact h11.index
      · exact h11.offset
      · exact h11.limit
      · exact h11.bound
      · exact h11.fits
      · exact h11.read
    _ = StateT.run (agave_batch_8.blocks.run A ⟨13, rfl, args13 A args rows⟩) s := by
      apply run12 A (args12 A args rows) s h12.p h12.word h12.off (rows 2)
      · exact h12.pointer
      · exact h12.index
      · exact h12.offset
      · exact h12.limit
      · exact h12.bound
      · exact h12.fits
      · exact h12.read
    _ = StateT.run (agave_batch_8.blocks.run A ⟨14, rfl, args14 A args rows⟩) s := by
      apply run13 A (args13 A args rows) s h13.p h13.word h13.off (rows 3)
      · exact h13.pointer
      · exact h13.index
      · exact h13.offset
      · exact h13.limit
      · exact h13.bound
      · exact h13.fits
      · exact h13.read
    _ = StateT.run (agave_batch_8.blocks.run A ⟨15, rfl, args15 A args rows⟩) s := by
      apply run14 A (args14 A args rows) s h14.p h14.word h14.off (rows 4)
      · exact h14.pointer
      · exact h14.index
      · exact h14.offset
      · exact h14.limit
      · exact h14.bound
      · exact h14.fits
      · exact h14.read
    _ = StateT.run (agave_batch_8.blocks.run A ⟨16, rfl, args16 A args rows⟩) s := by
      apply run15 A (args15 A args rows) s h15.p h15.word h15.off (rows 5)
      · exact h15.pointer
      · exact h15.index
      · exact h15.offset
      · exact h15.limit
      · exact h15.bound
      · exact h15.fits
      · exact h15.read

/-- The compiler's shift computes the word index for each of sixteen blocks. -/
theorem word_shift (j : Nat) (hj : j ≤ 15) :
    LLVM.lshr (.value (BitVec.ofNat 64 (64*j))) (.value 2#64) =
      .value (BitVec.ofNat 64 (16*j)) := by
  interval_cases j <;> rfl

/-- The first load's low-level hypotheses follow from the represented loop
state and the caller's initialized row at the computed address. -/
noncomputable def first10_ready (s u : GlobalState) (src len out sched panic : Pointer)
    (lengths : Vector (BitVec 64) 8) (ms : Fin 8 → AgaveConcrete.Message)
    (iteration : Nat) (hms : ∀ lane, (ms lane).length ≤ 1024)
    (row : Vector (BitVec 32) 8)
    (hf : Fits u.mem (rowPtr src (BitVec.ofNat 64 (16 * min iteration
      (AgaveBatchControl.rootIndex (ms 0).length)))) 256)
    (hr : readWord? (rowPtr src (BitVec.ofNat 64 (16 * min iteration
      (AgaveBatchControl.rootIndex (ms 0).length)))) 256 u.mem = some (packBits row)) :
    Ready10 (input10 (BatchEntry.entryVal8 s src len out sched panic lengths)
      (BatchHeader.next8 (headerAt8Val (BatchEntry.entryVal8 s src len out sched panic lengths)
        ms iteration)).args) u row := by
  refine ⟨src, BitVec.ofNat 64 (16 * min iteration (AgaveBatchControl.rootIndex (ms 0).length)),
    BitVec.ofNat 64 (batchOffset (ms 1).length iteration), ?_, ?_, ?_, ?_, ?_, hf, hr⟩
  · rfl
  · change LLVM.lshr (((Vector.ofFn fun lane : Fin 8 =>
      BitVec.ofNat 64 (batchOffset (ms lane).length iteration)).map PoisonOr.value)[0])
      (.value 2#64) = _
    simp only [Vector.getElem_map, Vector.getElem_ofFn]
    have hj : min iteration (AgaveBatchControl.rootIndex (ms 0).length) ≤ 15 := by
      have h := batchOffset_le_960 (ms 0).length iteration (hms 0)
      unfold batchOffset at h
      omega
    exact word_shift _ hj
  · change (((Vector.ofFn fun lane : Fin 8 =>
      BitVec.ofNat 64 (batchOffset (ms lane).length iteration)).map PoisonOr.value)[1]) = _
    simp
  · rfl
  · simp only [BitVec.toNat_ofNat]
    exact Nat.le_trans (Nat.mod_le ..) (batchOffset_le_960 _ _ (hms 1))

/-- Derived entry facts for source load block 11, with all earlier rows retained. -/
noncomputable def first11_ready (s u : GlobalState) (src len out sched panic : Pointer)
    (lengths : Vector (BitVec 64) 8) (ms : Fin 8 → AgaveConcrete.Message)
    (iteration : Nat) (hms : ∀ lane, (ms lane).length ≤ 1024)
    (rows : Fin 6 → Vector (BitVec 32) 8)
    (hf : Fits u.mem (rowPtr (src.withOffset 1024) (BitVec.ofNat 64 (16 * min iteration
      (AgaveBatchControl.rootIndex (ms 1).length)))) 256)
    (hr : readWord? (rowPtr (src.withOffset 1024) (BitVec.ofNat 64 (16 * min iteration
      (AgaveBatchControl.rootIndex (ms 1).length)))) 256 u.mem = some (packBits (rows 1))) :
    Ready11 (input11 (BatchEntry.entryVal8 s src len out sched panic lengths)
      (args11 (BatchEntry.entryVal8 s src len out sched panic lengths) (BatchHeader.next8 (headerAt8Val (BatchEntry.entryVal8 s src len out sched panic lengths) ms iteration)).args rows)) u (rows 1) := by
  refine ⟨src.withOffset 1024, BitVec.ofNat 64 (16 * min iteration (AgaveBatchControl.rootIndex (ms 1).length)),
    BitVec.ofNat 64 (batchOffset (ms 2).length iteration), ?_, ?_, ?_, ?_, ?_, hf, hr⟩
  · rfl
  · change LLVM.lshr (((Vector.ofFn fun lane : Fin 8 =>
      BitVec.ofNat 64 (batchOffset (ms lane).length iteration)).map PoisonOr.value)[1])
      (.value 2#64) = _
    simp only [Vector.getElem_map, Vector.getElem_ofFn]
    have hj : min iteration (AgaveBatchControl.rootIndex (ms 1).length) ≤ 15 := by
      have h := batchOffset_le_960 (ms 1).length iteration (hms 1)
      unfold batchOffset at h
      omega
    exact word_shift _ hj
  · change (((Vector.ofFn fun lane : Fin 8 =>
      BitVec.ofNat 64 (batchOffset (ms lane).length iteration)).map PoisonOr.value)[2]) = _
    simp
  · rfl
  · simp only [BitVec.toNat_ofNat]
    exact Nat.le_trans (Nat.mod_le ..) (batchOffset_le_960 _ _ (hms 2))

/-- Derived entry facts for source load block 12, with all earlier rows retained. -/
noncomputable def first12_ready (s u : GlobalState) (src len out sched panic : Pointer)
    (lengths : Vector (BitVec 64) 8) (ms : Fin 8 → AgaveConcrete.Message)
    (iteration : Nat) (hms : ∀ lane, (ms lane).length ≤ 1024)
    (rows : Fin 6 → Vector (BitVec 32) 8)
    (hf : Fits u.mem (rowPtr (src.withOffset 2048) (BitVec.ofNat 64 (16 * min iteration
      (AgaveBatchControl.rootIndex (ms 2).length)))) 256)
    (hr : readWord? (rowPtr (src.withOffset 2048) (BitVec.ofNat 64 (16 * min iteration
      (AgaveBatchControl.rootIndex (ms 2).length)))) 256 u.mem = some (packBits (rows 2))) :
    Ready12 (input12 (BatchEntry.entryVal8 s src len out sched panic lengths)
      (args12 (BatchEntry.entryVal8 s src len out sched panic lengths) (BatchHeader.next8 (headerAt8Val (BatchEntry.entryVal8 s src len out sched panic lengths) ms iteration)).args rows)) u (rows 2) := by
  refine ⟨src.withOffset 2048, BitVec.ofNat 64 (16 * min iteration (AgaveBatchControl.rootIndex (ms 2).length)),
    BitVec.ofNat 64 (batchOffset (ms 3).length iteration), ?_, ?_, ?_, ?_, ?_, hf, hr⟩
  · rfl
  · change LLVM.lshr (((Vector.ofFn fun lane : Fin 8 =>
      BitVec.ofNat 64 (batchOffset (ms lane).length iteration)).map PoisonOr.value)[2])
      (.value 2#64) = _
    simp only [Vector.getElem_map, Vector.getElem_ofFn]
    have hj : min iteration (AgaveBatchControl.rootIndex (ms 2).length) ≤ 15 := by
      have h := batchOffset_le_960 (ms 2).length iteration (hms 2)
      unfold batchOffset at h
      omega
    exact word_shift _ hj
  · change (((Vector.ofFn fun lane : Fin 8 =>
      BitVec.ofNat 64 (batchOffset (ms lane).length iteration)).map PoisonOr.value)[3]) = _
    simp
  · rfl
  · simp only [BitVec.toNat_ofNat]
    exact Nat.le_trans (Nat.mod_le ..) (batchOffset_le_960 _ _ (hms 3))

/-- Derived entry facts for source load block 13, with all earlier rows retained. -/
noncomputable def first13_ready (s u : GlobalState) (src len out sched panic : Pointer)
    (lengths : Vector (BitVec 64) 8) (ms : Fin 8 → AgaveConcrete.Message)
    (iteration : Nat) (hms : ∀ lane, (ms lane).length ≤ 1024)
    (rows : Fin 6 → Vector (BitVec 32) 8)
    (hf : Fits u.mem (rowPtr (src.withOffset 3072) (BitVec.ofNat 64 (16 * min iteration
      (AgaveBatchControl.rootIndex (ms 3).length)))) 256)
    (hr : readWord? (rowPtr (src.withOffset 3072) (BitVec.ofNat 64 (16 * min iteration
      (AgaveBatchControl.rootIndex (ms 3).length)))) 256 u.mem = some (packBits (rows 3))) :
    Ready13 (input13 (BatchEntry.entryVal8 s src len out sched panic lengths)
      (args13 (BatchEntry.entryVal8 s src len out sched panic lengths) (BatchHeader.next8 (headerAt8Val (BatchEntry.entryVal8 s src len out sched panic lengths) ms iteration)).args rows)) u (rows 3) := by
  refine ⟨src.withOffset 3072, BitVec.ofNat 64 (16 * min iteration (AgaveBatchControl.rootIndex (ms 3).length)),
    BitVec.ofNat 64 (batchOffset (ms 4).length iteration), ?_, ?_, ?_, ?_, ?_, hf, hr⟩
  · rfl
  · change LLVM.lshr (((Vector.ofFn fun lane : Fin 8 =>
      BitVec.ofNat 64 (batchOffset (ms lane).length iteration)).map PoisonOr.value)[3])
      (.value 2#64) = _
    simp only [Vector.getElem_map, Vector.getElem_ofFn]
    have hj : min iteration (AgaveBatchControl.rootIndex (ms 3).length) ≤ 15 := by
      have h := batchOffset_le_960 (ms 3).length iteration (hms 3)
      unfold batchOffset at h
      omega
    exact word_shift _ hj
  · change (((Vector.ofFn fun lane : Fin 8 =>
      BitVec.ofNat 64 (batchOffset (ms lane).length iteration)).map PoisonOr.value)[4]) = _
    simp
  · rfl
  · simp only [BitVec.toNat_ofNat]
    exact Nat.le_trans (Nat.mod_le ..) (batchOffset_le_960 _ _ (hms 4))

/-- Derived entry facts for source load block 14, with all earlier rows retained. -/
noncomputable def first14_ready (s u : GlobalState) (src len out sched panic : Pointer)
    (lengths : Vector (BitVec 64) 8) (ms : Fin 8 → AgaveConcrete.Message)
    (iteration : Nat) (hms : ∀ lane, (ms lane).length ≤ 1024)
    (rows : Fin 6 → Vector (BitVec 32) 8)
    (hf : Fits u.mem (rowPtr (src.withOffset 4096) (BitVec.ofNat 64 (16 * min iteration
      (AgaveBatchControl.rootIndex (ms 4).length)))) 256)
    (hr : readWord? (rowPtr (src.withOffset 4096) (BitVec.ofNat 64 (16 * min iteration
      (AgaveBatchControl.rootIndex (ms 4).length)))) 256 u.mem = some (packBits (rows 4))) :
    Ready14 (input14 (BatchEntry.entryVal8 s src len out sched panic lengths)
      (args14 (BatchEntry.entryVal8 s src len out sched panic lengths) (BatchHeader.next8 (headerAt8Val (BatchEntry.entryVal8 s src len out sched panic lengths) ms iteration)).args rows)) u (rows 4) := by
  refine ⟨src.withOffset 4096, BitVec.ofNat 64 (16 * min iteration (AgaveBatchControl.rootIndex (ms 4).length)),
    BitVec.ofNat 64 (batchOffset (ms 5).length iteration), ?_, ?_, ?_, ?_, ?_, hf, hr⟩
  · rfl
  · change LLVM.lshr (((Vector.ofFn fun lane : Fin 8 =>
      BitVec.ofNat 64 (batchOffset (ms lane).length iteration)).map PoisonOr.value)[4])
      (.value 2#64) = _
    simp only [Vector.getElem_map, Vector.getElem_ofFn]
    have hj : min iteration (AgaveBatchControl.rootIndex (ms 4).length) ≤ 15 := by
      have h := batchOffset_le_960 (ms 4).length iteration (hms 4)
      unfold batchOffset at h
      omega
    exact word_shift _ hj
  · change (((Vector.ofFn fun lane : Fin 8 =>
      BitVec.ofNat 64 (batchOffset (ms lane).length iteration)).map PoisonOr.value)[5]) = _
    simp
  · rfl
  · simp only [BitVec.toNat_ofNat]
    exact Nat.le_trans (Nat.mod_le ..) (batchOffset_le_960 _ _ (hms 5))

/-- Derived entry facts for source load block 15, with all earlier rows retained. -/
noncomputable def first15_ready (s u : GlobalState) (src len out sched panic : Pointer)
    (lengths : Vector (BitVec 64) 8) (ms : Fin 8 → AgaveConcrete.Message)
    (iteration : Nat) (hms : ∀ lane, (ms lane).length ≤ 1024)
    (rows : Fin 6 → Vector (BitVec 32) 8)
    (hf : Fits u.mem (rowPtr (src.withOffset 5120) (BitVec.ofNat 64 (16 * min iteration
      (AgaveBatchControl.rootIndex (ms 5).length)))) 256)
    (hr : readWord? (rowPtr (src.withOffset 5120) (BitVec.ofNat 64 (16 * min iteration
      (AgaveBatchControl.rootIndex (ms 5).length)))) 256 u.mem = some (packBits (rows 5))) :
    Ready15 (input15 (BatchEntry.entryVal8 s src len out sched panic lengths)
      (args15 (BatchEntry.entryVal8 s src len out sched panic lengths) (BatchHeader.next8 (headerAt8Val (BatchEntry.entryVal8 s src len out sched panic lengths) ms iteration)).args rows)) u (rows 5) := by
  refine ⟨src.withOffset 5120, BitVec.ofNat 64 (16 * min iteration (AgaveBatchControl.rootIndex (ms 5).length)),
    BitVec.ofNat 64 (batchOffset (ms 6).length iteration), ?_, ?_, ?_, ?_, ?_, hf, hr⟩
  · rfl
  · change LLVM.lshr (((Vector.ofFn fun lane : Fin 8 =>
      BitVec.ofNat 64 (batchOffset (ms lane).length iteration)).map PoisonOr.value)[5])
      (.value 2#64) = _
    simp only [Vector.getElem_map, Vector.getElem_ofFn]
    have hj : min iteration (AgaveBatchControl.rootIndex (ms 5).length) ≤ 15 := by
      have h := batchOffset_le_960 (ms 5).length iteration (hms 5)
      unfold batchOffset at h
      omega
    exact word_shift _ hj
  · change (((Vector.ofFn fun lane : Fin 8 =>
      BitVec.ofNat 64 (batchOffset (ms lane).length iteration)).map PoisonOr.value)[6]) = _
    simp
  · rfl
  · simp only [BitVec.toNat_ofNat]
    exact Nat.le_trans (Nat.mod_le ..) (batchOffset_le_960 _ _ (hms 6))

/-- Address of a source lane in the fixed eight-slot input layout. -/
def sourceLane (src : Pointer) (lane : Fin 6) : Pointer :=
  if lane.val = 0 then src else src.withOffset (BitVec.ofNat 64 (1024 * lane.val))

def firstWord (ms : Fin 8 → AgaveConcrete.Message) (iteration : Nat) (lane : Fin 6) : BitVec 64 :=
  BitVec.ofNat 64 (16 * min iteration (AgaveBatchControl.rootIndex (ms ⟨lane.val, by omega⟩).length))

/-- Starting at the actual scalar-state header, execute the header and six
source loads. The only memory hypotheses concern the initialized source rows;
all index, pointer, poison and panic-guard facts are derived. -/
theorem header_firstSix_run (s u : GlobalState) (src len out sched panic : Pointer)
    (lengths : Vector (BitVec 64) 8) (ms : Fin 8 → AgaveConcrete.Message)
    (iteration : Nat) (hms : ∀ lane, (ms lane).length ≤ 1024)
    (rows : Fin 6 → Vector (BitVec 32) 8)
    (hf : ∀ lane, Fits u.mem (rowPtr (sourceLane src lane) (firstWord ms iteration lane)) 256)
    (hr : ∀ lane, readWord? (rowPtr (sourceLane src lane) (firstWord ms iteration lane)) 256 u.mem =
      some (packBits (rows lane))) :
    StateT.run (agave_batch_8.blocks.run (BatchEntry.entryVal8 s src len out sched panic lengths)
      (headerAt8 ms iteration)) u =
    StateT.run (agave_batch_8.blocks.run (BatchEntry.entryVal8 s src len out sched panic lengths)
      ⟨16, rfl, args16 (BatchEntry.entryVal8 s src len out sched panic lengths)
        (BatchHeader.next8 (headerAt8Val (BatchEntry.entryVal8 s src len out sched panic lengths)
          ms iteration)).args rows⟩) u := by
  rw [BatchHeader.run8 s u src len out sched panic lengths ms iteration hms]
  apply firstSix_run
  · exact first10_ready s u src len out sched panic lengths ms iteration hms (rows 0) (hf 0) (hr 0)
  · exact first11_ready s u src len out sched panic lengths ms iteration hms rows (hf 1) (hr 1)
  · exact first12_ready s u src len out sched panic lengths ms iteration hms rows (hf 2) (hr 2)
  · exact first13_ready s u src len out sched panic lengths ms iteration hms rows (hf 3) (hr 3)
  · exact first14_ready s u src len out sched panic lengths ms iteration hms rows (hf 4) (hr 4)
  · exact first15_ready s u src len out sched panic lengths ms iteration hms rows (hf 5) (hr 5)

end AgaveLatticeHash.MLIR.BatchLoadPath
