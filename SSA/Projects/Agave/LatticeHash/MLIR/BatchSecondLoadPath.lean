/- Released under Apache 2.0 license as described in the file LICENSE. -/
import SSA.Projects.Agave.LatticeHash.MLIR.BatchLoadPath

namespace AgaveLatticeHash.MLIR.BatchSecondLoadPath
open LeanMLIR SLLVM Firedancer
open InstCombine (LLVM)
open BatchLoads

noncomputable def input2 (A : agave_batch_8.cfgCtx.Valuation)
    (args : HVector TyDenote.toType (agave_batch_8.cfgSigs[2]'(by decide))) : Input2.Valuation :=
  Ctxt.Valuation.ofHVector args.reverse ++ A

theorem run2 (A : agave_batch_8.cfgCtx.Valuation)
    (args : HVector TyDenote.toType (agave_batch_8.cfgSigs[2]'(by decide)))
    (s : GlobalState)
    (p : Pointer) (word off : BitVec 64) (row : Vector (BitVec 32) 8)
    (hp : (input2 A args) ⟨135, rfl⟩ = PoisonOr.value p)
    (hi : (input2 A args) ⟨0, rfl⟩ = PoisonOr.value word)
    (ho : (input2 A args) ⟨22, rfl⟩ = PoisonOr.value off)
    (hl : (input2 A args) ⟨86, rfl⟩ = PoisonOr.value 995#64)
    (hb : off.toNat ≤ 960)
    (hf : Fits s.mem (rowPtr p word) 256)
    (hr : readWord? (rowPtr p word) 256 s.mem = some (packBits row))
 :
    StateT.run (agave_batch_8.blocks.run A ⟨2, rfl, args⟩) s =
      StateT.run (agave_batch_8.blocks.run A (next2 (input2 A args) row)) s := by
  denote_enter_block
  apply block2_continue (input2 A args) s p word off row hp hi ho hl hb hf hr

structure Ready2 (V : Input2.Valuation) (s : GlobalState) (row : Vector (BitVec 32) 8) where
  p : Pointer
  word : BitVec 64
  off : BitVec 64
  pointer : V ⟨135, rfl⟩ = PoisonOr.value p
  index : V ⟨0, rfl⟩ = PoisonOr.value word
  offset : V ⟨22, rfl⟩ = PoisonOr.value off
  limit : V ⟨86, rfl⟩ = PoisonOr.value 995#64
  bound : off.toNat ≤ 960
  fits : Fits s.mem (rowPtr p word) 256
  read : readWord? (rowPtr p word) 256 s.mem = some (packBits row)

noncomputable def input3 (A : agave_batch_8.cfgCtx.Valuation)
    (args : HVector TyDenote.toType (agave_batch_8.cfgSigs[3]'(by decide))) : Input3.Valuation :=
  Ctxt.Valuation.ofHVector args.reverse ++ A

theorem run3 (A : agave_batch_8.cfgCtx.Valuation)
    (args : HVector TyDenote.toType (agave_batch_8.cfgSigs[3]'(by decide)))
    (s : GlobalState)
    (p : Pointer) (word off : BitVec 64) (row : Vector (BitVec 32) 8)
    (hp : (input3 A args) ⟨57, rfl⟩ = PoisonOr.value p)
    (hi : (input3 A args) ⟨0, rfl⟩ = PoisonOr.value word)
    (ho : (input3 A args) ⟨21, rfl⟩ = PoisonOr.value off)
    (hl : (input3 A args) ⟨85, rfl⟩ = PoisonOr.value 995#64)
    (hb : off.toNat ≤ 960)
    (hf : Fits s.mem (rowPtr p word) 256)
    (hr : readWord? (rowPtr p word) 256 s.mem = some (packBits row))
 :
    StateT.run (agave_batch_8.blocks.run A ⟨3, rfl, args⟩) s =
      StateT.run (agave_batch_8.blocks.run A (next3 (input3 A args) row)) s := by
  denote_enter_block
  apply block3_continue (input3 A args) s p word off row hp hi ho hl hb hf hr

structure Ready3 (V : Input3.Valuation) (s : GlobalState) (row : Vector (BitVec 32) 8) where
  p : Pointer
  word : BitVec 64
  off : BitVec 64
  pointer : V ⟨57, rfl⟩ = PoisonOr.value p
  index : V ⟨0, rfl⟩ = PoisonOr.value word
  offset : V ⟨21, rfl⟩ = PoisonOr.value off
  limit : V ⟨85, rfl⟩ = PoisonOr.value 995#64
  bound : off.toNat ≤ 960
  fits : Fits s.mem (rowPtr p word) 256
  read : readWord? (rowPtr p word) 256 s.mem = some (packBits row)

noncomputable def input4 (A : agave_batch_8.cfgCtx.Valuation)
    (args : HVector TyDenote.toType (agave_batch_8.cfgSigs[4]'(by decide))) : Input4.Valuation :=
  Ctxt.Valuation.ofHVector args.reverse ++ A

theorem run4 (A : agave_batch_8.cfgCtx.Valuation)
    (args : HVector TyDenote.toType (agave_batch_8.cfgSigs[4]'(by decide)))
    (s : GlobalState)
    (p : Pointer) (word off : BitVec 64) (row : Vector (BitVec 32) 8)
    (hp : (input4 A args) ⟨55, rfl⟩ = PoisonOr.value p)
    (hi : (input4 A args) ⟨0, rfl⟩ = PoisonOr.value word)
    (ho : (input4 A args) ⟨20, rfl⟩ = PoisonOr.value off)
    (hl : (input4 A args) ⟨84, rfl⟩ = PoisonOr.value 995#64)
    (hb : off.toNat ≤ 960)
    (hf : Fits s.mem (rowPtr p word) 256)
    (hr : readWord? (rowPtr p word) 256 s.mem = some (packBits row))
 :
    StateT.run (agave_batch_8.blocks.run A ⟨4, rfl, args⟩) s =
      StateT.run (agave_batch_8.blocks.run A (next4 (input4 A args) row)) s := by
  denote_enter_block
  apply block4_continue (input4 A args) s p word off row hp hi ho hl hb hf hr

structure Ready4 (V : Input4.Valuation) (s : GlobalState) (row : Vector (BitVec 32) 8) where
  p : Pointer
  word : BitVec 64
  off : BitVec 64
  pointer : V ⟨55, rfl⟩ = PoisonOr.value p
  index : V ⟨0, rfl⟩ = PoisonOr.value word
  offset : V ⟨20, rfl⟩ = PoisonOr.value off
  limit : V ⟨84, rfl⟩ = PoisonOr.value 995#64
  bound : off.toNat ≤ 960
  fits : Fits s.mem (rowPtr p word) 256
  read : readWord? (rowPtr p word) 256 s.mem = some (packBits row)

noncomputable def input5 (A : agave_batch_8.cfgCtx.Valuation)
    (args : HVector TyDenote.toType (agave_batch_8.cfgSigs[5]'(by decide))) : Input5.Valuation :=
  Ctxt.Valuation.ofHVector args.reverse ++ A

theorem run5 (A : agave_batch_8.cfgCtx.Valuation)
    (args : HVector TyDenote.toType (agave_batch_8.cfgSigs[5]'(by decide)))
    (s : GlobalState)
    (p : Pointer) (word off : BitVec 64) (row : Vector (BitVec 32) 8)
    (hp : (input5 A args) ⟨53, rfl⟩ = PoisonOr.value p)
    (hi : (input5 A args) ⟨0, rfl⟩ = PoisonOr.value word)
    (ho : (input5 A args) ⟨19, rfl⟩ = PoisonOr.value off)
    (hl : (input5 A args) ⟨83, rfl⟩ = PoisonOr.value 995#64)
    (hb : off.toNat ≤ 960)
    (hf : Fits s.mem (rowPtr p word) 256)
    (hr : readWord? (rowPtr p word) 256 s.mem = some (packBits row))
 :
    StateT.run (agave_batch_8.blocks.run A ⟨5, rfl, args⟩) s =
      StateT.run (agave_batch_8.blocks.run A (next5 (input5 A args) row)) s := by
  denote_enter_block
  apply block5_continue (input5 A args) s p word off row hp hi ho hl hb hf hr

structure Ready5 (V : Input5.Valuation) (s : GlobalState) (row : Vector (BitVec 32) 8) where
  p : Pointer
  word : BitVec 64
  off : BitVec 64
  pointer : V ⟨53, rfl⟩ = PoisonOr.value p
  index : V ⟨0, rfl⟩ = PoisonOr.value word
  offset : V ⟨19, rfl⟩ = PoisonOr.value off
  limit : V ⟨83, rfl⟩ = PoisonOr.value 995#64
  bound : off.toNat ≤ 960
  fits : Fits s.mem (rowPtr p word) 256
  read : readWord? (rowPtr p word) 256 s.mem = some (packBits row)

noncomputable def input6 (A : agave_batch_8.cfgCtx.Valuation)
    (args : HVector TyDenote.toType (agave_batch_8.cfgSigs[6]'(by decide))) : Input6.Valuation :=
  Ctxt.Valuation.ofHVector args.reverse ++ A

theorem run6 (A : agave_batch_8.cfgCtx.Valuation)
    (args : HVector TyDenote.toType (agave_batch_8.cfgSigs[6]'(by decide)))
    (s : GlobalState)
    (p : Pointer) (word off : BitVec 64) (row : Vector (BitVec 32) 8)
    (hp : (input6 A args) ⟨51, rfl⟩ = PoisonOr.value p)
    (hi : (input6 A args) ⟨0, rfl⟩ = PoisonOr.value word)
    (ho : (input6 A args) ⟨18, rfl⟩ = PoisonOr.value off)
    (hl : (input6 A args) ⟨82, rfl⟩ = PoisonOr.value 995#64)
    (hb : off.toNat ≤ 960)
    (hf : Fits s.mem (rowPtr p word) 256)
    (hr : readWord? (rowPtr p word) 256 s.mem = some (packBits row))
 :
    StateT.run (agave_batch_8.blocks.run A ⟨6, rfl, args⟩) s =
      StateT.run (agave_batch_8.blocks.run A (next6 (input6 A args) row)) s := by
  denote_enter_block
  apply block6_continue (input6 A args) s p word off row hp hi ho hl hb hf hr

structure Ready6 (V : Input6.Valuation) (s : GlobalState) (row : Vector (BitVec 32) 8) where
  p : Pointer
  word : BitVec 64
  off : BitVec 64
  pointer : V ⟨51, rfl⟩ = PoisonOr.value p
  index : V ⟨0, rfl⟩ = PoisonOr.value word
  offset : V ⟨18, rfl⟩ = PoisonOr.value off
  limit : V ⟨82, rfl⟩ = PoisonOr.value 995#64
  bound : off.toNat ≤ 960
  fits : Fits s.mem (rowPtr p word) 256
  read : readWord? (rowPtr p word) 256 s.mem = some (packBits row)

noncomputable def input7 (A : agave_batch_8.cfgCtx.Valuation)
    (args : HVector TyDenote.toType (agave_batch_8.cfgSigs[7]'(by decide))) : Input7.Valuation :=
  Ctxt.Valuation.ofHVector args.reverse ++ A

theorem run7 (A : agave_batch_8.cfgCtx.Valuation)
    (args : HVector TyDenote.toType (agave_batch_8.cfgSigs[7]'(by decide)))
    (s : GlobalState)
    (p : Pointer) (word off : BitVec 64) (row : Vector (BitVec 32) 8)
    (hp : (input7 A args) ⟨49, rfl⟩ = PoisonOr.value p)
    (hi : (input7 A args) ⟨0, rfl⟩ = PoisonOr.value word)
    (ho : (input7 A args) ⟨17, rfl⟩ = PoisonOr.value off)
    (hl : (input7 A args) ⟨81, rfl⟩ = PoisonOr.value 995#64)
    (hb : off.toNat ≤ 960)
    (hf : Fits s.mem (rowPtr p word) 256)
    (hr : readWord? (rowPtr p word) 256 s.mem = some (packBits row))
 :
    StateT.run (agave_batch_8.blocks.run A ⟨7, rfl, args⟩) s =
      StateT.run (agave_batch_8.blocks.run A (next7 (input7 A args) row)) s := by
  denote_enter_block
  apply block7_continue (input7 A args) s p word off row hp hi ho hl hb hf hr

structure Ready7 (V : Input7.Valuation) (s : GlobalState) (row : Vector (BitVec 32) 8) where
  p : Pointer
  word : BitVec 64
  off : BitVec 64
  pointer : V ⟨49, rfl⟩ = PoisonOr.value p
  index : V ⟨0, rfl⟩ = PoisonOr.value word
  offset : V ⟨17, rfl⟩ = PoisonOr.value off
  limit : V ⟨81, rfl⟩ = PoisonOr.value 995#64
  bound : off.toNat ≤ 960
  fits : Fits s.mem (rowPtr p word) 256
  read : readWord? (rowPtr p word) 256 s.mem = some (packBits row)

noncomputable def input8 (A : agave_batch_8.cfgCtx.Valuation)
    (args : HVector TyDenote.toType (agave_batch_8.cfgSigs[8]'(by decide))) : Input8.Valuation :=
  Ctxt.Valuation.ofHVector args.reverse ++ A

theorem run8 (A : agave_batch_8.cfgCtx.Valuation)
    (args : HVector TyDenote.toType (agave_batch_8.cfgSigs[8]'(by decide)))
    (s : GlobalState)
    (off : BitVec 64)
    (ho : (input8 A args) ⟨16, rfl⟩ = PoisonOr.value off)
    (hl : (input8 A args) ⟨80, rfl⟩ = PoisonOr.value 995#64)
    (hb : off.toNat ≤ 960)
 :
    StateT.run (agave_batch_8.blocks.run A ⟨8, rfl, args⟩) s =
      StateT.run (agave_batch_8.blocks.run A (next8 (input8 A args))) s := by
  denote_enter_block
  apply block8_continue (input8 A args) s off ho hl hb

noncomputable def args3 (A : agave_batch_8.cfgCtx.Valuation)
    (args : HVector TyDenote.toType (agave_batch_8.cfgSigs[2]'(by decide)))
    (rows : Fin 6 → Vector (BitVec 32) 8) :
    HVector TyDenote.toType (agave_batch_8.cfgSigs[3]'(by decide)) :=
  (next2 (input2 A args) (rows 0)).args

noncomputable def args4 (A : agave_batch_8.cfgCtx.Valuation)
    (args : HVector TyDenote.toType (agave_batch_8.cfgSigs[2]'(by decide)))
    (rows : Fin 6 → Vector (BitVec 32) 8) :
    HVector TyDenote.toType (agave_batch_8.cfgSigs[4]'(by decide)) :=
  (next3 (input3 A (args3 A args rows)) (rows 1)).args

noncomputable def args5 (A : agave_batch_8.cfgCtx.Valuation)
    (args : HVector TyDenote.toType (agave_batch_8.cfgSigs[2]'(by decide)))
    (rows : Fin 6 → Vector (BitVec 32) 8) :
    HVector TyDenote.toType (agave_batch_8.cfgSigs[5]'(by decide)) :=
  (next4 (input4 A (args4 A args rows)) (rows 2)).args

noncomputable def args6 (A : agave_batch_8.cfgCtx.Valuation)
    (args : HVector TyDenote.toType (agave_batch_8.cfgSigs[2]'(by decide)))
    (rows : Fin 6 → Vector (BitVec 32) 8) :
    HVector TyDenote.toType (agave_batch_8.cfgSigs[6]'(by decide)) :=
  (next5 (input5 A (args5 A args rows)) (rows 3)).args

noncomputable def args7 (A : agave_batch_8.cfgCtx.Valuation)
    (args : HVector TyDenote.toType (agave_batch_8.cfgSigs[2]'(by decide)))
    (rows : Fin 6 → Vector (BitVec 32) 8) :
    HVector TyDenote.toType (agave_batch_8.cfgSigs[7]'(by decide)) :=
  (next6 (input6 A (args6 A args rows)) (rows 4)).args

noncomputable def args8 (A : agave_batch_8.cfgCtx.Valuation)
    (args : HVector TyDenote.toType (agave_batch_8.cfgSigs[2]'(by decide)))
    (rows : Fin 6 → Vector (BitVec 32) 8) :
    HVector TyDenote.toType (agave_batch_8.cfgSigs[8]'(by decide)) :=
  (next7 (input7 A (args7 A args rows)) (rows 5)).args

theorem six_run (A : agave_batch_8.cfgCtx.Valuation)
    (args : HVector TyDenote.toType (agave_batch_8.cfgSigs[2]'(by decide)))
    (rows : Fin 6 → Vector (BitVec 32) 8) (s : GlobalState)
    (h2 : Ready2 (input2 A args) s (rows 0))
    (h3 : Ready3 (input3 A (args3 A args rows)) s (rows 1))
    (h4 : Ready4 (input4 A (args4 A args rows)) s (rows 2))
    (h5 : Ready5 (input5 A (args5 A args rows)) s (rows 3))
    (h6 : Ready6 (input6 A (args6 A args rows)) s (rows 4))
    (h7 : Ready7 (input7 A (args7 A args rows)) s (rows 5))
    : StateT.run (agave_batch_8.blocks.run A ⟨2, rfl, args⟩) s =
      StateT.run (agave_batch_8.blocks.run A ⟨8, rfl, args8 A args rows⟩) s := by
  calc
    _ = StateT.run (agave_batch_8.blocks.run A ⟨3, rfl, args3 A args rows⟩) s := by
      apply run2 A args s h2.p h2.word h2.off (rows 0)
      · exact h2.pointer
      · exact h2.index
      · exact h2.offset
      · exact h2.limit
      · exact h2.bound
      · exact h2.fits
      · exact h2.read
    _ = StateT.run (agave_batch_8.blocks.run A ⟨4, rfl, args4 A args rows⟩) s := by
      apply run3 A (args3 A args rows) s h3.p h3.word h3.off (rows 1)
      · exact h3.pointer
      · exact h3.index
      · exact h3.offset
      · exact h3.limit
      · exact h3.bound
      · exact h3.fits
      · exact h3.read
    _ = StateT.run (agave_batch_8.blocks.run A ⟨5, rfl, args5 A args rows⟩) s := by
      apply run4 A (args4 A args rows) s h4.p h4.word h4.off (rows 2)
      · exact h4.pointer
      · exact h4.index
      · exact h4.offset
      · exact h4.limit
      · exact h4.bound
      · exact h4.fits
      · exact h4.read
    _ = StateT.run (agave_batch_8.blocks.run A ⟨6, rfl, args6 A args rows⟩) s := by
      apply run5 A (args5 A args rows) s h5.p h5.word h5.off (rows 3)
      · exact h5.pointer
      · exact h5.index
      · exact h5.offset
      · exact h5.limit
      · exact h5.bound
      · exact h5.fits
      · exact h5.read
    _ = StateT.run (agave_batch_8.blocks.run A ⟨7, rfl, args7 A args rows⟩) s := by
      apply run6 A (args6 A args rows) s h6.p h6.word h6.off (rows 4)
      · exact h6.pointer
      · exact h6.index
      · exact h6.offset
      · exact h6.limit
      · exact h6.bound
      · exact h6.fits
      · exact h6.read
    _ = StateT.run (agave_batch_8.blocks.run A ⟨8, rfl, args8 A args rows⟩) s := by
      apply run7 A (args7 A args rows) s h7.p h7.word h7.off (rows 5)
      · exact h7.pointer
      · exact h7.index
      · exact h7.offset
      · exact h7.limit
      · exact h7.bound
      · exact h7.fits
      · exact h7.read

end AgaveLatticeHash.MLIR.BatchSecondLoadPath
