/- Released under Apache 2.0 license as described in the file LICENSE. -/
import SSA.Projects.Agave.LatticeHash.MLIR.BatchProof

namespace AgaveLatticeHash.MLIR.BatchHeader
open LeanMLIR SLLVM
open InstCombine (LLVM)

private abbrev blockOutput {Γ Γout : Ctxt SLLVM.Ty} {rets sigs}
    (_ : BlockCom Γ Γout rets sigs) := Γout

abbrev outputTypes8 : List SLLVM.Ty :=
  [SLLVM.Ty.bitvec 1,
   SLLVM.Ty.bitvec 64,
   SLLVM.Ty.bitvec 64,
   SLLVM.Ty.bitvec 64,
   SLLVM.Ty.bitvec 64,
   SLLVM.Ty.bitvec 64,
   SLLVM.Ty.bitvec 64,
   SLLVM.Ty.bitvec 64,
   SLLVM.Ty.bitvec 64,
   SLLVM.Ty.bitvec 64,
   SLLVM.Ty.bitvec 64,
   SLLVM.Ty.bitvec 64,
   SLLVM.Ty.bitvec 64,
   SLLVM.Ty.bitvec 64,
   SLLVM.Ty.bitvec 64,
   SLLVM.Ty.bitvec 64,
   SLLVM.Ty.bitvec 64,
   SLLVM.Ty.arith (.vector 8 (.bitvec 32)),
   SLLVM.Ty.arith (.vector 8 (.bitvec 64)),
   SLLVM.Ty.arith (.vector 8 (.bitvec 64)),
   SLLVM.Ty.arith (.vector 8 (.bitvec 32)),
   SLLVM.Ty.arith (.vector 8 (.bitvec 32)),
   SLLVM.Ty.arith (.vector 8 (.bitvec 32)),
   SLLVM.Ty.arith (.vector 8 (.bitvec 1)),
   SLLVM.Ty.arith (.vector 8 (.bitvec 1)),
   SLLVM.Ty.arith (.vector 8 (.bitvec 1)),
   SLLVM.Ty.arith (.vector 8 (.bitvec 64))]

abbrev Output8 := Ctxt.ofList outputTypes8 ++ Header8Ctx

/-- The SSA values computed by the emitted loop header, retaining poison and
all instruction flags. This is a block contract, not a replacement batch algorithm. -/
noncomputable def values8 (V : Header8Ctx.Valuation) :
    Output8.Valuation :=
  let offsets : Vector (LLVM.IntW 64) 8 := V ⟨0, rfl⟩
  let step : Vector (LLVM.IntW 64) 8 := V ⟨72, rfl⟩
  let lengths : Vector (LLVM.IntW 64) 8 := V ⟨24, rfl⟩
  let v0 := Vector.ofFn fun i : Fin 8 => LLVM.add offsets[i] step[i]
  let v1 := vicmp .ugt lengths v0
  let v2 := vfreeze v1
  let v3 := vicmp .eq offsets (V ⟨73, rfl⟩)
  let v4 := vselect v2 (V ⟨70, rfl⟩) (V ⟨69, rfl⟩)
  let v5 := vzext 32 v3
  let v6 := Vector.ofFn fun i : Fin 8 => LLVM.or v4[i] v5[i] {«disjoint» := true}
  let v7 := Vector.ofFn fun i : Fin 8 => LLVM.sub lengths[i] offsets[i]
  let v8 := vumin v7 step
  let v9 := vtrunc 32 v8 {nsw := true, nuw := true}
  let v10 := LLVM.Ty.extractelement (l := 8) (e := .bitvec 64) offsets (V ⟨74, rfl⟩)
  let v11 := LLVM.lshr v10 (V ⟨68, rfl⟩)
  let v12 := LLVM.Ty.extractelement (l := 8) (e := .bitvec 64) offsets (V ⟨67, rfl⟩)
  let v13 := LLVM.lshr v12 (V ⟨68, rfl⟩)
  let v14 := LLVM.Ty.extractelement (l := 8) (e := .bitvec 64) offsets (V ⟨68, rfl⟩)
  let v15 := LLVM.lshr v14 (V ⟨68, rfl⟩)
  let v16 := LLVM.Ty.extractelement (l := 8) (e := .bitvec 64) offsets (V ⟨66, rfl⟩)
  let v17 := LLVM.lshr v16 (V ⟨68, rfl⟩)
  let v18 := LLVM.Ty.extractelement (l := 8) (e := .bitvec 64) offsets (V ⟨65, rfl⟩)
  let v19 := LLVM.lshr v18 (V ⟨68, rfl⟩)
  let v20 := LLVM.Ty.extractelement (l := 8) (e := .bitvec 64) offsets (V ⟨64, rfl⟩)
  let v21 := LLVM.lshr v20 (V ⟨68, rfl⟩)
  let v22 := LLVM.Ty.extractelement (l := 8) (e := .bitvec 64) offsets (V ⟨63, rfl⟩)
  let v23 := LLVM.lshr v22 (V ⟨68, rfl⟩)
  let v24 := LLVM.Ty.extractelement (l := 8) (e := .bitvec 64) offsets (V ⟨62, rfl⟩)
  let v25 := LLVM.lshr v24 (V ⟨68, rfl⟩)
  Ctxt.Valuation.ofHVector (types := outputTypes8) (PoisonOr.value 0#1 ::ₕ v25 ::ₕ v24 ::ₕ v23 ::ₕ v22 ::ₕ v21 ::ₕ v20 ::ₕ v19 ::ₕ v18 ::ₕ v17 ::ₕ v16 ::ₕ v15 ::ₕ v14 ::ₕ v13 ::ₕ v12 ::ₕ v11 ::ₕ v10 ::ₕ v9 ::ₕ v8 ::ₕ v7 ::ₕ v6 ::ₕ v5 ::ₕ v4 ::ₕ v3 ::ₕ v2 ::ₕ v1 ::ₕ v0 ::ₕ .nil) ++ V

noncomputable def next8 (V : Header8Ctx.Valuation) : SuccArgs agave_batch_8.cfgSigs :=
  let W := values8 V
  ⟨10, rfl, W ⟨35, rfl⟩ ::ₕ
    W ⟨34, rfl⟩ ::ₕ
    W ⟨33, rfl⟩ ::ₕ
    W ⟨32, rfl⟩ ::ₕ
    W ⟨31, rfl⟩ ::ₕ
    W ⟨30, rfl⟩ ::ₕ
    W ⟨29, rfl⟩ ::ₕ
    W ⟨28, rfl⟩ ::ₕ
    W ⟨27, rfl⟩ ::ₕ
    W ⟨26, rfl⟩ ::ₕ
    W ⟨24, rfl⟩ ::ₕ
    W ⟨20, rfl⟩ ::ₕ
    W ⟨17, rfl⟩ ::ₕ
    W ⟨16, rfl⟩ ::ₕ
    W ⟨15, rfl⟩ ::ₕ
    W ⟨14, rfl⟩ ::ₕ
    W ⟨13, rfl⟩ ::ₕ
    W ⟨12, rfl⟩ ::ₕ
    W ⟨11, rfl⟩ ::ₕ
    W ⟨10, rfl⟩ ::ₕ
    W ⟨9, rfl⟩ ::ₕ
    W ⟨8, rfl⟩ ::ₕ
    W ⟨7, rfl⟩ ::ₕ
    W ⟨6, rfl⟩ ::ₕ
    W ⟨5, rfl⟩ ::ₕ
    W ⟨4, rfl⟩ ::ₕ
    W ⟨3, rfl⟩ ::ₕ
    W ⟨2, rfl⟩ ::ₕ
    W ⟨1, rfl⟩ ::ₕ .nil⟩

/-- Execute the actual header and forward its complete typed payload. -/
theorem continue8 {α : Type} (V : Header8Ctx.Valuation) (s : GlobalState)
    (off : BitVec 64)
    (hz : V ⟨74, rfl⟩ = PoisonOr.value 0#64)
    (hl : V ⟨61, rfl⟩ = PoisonOr.value 1027#64)
    (ho : (show Vector (LLVM.IntW 64) 8 from V ⟨0, rfl⟩)[0] = PoisonOr.value off)
    (hb : off.toNat ≤ 960)
    (k : (blockOutput agave_batch_8.cfgBlock_0).Valuation ×
      (HVector TyDenote.toType ([] : List SLLVM.Ty) ⊕ SuccArgs agave_batch_8.cfgSigs) → EffectM α) :
    StateT.run (agave_batch_8.cfgBlock_0.denote V >>= k) s =
      StateT.run (k (values8 V, .inr (next8 V))) s := by
  denote_step_all v
  simp only [BlockCom.run_bind_denote_lifetime]
  denote_step_all v
  denote_eval v 0 26
  have e10 : v10 = PoisonOr.value off := by
    change v10 = LLVM.Ty.extractelement (l := 8) (e := .bitvec 64)
      (V ⟨0, rfl⟩) (V ⟨74, rfl⟩) at hv10
    rw [hz] at hv10
    change v10 = (show Vector (LLVM.IntW 64) 8 from V ⟨0, rfl⟩)[0] at hv10
    exact hv10.trans ho
  have e26 : v26 = PoisonOr.value 0#1 := by
    rw [hv26, e10, hl]
    have hn : ¬1027 < off.toNat := by omega
    simp [LLVM.icmp, LLVM.icmp?, LLVM.icmp', BitVec.ult, hn]
  subst e26
  clear hv26
  simp only [BlockCom.denote, Terminator.denote, Target.denote]
  clear e10
  subst_vars
  simp only [next8, values8, Ctxt.Valuation.ofHVector_cons, Ctxt.Valuation.ofHVector_nil,
    Ctxt.Valuation.cons_append, Ctxt.Valuation.nil_append]
  rfl

/-- The frozen mask in the actual header agrees with scalar lane activity. -/
theorem active_lane (s : GlobalState) (src len out sched panic : Pointer)
    (ms : Fin 8 → AgaveConcrete.Message) (iteration : Nat) (lane : Fin 8)
    (hms : ∀ i, (ms i).length ≤ 1024) :
    (show Vector (LLVM.IntW 1) 8 from
      values8 (headerAt8Val (BatchEntry.entryVal8 s src len out sched panic
        (Vector.ofFn fun i => BitVec.ofNat 64 (ms i).length)) ms iteration) ⟨24, rfl⟩)[lane.val] =
      PoisonOr.value (BitVec.ofBool (decide (iteration < AgaveBatchControl.rootIndex (ms lane).length))) := by
  let W := headerAt8Val (BatchEntry.entryVal8 s src len out sched panic
    (Vector.ofFn fun i => BitVec.ofNat 64 (ms i).length)) ms iteration
  have h0 : W ⟨0, rfl⟩ = (Vector.ofFn fun i : Fin 8 =>
      BitVec.ofNat 64 (batchOffset (ms i).length iteration)).map PoisonOr.value := by rfl
  have h24 : W ⟨24, rfl⟩ = (Vector.ofFn fun i : Fin 8 =>
      BitVec.ofNat 64 (ms i).length).map PoisonOr.value := by rfl
  have h72 : W ⟨72, rfl⟩ = LLVM.Ty.dense (.vector 8 (.bitvec 64)) [64] := by rfl
  change (show Vector (LLVM.IntW 1) 8 from values8 W ⟨24, rfl⟩)[lane.val] = _
  simp only [values8, Ctxt.Valuation.ofHVector_cons, Ctxt.Valuation.ofHVector_nil,
    Ctxt.Valuation.cons_append, Ctxt.Valuation.nil_append]
  simp only [Ctxt.Valuation.cons_succ, Ctxt.Valuation.cons_zero]
  simp only [h0, h24, h72, vfreeze, vicmp, Fin.getElem_fin, Vector.getElem_map, Vector.getElem_ofFn]
  simp only [LLVM.Ty.dense, Vector.getElem_ofFn]
  change LLVM.freeze (LLVM.icmp .ugt (.value (BitVec.ofNat 64 (ms lane).length))
    (LLVM.add (.value (BitVec.ofNat 64 (batchOffset (ms lane).length iteration))) (.value 64#64))) = _
  have hadd : LLVM.add (.value (BitVec.ofNat 64 (batchOffset (ms lane).length iteration)))
      (.value 64#64) = .value (BitVec.ofNat 64 (batchOffset (ms lane).length iteration + 64)) := by
    simp [LLVM.add, LLVM.add?, BitVec.ofNat_add]
  rw [hadd, batchOffset_llvm_active _ _ (hms lane)]
  rfl

/-- One transition of the actual batch CFG from its represented scalar-loop
header to the first source load. The global ambient valuation is unchanged. -/
theorem run8 (s u : GlobalState) (src len out sched panic : Pointer)
    (lengths : Vector (BitVec 64) 8)
    (ms : Fin 8 → AgaveConcrete.Message) (iteration : Nat)
    (hms : ∀ lane, (ms lane).length ≤ 1024) :
    StateT.run (agave_batch_8.blocks.run
      (BatchEntry.entryVal8 s src len out sched panic lengths) (headerAt8 ms iteration)) u =
    StateT.run (agave_batch_8.blocks.run
      (BatchEntry.entryVal8 s src len out sched panic lengths)
      (next8 (headerAt8Val (BatchEntry.entryVal8 s src len out sched panic lengths) ms iteration))) u := by
  denote_enter_block
  apply continue8 _ u (BitVec.ofNat 64 (batchOffset (ms 0).length iteration))
  · rfl
  · rfl
  · change ((Vector.ofFn fun lane : Fin 8 =>
      BitVec.ofNat 64 (batchOffset (ms lane).length iteration)).map PoisonOr.value)[0] = _
    simp
  · simp only [BitVec.toNat_ofNat]
    exact Nat.le_trans (Nat.mod_le ..) (batchOffset_le_960 _ _ (hms 0))

end AgaveLatticeHash.MLIR.BatchHeader
