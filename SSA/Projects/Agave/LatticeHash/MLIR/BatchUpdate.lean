/- Released under Apache 2.0 license as described in the file LICENSE. -/
import SSA.Projects.Agave.LatticeHash.MLIR.BatchProof
import SSA.Projects.Agave.LatticeHash.MLIR.ByteSelect
import SSA.Projects.Firedancer.MLIR.DenoteStep

namespace AgaveLatticeHash.MLIR.BatchUpdate
open LeanMLIR SLLVM Firedancer
open InstCombine (LLVM)
private abbrev blockInput {Γ Γout : Ctxt SLLVM.Ty} {rets sigs}
    (_ : BlockCom Γ Γout rets sigs) := Γ
private abbrev blockOutput {Γ Γout : Ctxt SLLVM.Ty} {rets sigs}
    (_ : BlockCom Γ Γout rets sigs) := Γout
abbrev Input8 := blockInput agave_batch_8.cfgBlock_21
abbrev UpdateTypes8 : List SLLVM.Ty := [
    SLLVM.Ty.arith (.vector 8 (.bitvec (.concrete 64))),
    SLLVM.Ty.arith (.vector 4 (.bitvec (.concrete 64))),
    SLLVM.Ty.arith (.vector 32 (.bitvec (.concrete 8))),
    SLLVM.Ty.arith (.vector 32 (.bitvec (.concrete 8))),
    SLLVM.Ty.arith (.vector 32 (.bitvec (.concrete 8))),
    SLLVM.Ty.arith (.vector 8 (.bitvec (.concrete 32))),
    SLLVM.Ty.arith (.vector 4 (.bitvec (.concrete 64))),
    SLLVM.Ty.arith (.vector 32 (.bitvec (.concrete 8))),
    SLLVM.Ty.arith (.vector 32 (.bitvec (.concrete 8))),
    SLLVM.Ty.arith (.vector 32 (.bitvec (.concrete 8))),
    SLLVM.Ty.arith (.vector 8 (.bitvec (.concrete 32))),
    SLLVM.Ty.arith (.vector 4 (.bitvec (.concrete 64))),
    SLLVM.Ty.arith (.vector 32 (.bitvec (.concrete 8))),
    SLLVM.Ty.arith (.vector 32 (.bitvec (.concrete 8))),
    SLLVM.Ty.arith (.vector 32 (.bitvec (.concrete 8))),
    SLLVM.Ty.arith (.vector 8 (.bitvec (.concrete 32))),
    SLLVM.Ty.arith (.vector 4 (.bitvec (.concrete 64))),
    SLLVM.Ty.arith (.vector 32 (.bitvec (.concrete 8))),
    SLLVM.Ty.arith (.vector 32 (.bitvec (.concrete 8))),
    SLLVM.Ty.arith (.vector 32 (.bitvec (.concrete 8))),
    SLLVM.Ty.arith (.vector 8 (.bitvec (.concrete 32))),
    SLLVM.Ty.arith (.vector 4 (.bitvec (.concrete 64))),
    SLLVM.Ty.arith (.vector 32 (.bitvec (.concrete 8))),
    SLLVM.Ty.arith (.vector 32 (.bitvec (.concrete 8))),
    SLLVM.Ty.arith (.vector 32 (.bitvec (.concrete 8))),
    SLLVM.Ty.arith (.vector 8 (.bitvec (.concrete 32))),
    SLLVM.Ty.arith (.vector 4 (.bitvec (.concrete 64))),
    SLLVM.Ty.arith (.vector 32 (.bitvec (.concrete 8))),
    SLLVM.Ty.arith (.vector 32 (.bitvec (.concrete 8))),
    SLLVM.Ty.arith (.vector 32 (.bitvec (.concrete 8))),
    SLLVM.Ty.arith (.vector 8 (.bitvec (.concrete 32))),
    SLLVM.Ty.arith (.vector 4 (.bitvec (.concrete 64))),
    SLLVM.Ty.arith (.vector 32 (.bitvec (.concrete 8))),
    SLLVM.Ty.arith (.vector 32 (.bitvec (.concrete 8))),
    SLLVM.Ty.arith (.vector 32 (.bitvec (.concrete 8))),
    SLLVM.Ty.arith (.vector 8 (.bitvec (.concrete 32))),
    SLLVM.Ty.arith (.vector 4 (.bitvec (.concrete 64))),
    SLLVM.Ty.arith (.vector 32 (.bitvec (.concrete 8))),
    SLLVM.Ty.arith (.vector 32 (.bitvec (.concrete 8))),
    SLLVM.Ty.arith (.vector 32 (.bitvec (.concrete 8))),
    SLLVM.Ty.arith (.vector 8 (.bitvec (.concrete 32))),
    SLLVM.Ty.arith (.vector 32 (.bitvec (.concrete 1))),
    SLLVM.Ty.arith (.vector 32 (.bitvec (.concrete 8))),
    SLLVM.Ty.arith (.vector 8 (.bitvec (.concrete 32)))]
abbrev Output8 := Ctxt.ofList UpdateTypes8 ++ Input8

def xor8 (x y : Vector (LLVM.IntW 32) 8) : Vector (LLVM.IntW 32) 8 :=
  Vector.ofFn fun i => LLVM.xor x[i] y[i]

/-- The exact pure SSA result, preserving poison behavior in all bitcasts,
comparisons and byte selections, of the compiler's CV update block. -/
noncomputable def result8 (V : Input8.Valuation) : Output8.Valuation ×
    (HVector TyDenote.toType ([] : List SLLVM.Ty) ⊕ SuccArgs agave_batch_8.cfgSigs) :=
  let v0 := vsext 32 (V ⟨16, rfl⟩)
  let v1 := bitcast (.vector 8 (.bitvec (.concrete 32))) (.vector 32 (.bitvec (.concrete 8))) v0
  let v2 := vicmp .slt v1 (V ⟨55, rfl⟩)
  let v3 := xor8 (V ⟨5, rfl⟩) (V ⟨15, rfl⟩)
  let v4 := bitcast (.vector 4 (.bitvec (.concrete 64))) (.vector 32 (.bitvec (.concrete 8))) (V ⟨19, rfl⟩)
  let v5 := bitcast (.vector 8 (.bitvec (.concrete 32))) (.vector 32 (.bitvec (.concrete 8))) v3
  let v6 := vselect v2 v5 v4
  let v7 := bitcast (.vector 32 (.bitvec (.concrete 8))) (.vector 4 (.bitvec (.concrete 64))) v6
  let v8 := xor8 (V ⟨1, rfl⟩) (V ⟨11, rfl⟩)
  let v9 := bitcast (.vector 4 (.bitvec (.concrete 64))) (.vector 32 (.bitvec (.concrete 8))) (V ⟨20, rfl⟩)
  let v10 := bitcast (.vector 8 (.bitvec (.concrete 32))) (.vector 32 (.bitvec (.concrete 8))) v8
  let v11 := vselect v2 v10 v9
  let v12 := bitcast (.vector 32 (.bitvec (.concrete 8))) (.vector 4 (.bitvec (.concrete 64))) v11
  let v13 := xor8 (V ⟨13, rfl⟩) (V ⟨7, rfl⟩)
  let v14 := bitcast (.vector 4 (.bitvec (.concrete 64))) (.vector 32 (.bitvec (.concrete 8))) (V ⟨21, rfl⟩)
  let v15 := bitcast (.vector 8 (.bitvec (.concrete 32))) (.vector 32 (.bitvec (.concrete 8))) v13
  let v16 := vselect v2 v15 v14
  let v17 := bitcast (.vector 32 (.bitvec (.concrete 8))) (.vector 4 (.bitvec (.concrete 64))) v16
  let v18 := xor8 (V ⟨9, rfl⟩) (V ⟨3, rfl⟩)
  let v19 := bitcast (.vector 4 (.bitvec (.concrete 64))) (.vector 32 (.bitvec (.concrete 8))) (V ⟨22, rfl⟩)
  let v20 := bitcast (.vector 8 (.bitvec (.concrete 32))) (.vector 32 (.bitvec (.concrete 8))) v18
  let v21 := vselect v2 v20 v19
  let v22 := bitcast (.vector 32 (.bitvec (.concrete 8))) (.vector 4 (.bitvec (.concrete 64))) v21
  let v23 := xor8 (V ⟨10, rfl⟩) (V ⟨0, rfl⟩)
  let v24 := bitcast (.vector 4 (.bitvec (.concrete 64))) (.vector 32 (.bitvec (.concrete 8))) (V ⟨23, rfl⟩)
  let v25 := bitcast (.vector 8 (.bitvec (.concrete 32))) (.vector 32 (.bitvec (.concrete 8))) v23
  let v26 := vselect v2 v25 v24
  let v27 := bitcast (.vector 32 (.bitvec (.concrete 8))) (.vector 4 (.bitvec (.concrete 64))) v26
  let v28 := xor8 (V ⟨6, rfl⟩) (V ⟨12, rfl⟩)
  let v29 := bitcast (.vector 4 (.bitvec (.concrete 64))) (.vector 32 (.bitvec (.concrete 8))) (V ⟨24, rfl⟩)
  let v30 := bitcast (.vector 8 (.bitvec (.concrete 32))) (.vector 32 (.bitvec (.concrete 8))) v28
  let v31 := vselect v2 v30 v29
  let v32 := bitcast (.vector 32 (.bitvec (.concrete 8))) (.vector 4 (.bitvec (.concrete 64))) v31
  let v33 := xor8 (V ⟨2, rfl⟩) (V ⟨8, rfl⟩)
  let v34 := bitcast (.vector 4 (.bitvec (.concrete 64))) (.vector 32 (.bitvec (.concrete 8))) (V ⟨25, rfl⟩)
  let v35 := bitcast (.vector 8 (.bitvec (.concrete 32))) (.vector 32 (.bitvec (.concrete 8))) v33
  let v36 := vselect v2 v35 v34
  let v37 := bitcast (.vector 32 (.bitvec (.concrete 8))) (.vector 4 (.bitvec (.concrete 64))) v36
  let v38 := xor8 (V ⟨14, rfl⟩) (V ⟨4, rfl⟩)
  let v39 := bitcast (.vector 4 (.bitvec (.concrete 64))) (.vector 32 (.bitvec (.concrete 8))) (V ⟨26, rfl⟩)
  let v40 := bitcast (.vector 8 (.bitvec (.concrete 32))) (.vector 32 (.bitvec (.concrete 8))) v38
  let v41 := vselect v2 v40 v39
  let v42 := bitcast (.vector 32 (.bitvec (.concrete 8))) (.vector 4 (.bitvec (.concrete 64))) v41
  let v43 := vselect (V ⟨16, rfl⟩) (V ⟨17, rfl⟩) (V ⟨18, rfl⟩)
  (Ctxt.Valuation.ofHVector (types := UpdateTypes8) (v43 ::ₕ v42 ::ₕ v41 ::ₕ v40 ::ₕ v39 ::ₕ v38 ::ₕ v37 ::ₕ v36 ::ₕ v35 ::ₕ v34 ::ₕ v33 ::ₕ v32 ::ₕ v31 ::ₕ v30 ::ₕ v29 ::ₕ v28 ::ₕ v27 ::ₕ v26 ::ₕ v25 ::ₕ v24 ::ₕ v23 ::ₕ v22 ::ₕ v21 ::ₕ v20 ::ₕ v19 ::ₕ v18 ::ₕ v17 ::ₕ v16 ::ₕ v15 ::ₕ v14 ::ₕ v13 ::ₕ v12 ::ₕ v11 ::ₕ v10 ::ₕ v9 ::ₕ v8 ::ₕ v7 ::ₕ v6 ::ₕ v5 ::ₕ v4 ::ₕ v3 ::ₕ v2 ::ₕ v1 ::ₕ v0 ::ₕ .nil) ++ V,
    .inr ⟨0, rfl, [v42, v37, v32, v27, v22, v17, v12, v7, v43]ₕ⟩)

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 4096 in
/-- Actual compiler-emitted feed-forward and masked update execution. -/
theorem update8_continue {α : Type} (V : Input8.Valuation) (s : GlobalState)
    (k : Output8.Valuation ×
      (HVector TyDenote.toType ([] : List SLLVM.Ty) ⊕ SuccArgs agave_batch_8.cfgSigs) → EffectM α) :
    StateT.run (agave_batch_8.cfgBlock_21.denote V >>= k) s =
      StateT.run (k (result8 V)) s := by
  denote_step_all v
  simp only [BlockCom.run_bind_denote_lifetime]
  denote_eval v 0 43
  subst hv0 hv1 hv2 hv3 hv4 hv5 hv6 hv7 hv8 hv9 hv10 hv11 hv12 hv13 hv14 hv15 hv16 hv17 hv18 hv19 hv20 hv21 hv22 hv23 hv24 hv25 hv26 hv27 hv28 hv29 hv30 hv31 hv32 hv33 hv34 hv35 hv36 hv37 hv38 hv39 hv40 hv41 hv42 hv43
  simp only [BlockCom.denote, Terminator.denote, Target.denote]
  simp only [result8, Ctxt.Valuation.ofHVector_cons, Ctxt.Valuation.ofHVector_nil,
    Ctxt.Valuation.cons_append, Ctxt.Valuation.nil_append, pure_bind]
  simp only [xor8, InstCombine.binaryDenote, Fin.getElem_fin]
  rfl


theorem xor8_values (a b : Fin 8 → BitVec 32) :
    xor8 ((Vector.ofFn a).map PoisonOr.value) ((Vector.ofFn b).map PoisonOr.value) =
      (Vector.ofFn fun i => a i ^^^ b i).map PoisonOr.value := by
  apply Vector.ext
  intro i hi
  simp [xor8, LLVM.xor, Fin.getElem_fin]
  rfl

theorem select_offsets (active : Fin 8 → Bool) (a b : Vector (BitVec 64) 8) :
    vselect (active8 active) (a.map PoisonOr.value) (b.map PoisonOr.value) =
      (Vector.ofFn fun i => if active i then a[i.val] else b[i.val]).map PoisonOr.value := by
  apply Vector.ext
  intro i hi
  simp only [vselect, active8, Vector.getElem_ofFn, Fin.getElem_fin, Vector.getElem_map]
  cases h : active ⟨i, hi⟩ <;> simp [LLVM.select]

open Blake3Compression in
/-- Representation at the emitted feed-forward block. Both input halves of
each XOR are specified independently, so the feed-forward itself is proved. -/
structure Env8 (V : Input8.Valuation) (active : Fin 8 → Bool)
    (old x y : CV (Lanes 8)) (offsets advanced : Vector (BitVec 64) 8) : Prop where
  mask : V ⟨16, rfl⟩ = active8 active
  zero : V ⟨55, rfl⟩ = Vector.replicate 32 (.value 0#8)
  offsets : V ⟨18, rfl⟩ = offsets.map PoisonOr.value
  advanced : V ⟨17, rfl⟩ = advanced.map PoisonOr.value
  old0 : V ⟨19, rfl⟩ = (packCV8 (old 0)).map PoisonOr.value
  x0 : V ⟨5, rfl⟩ = (Vector.ofFn (x 0)).map PoisonOr.value
  y0 : V ⟨15, rfl⟩ = (Vector.ofFn (y 0)).map PoisonOr.value
  old1 : V ⟨20, rfl⟩ = (packCV8 (old 1)).map PoisonOr.value
  x1 : V ⟨1, rfl⟩ = (Vector.ofFn (x 1)).map PoisonOr.value
  y1 : V ⟨11, rfl⟩ = (Vector.ofFn (y 1)).map PoisonOr.value
  old2 : V ⟨21, rfl⟩ = (packCV8 (old 2)).map PoisonOr.value
  x2 : V ⟨13, rfl⟩ = (Vector.ofFn (x 2)).map PoisonOr.value
  y2 : V ⟨7, rfl⟩ = (Vector.ofFn (y 2)).map PoisonOr.value
  old3 : V ⟨22, rfl⟩ = (packCV8 (old 3)).map PoisonOr.value
  x3 : V ⟨9, rfl⟩ = (Vector.ofFn (x 3)).map PoisonOr.value
  y3 : V ⟨3, rfl⟩ = (Vector.ofFn (y 3)).map PoisonOr.value
  old4 : V ⟨23, rfl⟩ = (packCV8 (old 4)).map PoisonOr.value
  x4 : V ⟨10, rfl⟩ = (Vector.ofFn (x 4)).map PoisonOr.value
  y4 : V ⟨0, rfl⟩ = (Vector.ofFn (y 4)).map PoisonOr.value
  old5 : V ⟨24, rfl⟩ = (packCV8 (old 5)).map PoisonOr.value
  x5 : V ⟨6, rfl⟩ = (Vector.ofFn (x 5)).map PoisonOr.value
  y5 : V ⟨12, rfl⟩ = (Vector.ofFn (y 5)).map PoisonOr.value
  old6 : V ⟨25, rfl⟩ = (packCV8 (old 6)).map PoisonOr.value
  x6 : V ⟨2, rfl⟩ = (Vector.ofFn (x 6)).map PoisonOr.value
  y6 : V ⟨8, rfl⟩ = (Vector.ofFn (y 6)).map PoisonOr.value
  old7 : V ⟨26, rfl⟩ = (packCV8 (old 7)).map PoisonOr.value
  x7 : V ⟨14, rfl⟩ = (Vector.ofFn (x 7)).map PoisonOr.value
  y7 : V ⟨4, rfl⟩ = (Vector.ofFn (y 7)).map PoisonOr.value

/-- The actual backedge payload contains lane-wise feed-forward CVs and
updated offsets, preserving every inactive lane. -/
theorem result8_target (V : Input8.Valuation) (active : Fin 8 → Bool)
    (old x y : Blake3Compression.CV (Blake3Compression.Lanes 8))
    (offsets advanced : Vector (BitVec 64) 8) (h : Env8 V active old x y offsets advanced) :
    (result8 V).2 = .inr (headerTarget8
      (fun w lane => if active lane then x w lane ^^^ y w lane else old w lane)
      (Vector.ofFn fun i => if active i then advanced[i.val] else offsets[i.val])) := by
  simp only [result8, h.mask, h.zero, h.offsets, h.advanced,
    h.old0, h.x0, h.y0,
    h.old1, h.x1, h.y1,
    h.old2, h.x2, h.y2,
    h.old3, h.x3, h.y3,
    h.old4, h.x4, h.y4,
    h.old5, h.x5, h.y5,
    h.old6, h.x6, h.y6,
    h.old7, h.x7, h.y7]
  rw [xor8_values (x 0) (y 0)]
  rw [xor8_values (x 1) (y 1)]
  rw [xor8_values (x 2) (y 2)]
  rw [xor8_values (x 3) (y 3)]
  rw [xor8_values (x 4) (y 4)]
  rw [xor8_values (x 5) (y 5)]
  rw [xor8_values (x 6) (y 6)]
  rw [xor8_values (x 7) (y 7)]
  rw [maskedCV_eq active (fun lane => x 0 lane ^^^ y 0 lane) (old 0)]
  rw [maskedCV_eq active (fun lane => x 1 lane ^^^ y 1 lane) (old 1)]
  rw [maskedCV_eq active (fun lane => x 2 lane ^^^ y 2 lane) (old 2)]
  rw [maskedCV_eq active (fun lane => x 3 lane ^^^ y 3 lane) (old 3)]
  rw [maskedCV_eq active (fun lane => x 4 lane ^^^ y 4 lane) (old 4)]
  rw [maskedCV_eq active (fun lane => x 5 lane ^^^ y 5 lane) (old 5)]
  rw [maskedCV_eq active (fun lane => x 6 lane ^^^ y 6 lane) (old 6)]
  rw [maskedCV_eq active (fun lane => x 7 lane ^^^ y 7 lane) (old 7)]
  rw [select_offsets]
  rfl

/-- Raw block denotation, retaining the entire exact SSA output valuation. -/
theorem update8_denote (V : Input8.Valuation) (s : GlobalState) :
    StateT.run (agave_batch_8.cfgBlock_21.denote V) s = .value (result8 V, s) := by
  simpa only [bind_pure, EffectM.run_pure] using update8_continue V s pure

/-- Actual execution reaches the represented lane-wise update, with its
complete SSA output and unchanged memory. -/
theorem update8_refines (V : Input8.Valuation) (s : GlobalState) (active : Fin 8 → Bool)
    (old x y : Blake3Compression.CV (Blake3Compression.Lanes 8))
    (offsets advanced : Vector (BitVec 64) 8) (h : Env8 V active old x y offsets advanced) :
    StateT.run (agave_batch_8.cfgBlock_21.denote V) s =
      .value (((result8 V).1, .inr (headerTarget8
        (fun w lane => if active lane then x w lane ^^^ y w lane else old w lane)
        (Vector.ofFn fun i => if active i then advanced[i.val] else offsets[i.val]))), s) := by
  rw [update8_denote]
  exact congrArg (fun q => PoisonOr.value (q, s))
    (Prod.ext rfl (result8_target V active old x y offsets advanced h))

/-- The masked machine update advances the existing scalar-prefix invariant.
The only compression premise is the primitive's independently proved result
on this iteration's scalar block. -/
theorem headerTarget8_stateAt_next (ms : Fin 8 → AgaveConcrete.Message) (iteration : Nat)
    (fresh : Blake3Compression.CV (Blake3Compression.Lanes 8))
    (hnew : ∀ lane, iteration < AgaveBatchControl.rootIndex (ms lane).length → ∀ w,
      fresh w lane = AgaveConcrete.compress
        (AgaveBatchControl.stateAt AgaveConcrete.compress AgaveConcrete.iv
          (AgaveConcrete.bytes (ms lane)) (ms lane).length iteration).cv
        (AgaveBatchControl.scalarBlock (AgaveConcrete.bytes (ms lane)) (ms lane).length
          (min iteration (AgaveBatchControl.rootIndex (ms lane).length)))
        0 0 64 (if min iteration (AgaveBatchControl.rootIndex (ms lane).length) = 0 then 1 else 0) w) :
    headerTarget8
      (fun w lane => if decide (iteration < AgaveBatchControl.rootIndex (ms lane).length) then
        fresh w lane else
        (AgaveBatchControl.stateAt AgaveConcrete.compress AgaveConcrete.iv
          (AgaveConcrete.bytes (ms lane)) (ms lane).length iteration).cv w)
      (Vector.ofFn fun lane =>
        if decide (iteration < AgaveBatchControl.rootIndex (ms lane).length) then
          BitVec.ofNat 64 (batchOffset (ms lane).length iteration + 64)
        else BitVec.ofNat 64 (batchOffset (ms lane).length iteration)) =
      headerAt8 ms (iteration + 1) := by
  unfold headerAt8
  congr 1
  · funext w lane
    by_cases ha : iteration < AgaveBatchControl.rootIndex (ms lane).length
    · have ht : min iteration (AgaveBatchControl.rootIndex (ms lane).length) = iteration := by omega
      have ht1 : min (iteration+1) (AgaveBatchControl.rootIndex (ms lane).length) = iteration+1 := by omega
      simp only [decide_eq_true_eq, ha, ite_true]
      rw [hnew lane ha w]
      simp only [AgaveBatchControl.stateAt, ht, ht1, AgaveBatchControl.scalarPrefix]
    · have ht : min iteration (AgaveBatchControl.rootIndex (ms lane).length) =
          AgaveBatchControl.rootIndex (ms lane).length := by omega
      have ht1 : min (iteration+1) (AgaveBatchControl.rootIndex (ms lane).length) =
          AgaveBatchControl.rootIndex (ms lane).length := by omega
      simp [ha, AgaveBatchControl.stateAt, ht, ht1]
  · apply Vector.ext
    intro i hi
    simp only [Vector.getElem_ofFn]
    by_cases ha : iteration < AgaveBatchControl.rootIndex (ms ⟨i, hi⟩).length
    · have ht : min iteration (AgaveBatchControl.rootIndex (ms ⟨i, hi⟩).length) = iteration := by omega
      have ht1 : min (iteration+1) (AgaveBatchControl.rootIndex (ms ⟨i, hi⟩).length) = iteration+1 := by omega
      simp [ha, batchOffset, ht, Nat.mul_add]
    · have ht : min iteration (AgaveBatchControl.rootIndex (ms ⟨i, hi⟩).length) =
          AgaveBatchControl.rootIndex (ms ⟨i, hi⟩).length := by omega
      have ht1 : min (iteration+1) (AgaveBatchControl.rootIndex (ms ⟨i, hi⟩).length) =
          AgaveBatchControl.rootIndex (ms ⟨i, hi⟩).length := by omega
      simp [ha, batchOffset, ht, ht1]

def stateCV8 (ms : Fin 8 → AgaveConcrete.Message) (iteration : Nat) :
    Blake3Compression.CV (Blake3Compression.Lanes 8) :=
  fun w lane => (AgaveBatchControl.stateAt AgaveConcrete.compress AgaveConcrete.iv
    (AgaveConcrete.bytes (ms lane)) (ms lane).length iteration).cv w

def activeAt8 (ms : Fin 8 → AgaveConcrete.Message) (iteration : Nat) : Fin 8 → Bool :=
  fun lane => decide (iteration < AgaveBatchControl.rootIndex (ms lane).length)

def offsetsAt8 (ms : Fin 8 → AgaveConcrete.Message) (iteration : Nat) : Vector (BitVec 64) 8 :=
  Vector.ofFn fun lane => BitVec.ofNat 64 (batchOffset (ms lane).length iteration)

def advancedAt8 (ms : Fin 8 → AgaveConcrete.Message) (iteration : Nat) : Vector (BitVec 64) 8 :=
  Vector.ofFn fun lane => BitVec.ofNat 64 (batchOffset (ms lane).length iteration + 64)

/-- Composition-ready actual backedge theorem: the independent compression
contract and the input representation produce the next scalar-prefix state. -/
theorem update8_stateAt (V : Input8.Valuation) (s : GlobalState)
    (ms : Fin 8 → AgaveConcrete.Message) (iteration : Nat)
    (x y : Blake3Compression.CV (Blake3Compression.Lanes 8))
    (henv : Env8 V (activeAt8 ms iteration) (stateCV8 ms iteration) x y
      (offsetsAt8 ms iteration) (advancedAt8 ms iteration))
    (hcompress : ∀ lane, iteration < AgaveBatchControl.rootIndex (ms lane).length → ∀ w,
      x w lane ^^^ y w lane = AgaveConcrete.compress
        (AgaveBatchControl.stateAt AgaveConcrete.compress AgaveConcrete.iv
          (AgaveConcrete.bytes (ms lane)) (ms lane).length iteration).cv
        (AgaveBatchControl.scalarBlock (AgaveConcrete.bytes (ms lane)) (ms lane).length
          (min iteration (AgaveBatchControl.rootIndex (ms lane).length)))
        0 0 64 (if min iteration (AgaveBatchControl.rootIndex (ms lane).length) = 0 then 1 else 0) w) :
    StateT.run (agave_batch_8.cfgBlock_21.denote V) s =
      .value (((result8 V).1, .inr (headerAt8 ms (iteration + 1))), s) := by
  rw [update8_refines V s _ _ x y _ _ henv]
  have ht := headerTarget8_stateAt_next ms iteration (fun w lane => x w lane ^^^ y w lane) hcompress
  have hoff : (Vector.ofFn fun i => if activeAt8 ms iteration i then
      (advancedAt8 ms iteration)[i.val] else (offsetsAt8 ms iteration)[i.val]) =
      (Vector.ofFn fun lane => if decide (iteration < AgaveBatchControl.rootIndex (ms lane).length) then
        BitVec.ofNat 64 (batchOffset (ms lane).length iteration + 64)
        else BitVec.ofNat 64 (batchOffset (ms lane).length iteration)) := by
    apply Vector.ext
    intro i hi
    simp [activeAt8, offsetsAt8, advancedAt8]
  rw [hoff]
  exact congrArg (fun t : SuccArgs agave_batch_8.cfgSigs =>
    PoisonOr.value (((result8 V).1, Sum.inr t), s)) ht

end AgaveLatticeHash.MLIR.BatchUpdate
