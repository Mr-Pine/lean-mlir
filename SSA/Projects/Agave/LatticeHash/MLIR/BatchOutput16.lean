/- Released under Apache 2.0 license as described in the file LICENSE. -/
import SSA.Projects.Agave.LatticeHash.MLIR.BatchCFG16
import SSA.Projects.Agave.LatticeHash.MLIR.BatchReduction16
import SSA.Projects.Agave.LatticeHash.MLIR.BatchXof16
import SSA.Projects.Agave.LatticeHash.MLIR.OutputRead
import SSA.Projects.Firedancer.MLIR.DenoteStep
namespace AgaveLatticeHash.MLIR.BatchOutput16
open LeanMLIR SLLVM Firedancer
open InstCombine (LLVM)
open BatchReduction16
private abbrev blockInput {Γ Γout : Ctxt SLLVM.Ty} {rets sigs}
    (_ : BlockCom Γ Γout rets sigs) := Γ
abbrev Input11 := blockInput agave_batch_16.cfgBlock_11
abbrev HalfTy : LLVM.Ty := .vector 32 (.bitvec (.concrete 16))
def xor16 (x y : Row16) : Row16 := Vector.ofFn fun i => LLVM.xor x[i] y[i]
def delta16 (V : Input11.Valuation) : HalfRow :=
  reduce16
    (xor16 (V ⟨5, rfl⟩) (V ⟨15, rfl⟩))
    (xor16 (V ⟨1, rfl⟩) (V ⟨11, rfl⟩))
    (xor16 (V ⟨13, rfl⟩) (V ⟨7, rfl⟩))
    (xor16 (V ⟨9, rfl⟩) (V ⟨3, rfl⟩))
    (xor16 (V ⟨10, rfl⟩) (V ⟨0, rfl⟩))
    (xor16 (V ⟨6, rfl⟩) (V ⟨12, rfl⟩))
    (xor16 (V ⟨2, rfl⟩) (V ⟨8, rfl⟩))
    (xor16 (V ⟨14, rfl⟩) (V ⟨4, rfl⟩))
    (xor16 (V ⟨19, rfl⟩) (V ⟨5, rfl⟩))
    (xor16 (V ⟨20, rfl⟩) (V ⟨1, rfl⟩))
    (xor16 (V ⟨21, rfl⟩) (V ⟨13, rfl⟩))
    (xor16 (V ⟨22, rfl⟩) (V ⟨9, rfl⟩))
    (xor16 (V ⟨23, rfl⟩) (V ⟨10, rfl⟩))
    (xor16 (V ⟨24, rfl⟩) (V ⟨6, rfl⟩))
    (xor16 (V ⟨25, rfl⟩) (V ⟨2, rfl⟩))
    (xor16 (V ⟨26, rfl⟩) (V ⟨14, rfl⟩))
def next11 (V : Input11.Valuation) (counter : LLVM.IntW 64) : SuccArgs agave_batch_16.cfgSigs :=
  ⟨9, rfl, counter ::ₕ V ⟨26, rfl⟩ ::ₕ V ⟨25, rfl⟩ ::ₕ V ⟨24, rfl⟩ ::ₕ V ⟨23, rfl⟩ ::ₕ V ⟨22, rfl⟩ ::ₕ V ⟨21, rfl⟩ ::ₕ V ⟨20, rfl⟩ ::ₕ V ⟨19, rfl⟩ ::ₕ V ⟨18, rfl⟩ ::ₕ V ⟨17, rfl⟩ ::ₕ .nil⟩
/-- The actual single 64-byte accumulator update and XOF-counter branch. -/
def output16Spec (V : Input11.Valuation) :
    EffectM (HVector TyDenote.toType ([] : List SLLVM.Ty) ⊕ SuccArgs agave_batch_16.cfgSigs) := do
  let offset := LLVM.shl (V ⟨16, rfl⟩) (V ⟨81, rfl⟩) {nsw := true, nuw := true}
  let ptr := gep (V ⟨162, rfl⟩) 1 0 offset
  let old : HalfRow ← liftM (load ptr HalfTy)
  liftM (store ptr HalfTy (addHalves old (delta16 V)))
  let next := LLVM.add (V ⟨16, rfl⟩) (V ⟨110, rfl⟩) {nsw := true, nuw := true}
  match LLVM.icmp .eq next (V ⟨100, rfl⟩) with
  | .poison => throwUB
  | .value b => pure (.inr (if b = 1 then ⟨12, rfl, .nil⟩ else next11 V next))
private theorem hvConsAppend {Γ : Ctxt SLLVM.Ty} {ts : List SLLVM.Ty} {t : SLLVM.Ty}
    (x : TyDenote.toType t) (xs : HVector TyDenote.toType ts) (V : Γ.Valuation) :
    (x ::ₕ xs) ++ V = x ::ᵥ (xs ++ V) := Ctxt.Valuation.cons_append
private theorem hvNilAppend {Γ : Ctxt SLLVM.Ty} (V : Γ.Valuation) :
    (HVector.nil : HVector TyDenote.toType ([] : List SLLVM.Ty)) ++ V = V := rfl
private theorem targetIte {Γ : Ctxt SLLVM.Ty} {sigs} (V : Γ.Valuation)
    (p : Prop) [Decidable p] (a b : Target Γ sigs) :
    (if p then a else b).denote V = if p then a.denote V else b.denote V := by
  split <;> rfl


private theorem denoteOp_store' {Γ : Ctxt SLLVM.Ty} (t : LLVM.Ty)
    (p : Γ.Var .ptr) (x : Γ.Var (.arith t)) (V : Γ.Valuation) :
    Expr.denoteOp
      (Expr.mk (d := SLLVM) (Γ := Γ) (eff := .impure) (SLLVMOp.store t) rfl
        (EffectKind.le_refl _) (p ::ₕ x ::ₕ .nil) Regions.nil) V =
      ((fun _ => HVector.nil) <$> (liftM (store (V p) t (V x))) :
        EffectM (HVector TyDenote.toType ([] : List SLLVM.Ty))) := by rfl

set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
/-- The complete lifted output block, including the emitted SIMD reduction. -/
theorem output16_denote (V : Input11.Valuation) :
    (do let (_, r) ← agave_batch_16.cfgBlock_11.denote V; pure r) = output16Spec V := by
  denote_step_all v
  denote_eval v 0 17
  change v0 = xor16 (V ⟨5, rfl⟩) (V ⟨15, rfl⟩) at hv0
  change v1 = xor16 (V ⟨19, rfl⟩) (V ⟨5, rfl⟩) at hv1
  change v2 = xor16 (V ⟨1, rfl⟩) (V ⟨11, rfl⟩) at hv2
  change v3 = xor16 (V ⟨20, rfl⟩) (V ⟨1, rfl⟩) at hv3
  change v4 = xor16 (V ⟨13, rfl⟩) (V ⟨7, rfl⟩) at hv4
  change v5 = xor16 (V ⟨21, rfl⟩) (V ⟨13, rfl⟩) at hv5
  change v6 = xor16 (V ⟨9, rfl⟩) (V ⟨3, rfl⟩) at hv6
  change v7 = xor16 (V ⟨22, rfl⟩) (V ⟨9, rfl⟩) at hv7
  change v8 = xor16 (V ⟨10, rfl⟩) (V ⟨0, rfl⟩) at hv8
  change v9 = xor16 (V ⟨23, rfl⟩) (V ⟨10, rfl⟩) at hv9
  change v10 = xor16 (V ⟨6, rfl⟩) (V ⟨12, rfl⟩) at hv10
  change v11 = xor16 (V ⟨24, rfl⟩) (V ⟨6, rfl⟩) at hv11
  change v12 = xor16 (V ⟨2, rfl⟩) (V ⟨8, rfl⟩) at hv12
  change v13 = xor16 (V ⟨25, rfl⟩) (V ⟨2, rfl⟩) at hv13
  change v14 = xor16 (V ⟨14, rfl⟩) (V ⟨4, rfl⟩) at hv14
  change v15 = xor16 (V ⟨26, rfl⟩) (V ⟨14, rfl⟩) at hv15
  unfold output16Spec
  simp only [← hv16, ← hv17]
  rw [BlockCom.denote_var]
  simp only [Expr.denote_unfold, denoteOp_load, bind_map_left, bind_assoc, hvConsAppend, hvNilAppend, simp_spine]
  apply congrArg (fun f : HalfRow → EffectM _ => (liftM (load v17 HalfTy) >>= f))
  funext old
  denote_step_all v
  denote_eval v 19 115
  change v83 = castHalves v67 at hv83
  change v84 = castHalves v68 at hv84
  change v85 = addHalves v84 v83 at hv85
  change v86 = castHalves v69 at hv86
  change v87 = addHalves v85 v86 at hv87
  change v88 = castHalves v70 at hv88
  change v89 = addHalves v87 v88 at hv89
  change v90 = castHalves v71 at hv90
  change v91 = addHalves v89 v90 at hv91
  change v92 = castHalves v72 at hv92
  change v93 = addHalves v91 v92 at hv93
  change v94 = castHalves v73 at hv94
  change v95 = addHalves v93 v94 at hv95
  change v96 = castHalves v74 at hv96
  change v97 = addHalves v95 v96 at hv97
  change v98 = castHalves v75 at hv98
  change v99 = addHalves v97 v98 at hv99
  change v100 = castHalves v76 at hv100
  change v101 = addHalves v99 v100 at hv101
  change v102 = castHalves v77 at hv102
  change v103 = addHalves v101 v102 at hv103
  change v104 = castHalves v78 at hv104
  change v105 = addHalves v103 v104 at hv105
  change v106 = castHalves v79 at hv106
  change v107 = addHalves v105 v106 at hv107
  change v108 = castHalves v80 at hv108
  change v109 = addHalves v107 v108 at hv109
  change v110 = castHalves v81 at hv110
  change v111 = addHalves v109 v110 at hv111
  change v112 = castHalves v82 at hv112
  change v113 = addHalves v111 v112 at hv113
  change v115 = addHalves old v113 at hv115
  have edelta : delta16 V = v113 := by
    simp only [delta16, reduce16, sumRows16, shuffleRows16, ← hv0, ← hv1, ← hv2, ← hv3, ← hv4, ← hv5, ← hv6, ← hv7, ← hv8, ← hv9, ← hv10, ← hv11, ← hv12, ← hv13, ← hv14, ← hv15, ← hv19, ← hv20, ← hv21, ← hv22, ← hv23, ← hv24, ← hv25, ← hv26, ← hv27, ← hv28, ← hv29, ← hv30, ← hv31, ← hv32, ← hv33, ← hv34, ← hv35, ← hv36, ← hv37, ← hv38, ← hv39, ← hv40, ← hv41, ← hv42, ← hv43, ← hv44, ← hv45, ← hv46, ← hv47, ← hv48, ← hv49, ← hv50, ← hv51, ← hv52, ← hv53, ← hv54, ← hv55, ← hv56, ← hv57, ← hv58, ← hv59, ← hv60, ← hv61, ← hv62, ← hv63, ← hv64, ← hv65, ← hv66, ← hv67, ← hv68, ← hv69, ← hv70, ← hv71, ← hv72, ← hv73, ← hv74, ← hv75, ← hv76, ← hv77, ← hv78, ← hv79, ← hv80, ← hv81, ← hv82, ← hv83, ← hv84, ← hv85, ← hv86, ← hv87, ← hv88, ← hv89, ← hv90, ← hv91, ← hv92, ← hv93, ← hv94, ← hv95, ← hv96, ← hv97, ← hv98, ← hv99, ← hv100, ← hv101, ← hv102, ← hv103, ← hv104, ← hv105, ← hv106, ← hv107, ← hv108, ← hv109, ← hv110, ← hv111, ← hv112, ← hv113, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
  conv_rhs => rw [edelta, ← hv115, ← hv114]
  rw [BlockCom.denote_var]
  simp only [Expr.denote_unfold, denoteOp_store', bind_map_left, bind_assoc, hvNilAppend, simp_spine]
  apply congrArg (fun f : Unit → EffectM _ => (liftM (store v17 HalfTy v115) >>= f))
  funext ignored
  denote_step_all v
  denote_eval v 116 116
  conv_rhs => rw [← hv116]
  simp only [BlockCom.denote_term, Terminator.denote, simp_spine]
  rcases v116 with ⟨c⟩
  cases c with
  | none => rfl
  | some b =>
    dsimp only
    rw [targetIte]
    by_cases hb : b = 1 <;> simp only [hb, reduceIte, Target.denote, next11] <;> rfl

theorem block11_continue {α : Type} (V : Input11.Valuation) (s : GlobalState)
    (k : (HVector TyDenote.toType ([] : List SLLVM.Ty) ⊕
      SuccArgs agave_batch_16.cfgSigs) → EffectM α) :
    StateT.run (agave_batch_16.cfgBlock_11.denote V >>= fun r => k r.2) s =
      StateT.run (output16Spec V >>= k) s := by
  have h := congrArg (fun x => x >>= k) (output16_denote V)
  simpa only [bind_assoc, pure_bind] using congrArg (fun x => StateT.run x s) h
end AgaveLatticeHash.MLIR.BatchOutput16
