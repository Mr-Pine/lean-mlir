/- Released under Apache 2.0 license as described in the file LICENSE. -/
import SSA.Projects.Agave.LatticeHash.MLIR.BatchCFG8
import SSA.Projects.Agave.LatticeHash.MLIR.BatchReductionCore
import SSA.Projects.Agave.LatticeHash.MLIR.BatchXof
import SSA.Projects.Agave.LatticeHash.MLIR.OutputRead
import SSA.Projects.Firedancer.MLIR.DenoteStep

namespace AgaveLatticeHash.MLIR.BatchOutput
open LeanMLIR SLLVM Firedancer
open InstCombine (LLVM)
open BatchReduction

private abbrev blockInput {Γ Γout : Ctxt SLLVM.Ty} {rets sigs}
    (_ : BlockCom Γ Γout rets sigs) := Γ
abbrev Input8 := blockInput agave_batch_8.cfgBlock_24
abbrev HalfTy : LLVM.Ty := .vector 16 (.bitvec (.concrete 16))

def xor8 (x y : Row8) : Row8 := Vector.ofFn fun i => LLVM.xor x[i] y[i]

def lower8 (V : Input8.Valuation) : HalfRow :=
  reduce8 (xor8 (V ⟨5, rfl⟩) (V ⟨15, rfl⟩))
    (xor8 (V ⟨1, rfl⟩) (V ⟨11, rfl⟩))
    (xor8 (V ⟨13, rfl⟩) (V ⟨7, rfl⟩))
    (xor8 (V ⟨9, rfl⟩) (V ⟨3, rfl⟩))
    (xor8 (V ⟨10, rfl⟩) (V ⟨0, rfl⟩))
    (xor8 (V ⟨6, rfl⟩) (V ⟨12, rfl⟩))
    (xor8 (V ⟨2, rfl⟩) (V ⟨8, rfl⟩))
    (xor8 (V ⟨14, rfl⟩) (V ⟨4, rfl⟩))

def upper8 (V : Input8.Valuation) : HalfRow :=
  reduce8 (xor8 (V ⟨5, rfl⟩) (V ⟨25, rfl⟩))
    (xor8 (V ⟨1, rfl⟩) (V ⟨24, rfl⟩))
    (xor8 (V ⟨13, rfl⟩) (V ⟨23, rfl⟩))
    (xor8 (V ⟨9, rfl⟩) (V ⟨22, rfl⟩))
    (xor8 (V ⟨10, rfl⟩) (V ⟨21, rfl⟩))
    (xor8 (V ⟨6, rfl⟩) (V ⟨20, rfl⟩))
    (xor8 (V ⟨2, rfl⟩) (V ⟨19, rfl⟩))
    (xor8 (V ⟨14, rfl⟩) (V ⟨18, rfl⟩))

def next8 (V : Input8.Valuation) (counter : LLVM.IntW 64) : SuccArgs agave_batch_8.cfgSigs :=
  ⟨22, rfl, [counter, V ⟨35, rfl⟩, V ⟨34, rfl⟩,
    V ⟨33, rfl⟩, V ⟨32, rfl⟩, V ⟨31, rfl⟩, V ⟨30, rfl⟩,
    V ⟨29, rfl⟩, V ⟨28, rfl⟩, V ⟨27, rfl⟩, V ⟨26, rfl⟩,
    V ⟨25, rfl⟩, V ⟨24, rfl⟩, V ⟨23, rfl⟩, V ⟨22, rfl⟩,
    V ⟨21, rfl⟩, V ⟨20, rfl⟩, V ⟨19, rfl⟩, V ⟨18, rfl⟩, V ⟨17, rfl⟩]ₕ⟩

/-- The two accumulator writes and the precise counter branch emitted in bb25.
The input reduction is separate from the surrounding memory effects. -/
def output8Spec (V : Input8.Valuation) :
    EffectM (HVector TyDenote.toType ([] : List SLLVM.Ty) ⊕ SuccArgs agave_batch_8.cfgSigs) := do
  let offset := LLVM.shl (V ⟨16, rfl⟩) (V ⟨90, rfl⟩) {nsw := true, nuw := true}
  let loPtr := gep (V ⟨133, rfl⟩) 1 0 offset
  let lo : HalfRow ← liftM (load loPtr HalfTy)
  liftM (store loPtr HalfTy (addHalves lo (lower8 V)))
  let hiPtr := gep (V ⟨17, rfl⟩) 1 0 offset
  let hi : HalfRow ← liftM (load hiPtr HalfTy)
  liftM (store hiPtr HalfTy (addHalves hi (upper8 V)))
  let next := LLVM.add (V ⟨16, rfl⟩) (V ⟨94, rfl⟩) {nsw := true, nuw := true}
  match LLVM.icmp .eq next (V ⟨124, rfl⟩) with
  | .poison => throwUB
  | .value b => pure (.inr (if b = 1 then ⟨25, rfl, .nil⟩ else next8 V next))

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
set_option maxHeartbeats 2000000 in
/-- The complete actual output block, including both effects and its branch. -/
theorem output8_denote (V : Input8.Valuation) :
    (do let (_, r) ← agave_batch_8.cfgBlock_24.denote V; pure r) = output8Spec V := by
  denote_step_all v
  denote_eval v 0 48
  change v0 = xor8 (V ⟨5, rfl⟩) (V ⟨15, rfl⟩) at hv0
  change v1 = xor8 (V ⟨1, rfl⟩) (V ⟨11, rfl⟩) at hv1
  change v2 = xor8 (V ⟨13, rfl⟩) (V ⟨7, rfl⟩) at hv2
  change v3 = xor8 (V ⟨9, rfl⟩) (V ⟨3, rfl⟩) at hv3
  change v4 = xor8 (V ⟨10, rfl⟩) (V ⟨0, rfl⟩) at hv4
  change v5 = xor8 (V ⟨6, rfl⟩) (V ⟨12, rfl⟩) at hv5
  change v6 = xor8 (V ⟨2, rfl⟩) (V ⟨8, rfl⟩) at hv6
  change v7 = xor8 (V ⟨14, rfl⟩) (V ⟨4, rfl⟩) at hv7
  change v32 = castHalves v24 at hv32
  change v33 = castHalves v25 at hv33
  change v35 = castHalves v26 at hv35
  change v37 = castHalves v27 at hv37
  change v39 = castHalves v28 at hv39
  change v41 = castHalves v29 at hv41
  change v43 = castHalves v30 at hv43
  change v45 = castHalves v31 at hv45
  change v34 = addHalves v33 v32 at hv34
  change v36 = addHalves v34 v35 at hv36
  change v38 = addHalves v36 v37 at hv38
  change v40 = addHalves v38 v39 at hv40
  change v42 = addHalves v40 v41 at hv42
  change v44 = addHalves v42 v43 at hv44
  change v46 = addHalves v44 v45 at hv46
  have elo : lower8 V = v46 := by
    simp only [lower8, reduce8, sumRows8, shuffleRows8, ← hv0, ← hv1, ← hv2, ← hv3, ← hv4, ← hv5, ← hv6, ← hv7, ← hv8, ← hv9, ← hv10, ← hv11, ← hv12, ← hv13, ← hv14, ← hv15, ← hv16, ← hv17, ← hv18, ← hv19, ← hv20, ← hv21, ← hv22, ← hv23, ← hv24, ← hv25, ← hv26, ← hv27, ← hv28, ← hv29, ← hv30, ← hv31, ← hv32, ← hv33, ← hv34, ← hv35, ← hv36, ← hv37, ← hv38, ← hv39, ← hv40, ← hv41, ← hv42, ← hv43, ← hv44, ← hv45, ← hv46, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
  unfold output8Spec
  simp only [elo, ← hv47, ← hv48]
  rw [BlockCom.denote_var]
  simp only [Expr.denote_unfold, denoteOp_load, bind_map_left, bind_assoc, hvConsAppend, hvNilAppend, simp_spine]
  congr 1
  funext lo
  denote_step_all v
  denote_eval v 50 50
  change v50 = addHalves lo v46 at hv50
  conv_rhs => rw [← hv50]
  rw [BlockCom.denote_var]
  simp only [Expr.denote_unfold, denoteOp_store', bind_map_left, bind_assoc, hvNilAppend, simp_spine]
  apply congrArg (fun f : Unit → EffectM _ => (liftM (store v48 HalfTy v50) >>= f))
  funext ignored
  denote_step_all v
  denote_eval v 51 98
  change v51 = xor8 (V ⟨5, rfl⟩) (V ⟨25, rfl⟩) at hv51
  change v52 = xor8 (V ⟨1, rfl⟩) (V ⟨24, rfl⟩) at hv52
  change v53 = xor8 (V ⟨13, rfl⟩) (V ⟨23, rfl⟩) at hv53
  change v54 = xor8 (V ⟨9, rfl⟩) (V ⟨22, rfl⟩) at hv54
  change v55 = xor8 (V ⟨10, rfl⟩) (V ⟨21, rfl⟩) at hv55
  change v56 = xor8 (V ⟨6, rfl⟩) (V ⟨20, rfl⟩) at hv56
  change v57 = xor8 (V ⟨2, rfl⟩) (V ⟨19, rfl⟩) at hv57
  change v58 = xor8 (V ⟨14, rfl⟩) (V ⟨18, rfl⟩) at hv58
  change v83 = castHalves v75 at hv83
  change v84 = castHalves v76 at hv84
  change v86 = castHalves v77 at hv86
  change v88 = castHalves v78 at hv88
  change v90 = castHalves v79 at hv90
  change v92 = castHalves v80 at hv92
  change v94 = castHalves v81 at hv94
  change v96 = castHalves v82 at hv96
  change v85 = addHalves v84 v83 at hv85
  change v87 = addHalves v85 v86 at hv87
  change v89 = addHalves v87 v88 at hv89
  change v91 = addHalves v89 v90 at hv91
  change v93 = addHalves v91 v92 at hv93
  change v95 = addHalves v93 v94 at hv95
  change v97 = addHalves v95 v96 at hv97
  have ehi : upper8 V = v97 := by
    simp only [upper8, reduce8, sumRows8, shuffleRows8, ← hv51, ← hv52, ← hv53, ← hv54, ← hv55, ← hv56, ← hv57, ← hv58, ← hv59, ← hv60, ← hv61, ← hv62, ← hv63, ← hv64, ← hv65, ← hv66, ← hv67, ← hv68, ← hv69, ← hv70, ← hv71, ← hv72, ← hv73, ← hv74, ← hv75, ← hv76, ← hv77, ← hv78, ← hv79, ← hv80, ← hv81, ← hv82, ← hv83, ← hv84, ← hv85, ← hv86, ← hv87, ← hv88, ← hv89, ← hv90, ← hv91, ← hv92, ← hv93, ← hv94, ← hv95, ← hv96, ← hv97, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
  conv_rhs => rw [ehi, ← hv98]
  rw [BlockCom.denote_var]
  simp only [Expr.denote_unfold, denoteOp_load, bind_map_left, bind_assoc, hvConsAppend, hvNilAppend, simp_spine]
  apply congrArg (fun f : HalfRow → EffectM _ => (liftM (load v98 HalfTy) >>= f))
  funext hi
  denote_step_all v
  denote_eval v 100 100
  change v100 = addHalves hi v97 at hv100
  conv_rhs => rw [← hv100]
  rw [BlockCom.denote_var]
  simp only [Expr.denote_unfold, denoteOp_store', bind_map_left, bind_assoc, hvNilAppend, simp_spine]
  apply congrArg (fun f : Unit → EffectM _ => (liftM (store v98 HalfTy v100) >>= f))
  funext ignored2
  denote_step_all v
  denote_eval v 101 102
  conv_rhs => rw [← hv101, ← hv102]
  simp only [BlockCom.denote_term, Terminator.denote, simp_spine]
  rcases v102 with ⟨c⟩
  cases c with
  | none => rfl
  | some b =>
    dsimp only
    rw [targetIte]
    by_cases hb : b = 1 <;> simp only [hb, reduceIte, Target.denote, next8] <;> rfl

/-- Use the block contract with any successor continuation. -/
theorem output8_continue {α : Type} (V : Input8.Valuation) (s : GlobalState)
    (k : (HVector TyDenote.toType ([] : List SLLVM.Ty) ⊕
      SuccArgs agave_batch_8.cfgSigs) → EffectM α) :
    StateT.run (agave_batch_8.cfgBlock_24.denote V >>= fun r => k r.2) s =
      StateT.run (output8Spec V >>= k) s := by
  have h := congrArg (fun x => x >>= k) (output8_denote V)
  simpa only [bind_assoc, pure_bind] using congrArg (fun x => StateT.run x s) h

def sums16 (a b : Vector (BitVec 16) 16) : Vector (BitVec 16) 16 :=
  Vector.ofFn fun i => a[i] + b[i]

/-- Both reduction halves are added to their existing accumulator bytes.
Only storage validity, disjoint writes, and the emitted scalar constants are
required; arithmetic values are arbitrary. -/
theorem output8Spec_run (V : Input8.Valuation) (s : GlobalState)
    (counter : Nat) (hc : counter < 32) (loPtr hiPtr : Pointer)
    (lo hi dlo dhi : Vector (BitVec 16) 16)
    (hcounter : V ⟨16, rfl⟩ = .value (BitVec.ofNat 64 counter))
    (hshift : V ⟨90, rfl⟩ = .value 6#64)
    (hone : V ⟨94, rfl⟩ = .value 1#64)
    (hend : V ⟨124, rfl⟩ = .value 32#64)
    (hloPtr : gep (V ⟨133, rfl⟩) 1 0 (.value (BitVec.ofNat 64 (64*counter))) = .value loPtr)
    (hhiPtr : gep (V ⟨17, rfl⟩) 1 0 (.value (BitVec.ofNat 64 (64*counter))) = .value hiPtr)
    (hlo : lower8 V = dlo.map PoisonOr.value)
    (hhi : upper8 V = dhi.map PoisonOr.value)
    (flo : Fits s.mem loPtr 256) (fhi : Fits s.mem hiPtr 256)
    (rlo : readWord? loPtr 256 s.mem = some (packBits lo))
    (rhi : readWord? hiPtr 256 s.mem = some (packBits hi))
    (hdisj : loPtr.offsetInBits + 256 ≤ hiPtr.offsetInBits ∨
      hiPtr.offsetInBits + 256 ≤ loPtr.offsetInBits) :
    StateT.run (output8Spec V) s = .value
      (.inr (if counter = 31 then ⟨25, rfl, .nil⟩
        else next8 V (.value (BitVec.ofNat 64 (counter+1)))),
        {s with mem := (s.mem.splice loPtr (packBits (sums16 lo dlo))).splice hiPtr (packBits (sums16 hi dhi))}) := by
  have rhi' : readWord? hiPtr 256
      (s.mem.splice loPtr (packBits (sums16 lo dlo))) = some (packBits hi) := by
    rw [readWord?_splice_disjoint _ hdisj]
    exact rhi
  simp only [output8Spec, hcounter, hshift, hone, hend,
    BatchXof.counter_shift6 counter hc, BatchXof.counter_succ counter hc,
    hloPtr, hhiPtr, hlo, hhi]
  rw [EffectM.run_bind, run_liftM (s := s) (run_load_vector lo flo rlo)]
  simp only [PoisonOr.value_bind]
  rw [show addHalves (lo.map PoisonOr.value) (dlo.map PoisonOr.value) =
    (sums16 lo dlo).map PoisonOr.value from addHalves_defined lo dlo]
  rw [EffectM.run_bind, run_liftM (s := s)
    (run_store (flatten_packBits (sums16 lo dlo)) flo)]
  simp only [PoisonOr.value_bind]
  rw [EffectM.run_bind, run_liftM
    (s := {s with mem := s.mem.splice loPtr (packBits (sums16 lo dlo))})
    (run_load_vector hi (fits_splice fhi) rhi')]
  simp only [PoisonOr.value_bind]
  rw [show addHalves (hi.map PoisonOr.value) (dhi.map PoisonOr.value) =
    (sums16 hi dhi).map PoisonOr.value from addHalves_defined hi dhi]
  rw [EffectM.run_bind, run_liftM
    (s := {s with mem := s.mem.splice loPtr (packBits (sums16 lo dlo))})
    (run_store (flatten_packBits (sums16 hi dhi)) (fits_splice fhi))]
  simp only [PoisonOr.value_bind, BatchXof.counter_exit counter hc]
  by_cases h : counter = 31 <;> simp [h]

end AgaveLatticeHash.MLIR.BatchOutput
