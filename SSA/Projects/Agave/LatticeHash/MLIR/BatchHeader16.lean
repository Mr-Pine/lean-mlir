/- Released under Apache 2.0 license as described in the file LICENSE. -/
import SSA.Projects.Agave.LatticeHash.MLIR.BatchCFG16
import SSA.Projects.Agave.LatticeHash.MLIR.Memory
import SSA.Projects.Firedancer.MLIR.DenoteStep

namespace AgaveLatticeHash.MLIR.BatchHeader16
open LeanMLIR SLLVM
open InstCombine (LLVM)
private abbrev blockInput {Γ Γout : Ctxt SLLVM.Ty} {rets sigs}
    (_ : BlockCom Γ Γout rets sigs) := Γ
private abbrev blockOutput {Γ Γout : Ctxt SLLVM.Ty} {rets sigs}
    (_ : BlockCom Γ Γout rets sigs) := Γout
abbrev Input16 := blockInput agave_batch_16.cfgBlock_0

private def laneBinary {n w : Nat} (f : LLVM.IntW w → LLVM.IntW w → LLVM.IntW w)
    (a b : Vector (LLVM.IntW w) n) : Vector (LLVM.IntW w) n :=
  Vector.ofFn fun i => f a[i] b[i]

abbrev outputTypes16 : List SLLVM.Ty :=
  [SLLVM.Ty.ptr,
   SLLVM.Ty.ptr,
   SLLVM.Ty.ptr,
   SLLVM.Ty.ptr,
   SLLVM.Ty.ptr,
   SLLVM.Ty.ptr,
   SLLVM.Ty.ptr,
   SLLVM.Ty.ptr,
   SLLVM.Ty.ptr,
   SLLVM.Ty.ptr,
   SLLVM.Ty.ptr,
   SLLVM.Ty.ptr,
   SLLVM.Ty.ptr,
   SLLVM.Ty.ptr,
   SLLVM.Ty.ptr,
   SLLVM.Ty.ptr,
   SLLVM.Ty.bitvec 1,
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
   SLLVM.Ty.arith (.vector 16 (.bitvec (.concrete 8))),
   SLLVM.Ty.arith (.vector 16 (.bitvec (.concrete 8))),
   SLLVM.Ty.arith (.vector 16 (.bitvec (.concrete 8))),
   SLLVM.Ty.arith (.vector 8 (.bitvec (.concrete 8))),
   SLLVM.Ty.arith (.vector 8 (.bitvec (.concrete 64))),
   SLLVM.Ty.arith (.vector 8 (.bitvec (.concrete 64))),
   SLLVM.Ty.arith (.vector 4 (.bitvec (.concrete 64))),
   SLLVM.Ty.arith (.vector 8 (.bitvec (.concrete 32))),
   SLLVM.Ty.arith (.vector 8 (.bitvec (.concrete 64))),
   SLLVM.Ty.arith (.vector 8 (.bitvec (.concrete 64))),
   SLLVM.Ty.arith (.vector 8 (.bitvec (.concrete 64))),
   SLLVM.Ty.arith (.vector 8 (.bitvec (.concrete 64))),
   SLLVM.Ty.arith (.vector 4 (.bitvec (.concrete 64))),
   SLLVM.Ty.arith (.vector 8 (.bitvec (.concrete 32))),
   SLLVM.Ty.arith (.vector 8 (.bitvec (.concrete 32))),
   SLLVM.Ty.arith (.vector 8 (.bitvec (.concrete 32))),
   SLLVM.Ty.arith (.vector 8 (.bitvec (.concrete 1))),
   SLLVM.Ty.arith (.vector 8 (.bitvec (.concrete 1))),
   SLLVM.Ty.arith (.vector 8 (.bitvec (.concrete 64))),
   SLLVM.Ty.arith (.vector 16 (.bitvec (.concrete 8))),
   SLLVM.Ty.arith (.vector 8 (.bitvec (.concrete 8))),
   SLLVM.Ty.arith (.vector 8 (.bitvec (.concrete 64))),
   SLLVM.Ty.arith (.vector 4 (.bitvec (.concrete 64))),
   SLLVM.Ty.arith (.vector 8 (.bitvec (.concrete 32))),
   SLLVM.Ty.arith (.vector 8 (.bitvec (.concrete 64))),
   SLLVM.Ty.arith (.vector 8 (.bitvec (.concrete 64))),
   SLLVM.Ty.arith (.vector 8 (.bitvec (.concrete 64))),
   SLLVM.Ty.arith (.vector 4 (.bitvec (.concrete 64))),
   SLLVM.Ty.arith (.vector 8 (.bitvec (.concrete 32))),
   SLLVM.Ty.arith (.vector 8 (.bitvec (.concrete 32))),
   SLLVM.Ty.arith (.vector 8 (.bitvec (.concrete 32))),
   SLLVM.Ty.arith (.vector 8 (.bitvec (.concrete 1))),
   SLLVM.Ty.arith (.vector 8 (.bitvec (.concrete 1))),
   SLLVM.Ty.arith (.vector 8 (.bitvec (.concrete 64)))]
abbrev Output16 := Ctxt.ofList outputTypes16 ++ Input16

/-- Exact header values, preserving all compiler arithmetic and poison flags.
The bounds predicate is represented as false under the run theorem's bound. -/
def values16 (V : Input16.Valuation) : Output16.Valuation :=
  let v0 : Vector (LLVM.IntW 64) 8 := laneBinary (n := 8) (w := 64) (fun a b => LLVM.add a b) (V ⟨24, rfl⟩) (V ⟨119, rfl⟩)
  let v1 : Vector (LLVM.IntW 1) 8 := vicmp .ugt (V ⟨28, rfl⟩) v0
  let v2 : Vector (LLVM.IntW 1) 8 := vicmp .eq (V ⟨24, rfl⟩) (V ⟨128, rfl⟩)
  let v3 : Vector (LLVM.IntW 32) 8 := vselect v1 (V ⟨117, rfl⟩) (V ⟨116, rfl⟩)
  let v4 : Vector (LLVM.IntW 32) 8 := vzext 32 v2
  let v5 : Vector (LLVM.IntW 32) 8 := laneBinary (n := 8) (w := 32) (fun a b => LLVM.or a b {«disjoint» := true}) v3 v4
  let v6 : Vector (LLVM.IntW 64) 4 := bitcast (.vector 8 (.bitvec (.concrete 32))) (.vector 4 (.bitvec (.concrete 64))) v5
  let v7 : Vector (LLVM.IntW 64) 8 := LLVM.Ty.shufflevector (e := .bitvec (.concrete 64)) [0, 1, 2, 3, -1, -1, -1, -1] v6 (V ⟨115, rfl⟩)
  let v8 : Vector (LLVM.IntW 64) 8 := laneBinary (n := 8) (w := 64) (fun a b => LLVM.sub a b) (V ⟨28, rfl⟩) (V ⟨24, rfl⟩)
  let v9 : Vector (LLVM.IntW 64) 8 := vumin v8 (V ⟨119, rfl⟩)
  let v10 : Vector (LLVM.IntW 32) 8 := vtrunc 32 v9 {nsw := true, nuw := true}
  let v11 : Vector (LLVM.IntW 64) 4 := bitcast (.vector 8 (.bitvec (.concrete 32))) (.vector 4 (.bitvec (.concrete 64))) v10
  let v12 : Vector (LLVM.IntW 64) 8 := LLVM.Ty.shufflevector (e := .bitvec (.concrete 64)) [0, 1, 2, 3, -1, -1, -1, -1] v11 (V ⟨115, rfl⟩)
  let v13 : Vector (LLVM.IntW 8) 8 := vzext 8 v1
  let v14 : Vector (LLVM.IntW 8) 16 := LLVM.Ty.shufflevector (e := .bitvec (.concrete 8)) [0, 1, 2, 3, 4, 5, 6, 7, -1, -1, -1, -1, -1, -1, -1, -1] v13 (V ⟨114, rfl⟩)
  let v15 : Vector (LLVM.IntW 64) 8 := laneBinary (n := 8) (w := 64) (fun a b => LLVM.add a b) (V ⟨25, rfl⟩) (V ⟨119, rfl⟩)
  let v16 : Vector (LLVM.IntW 1) 8 := vicmp .ugt (V ⟨26, rfl⟩) v15
  let v17 : Vector (LLVM.IntW 1) 8 := vicmp .eq (V ⟨25, rfl⟩) (V ⟨128, rfl⟩)
  let v18 : Vector (LLVM.IntW 32) 8 := vselect v16 (V ⟨117, rfl⟩) (V ⟨116, rfl⟩)
  let v19 : Vector (LLVM.IntW 32) 8 := vzext 32 v17
  let v20 : Vector (LLVM.IntW 32) 8 := laneBinary (n := 8) (w := 32) (fun a b => LLVM.or a b {«disjoint» := true}) v18 v19
  let v21 : Vector (LLVM.IntW 64) 4 := bitcast (.vector 8 (.bitvec (.concrete 32))) (.vector 4 (.bitvec (.concrete 64))) v20
  let v22 : Vector (LLVM.IntW 64) 8 := LLVM.Ty.shufflevector (e := .bitvec (.concrete 64)) [-1, -1, -1, -1, 0, 1, 2, 3] v21 (V ⟨115, rfl⟩)
  let v23 : Vector (LLVM.IntW 64) 8 := LLVM.Ty.shufflevector (e := .bitvec (.concrete 64)) [0, 1, 2, 3, 12, 13, 14, 15] v7 v22
  let v24 : Vector (LLVM.IntW 64) 8 := laneBinary (n := 8) (w := 64) (fun a b => LLVM.sub a b) (V ⟨26, rfl⟩) (V ⟨25, rfl⟩)
  let v25 : Vector (LLVM.IntW 64) 8 := vumin v24 (V ⟨119, rfl⟩)
  let v26 : Vector (LLVM.IntW 32) 8 := vtrunc 32 v25 {nsw := true, nuw := true}
  let v27 : Vector (LLVM.IntW 64) 4 := bitcast (.vector 8 (.bitvec (.concrete 32))) (.vector 4 (.bitvec (.concrete 64))) v26
  let v28 : Vector (LLVM.IntW 64) 8 := LLVM.Ty.shufflevector (e := .bitvec (.concrete 64)) [-1, -1, -1, -1, 0, 1, 2, 3] v27 (V ⟨115, rfl⟩)
  let v29 : Vector (LLVM.IntW 64) 8 := LLVM.Ty.shufflevector (e := .bitvec (.concrete 64)) [0, 1, 2, 3, 12, 13, 14, 15] v12 v28
  let v30 : Vector (LLVM.IntW 8) 8 := vzext 8 v16
  let v31 : Vector (LLVM.IntW 8) 16 := LLVM.Ty.shufflevector (e := .bitvec (.concrete 8)) [-1, -1, -1, -1, -1, -1, -1, -1, 0, 1, 2, 3, 4, 5, 6, 7] v30 (V ⟨114, rfl⟩)
  let v32 : Vector (LLVM.IntW 8) 16 := LLVM.Ty.shufflevector (e := .bitvec (.concrete 8)) [0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31] v14 v31
  let v33 : Vector (LLVM.IntW 8) 16 := vfreeze v32
  let v34 : LLVM.IntW 64 := LLVM.lshr (V ⟨8, rfl⟩) (V ⟨113, rfl⟩)
  let v35 : LLVM.IntW 64 := LLVM.lshr (V ⟨9, rfl⟩) (V ⟨113, rfl⟩)
  let v36 : LLVM.IntW 64 := LLVM.lshr (V ⟨10, rfl⟩) (V ⟨113, rfl⟩)
  let v37 : LLVM.IntW 64 := LLVM.lshr (V ⟨11, rfl⟩) (V ⟨113, rfl⟩)
  let v38 : LLVM.IntW 64 := LLVM.lshr (V ⟨12, rfl⟩) (V ⟨113, rfl⟩)
  let v39 : LLVM.IntW 64 := LLVM.lshr (V ⟨13, rfl⟩) (V ⟨113, rfl⟩)
  let v40 : LLVM.IntW 64 := LLVM.lshr (V ⟨14, rfl⟩) (V ⟨113, rfl⟩)
  let v41 : LLVM.IntW 64 := LLVM.lshr (V ⟨15, rfl⟩) (V ⟨113, rfl⟩)
  let v42 : LLVM.IntW 64 := LLVM.lshr (V ⟨16, rfl⟩) (V ⟨113, rfl⟩)
  let v43 : LLVM.IntW 64 := LLVM.lshr (V ⟨17, rfl⟩) (V ⟨113, rfl⟩)
  let v44 : LLVM.IntW 64 := LLVM.lshr (V ⟨18, rfl⟩) (V ⟨113, rfl⟩)
  let v45 : LLVM.IntW 64 := LLVM.lshr (V ⟨19, rfl⟩) (V ⟨113, rfl⟩)
  let v46 : LLVM.IntW 64 := LLVM.lshr (V ⟨20, rfl⟩) (V ⟨113, rfl⟩)
  let v47 : LLVM.IntW 64 := LLVM.lshr (V ⟨21, rfl⟩) (V ⟨113, rfl⟩)
  let v48 : LLVM.IntW 64 := LLVM.lshr (V ⟨22, rfl⟩) (V ⟨113, rfl⟩)
  let v49 : LLVM.IntW 64 := LLVM.lshr (V ⟨23, rfl⟩) (V ⟨113, rfl⟩)
  let v50 : LLVM.IntW 1 := PoisonOr.value 0#1
  let v51 : SLLVM.Ptr := gep (V ⟨163, rfl⟩) 4 0 v34
  let v52 : SLLVM.Ptr := gep (V ⟨58, rfl⟩) 4 0 v35
  let v53 : SLLVM.Ptr := gep (V ⟨57, rfl⟩) 4 0 v36
  let v54 : SLLVM.Ptr := gep (V ⟨56, rfl⟩) 4 0 v37
  let v55 : SLLVM.Ptr := gep (V ⟨55, rfl⟩) 4 0 v38
  let v56 : SLLVM.Ptr := gep (V ⟨54, rfl⟩) 4 0 v39
  let v57 : SLLVM.Ptr := gep (V ⟨53, rfl⟩) 4 0 v40
  let v58 : SLLVM.Ptr := gep (V ⟨52, rfl⟩) 4 0 v41
  let v59 : SLLVM.Ptr := gep (V ⟨51, rfl⟩) 4 0 v42
  let v60 : SLLVM.Ptr := gep (V ⟨50, rfl⟩) 4 0 v43
  let v61 : SLLVM.Ptr := gep (V ⟨49, rfl⟩) 4 0 v44
  let v62 : SLLVM.Ptr := gep (V ⟨48, rfl⟩) 4 0 v45
  let v63 : SLLVM.Ptr := gep (V ⟨47, rfl⟩) 4 0 v46
  let v64 : SLLVM.Ptr := gep (V ⟨46, rfl⟩) 4 0 v47
  let v65 : SLLVM.Ptr := gep (V ⟨45, rfl⟩) 4 0 v48
  let v66 : SLLVM.Ptr := gep (V ⟨44, rfl⟩) 4 0 v49
  Ctxt.Valuation.ofHVector (types := outputTypes16)
    (v66 ::ₕ v65 ::ₕ v64 ::ₕ v63 ::ₕ v62 ::ₕ v61 ::ₕ v60 ::ₕ v59 ::ₕ v58 ::ₕ v57 ::ₕ v56 ::ₕ v55 ::ₕ v54 ::ₕ v53 ::ₕ v52 ::ₕ v51 ::ₕ v50 ::ₕ v49 ::ₕ v48 ::ₕ v47 ::ₕ v46 ::ₕ v45 ::ₕ v44 ::ₕ v43 ::ₕ v42 ::ₕ v41 ::ₕ v40 ::ₕ v39 ::ₕ v38 ::ₕ v37 ::ₕ v36 ::ₕ v35 ::ₕ v34 ::ₕ v33 ::ₕ v32 ::ₕ v31 ::ₕ v30 ::ₕ v29 ::ₕ v28 ::ₕ v27 ::ₕ v26 ::ₕ v25 ::ₕ v24 ::ₕ v23 ::ₕ v22 ::ₕ v21 ::ₕ v20 ::ₕ v19 ::ₕ v18 ::ₕ v17 ::ₕ v16 ::ₕ v15 ::ₕ v14 ::ₕ v13 ::ₕ v12 ::ₕ v11 ::ₕ v10 ::ₕ v9 ::ₕ v8 ::ₕ v7 ::ₕ v6 ::ₕ v5 ::ₕ v4 ::ₕ v3 ::ₕ v2 ::ₕ v1 ::ₕ v0 ::ₕ .nil) ++ V

def next16 (V : Input16.Valuation) : SuccArgs agave_batch_16.cfgSigs :=
  let W := values16 V
  ⟨1, rfl, W ⟨92, rfl⟩ ::ₕ
    W ⟨91, rfl⟩ ::ₕ
    W ⟨90, rfl⟩ ::ₕ
    W ⟨89, rfl⟩ ::ₕ
    W ⟨88, rfl⟩ ::ₕ
    W ⟨87, rfl⟩ ::ₕ
    W ⟨86, rfl⟩ ::ₕ
    W ⟨85, rfl⟩ ::ₕ
    W ⟨84, rfl⟩ ::ₕ
    W ⟨83, rfl⟩ ::ₕ
    W ⟨82, rfl⟩ ::ₕ
    W ⟨81, rfl⟩ ::ₕ
    W ⟨80, rfl⟩ ::ₕ
    W ⟨79, rfl⟩ ::ₕ
    W ⟨78, rfl⟩ ::ₕ
    W ⟨77, rfl⟩ ::ₕ
    W ⟨76, rfl⟩ ::ₕ
    W ⟨75, rfl⟩ ::ₕ
    W ⟨74, rfl⟩ ::ₕ
    W ⟨73, rfl⟩ ::ₕ
    W ⟨72, rfl⟩ ::ₕ
    W ⟨71, rfl⟩ ::ₕ
    W ⟨70, rfl⟩ ::ₕ
    W ⟨69, rfl⟩ ::ₕ
    W ⟨68, rfl⟩ ::ₕ
    W ⟨67, rfl⟩ ::ₕ
    W ⟨43, rfl⟩ ::ₕ
    W ⟨37, rfl⟩ ::ₕ
    W ⟨33, rfl⟩ ::ₕ
    W ⟨31, rfl⟩ ::ₕ
    W ⟨30, rfl⟩ ::ₕ
    W ⟨29, rfl⟩ ::ₕ
    W ⟨28, rfl⟩ ::ₕ
    W ⟨27, rfl⟩ ::ₕ
    W ⟨26, rfl⟩ ::ₕ
    W ⟨25, rfl⟩ ::ₕ
    W ⟨24, rfl⟩ ::ₕ
    W ⟨23, rfl⟩ ::ₕ
    W ⟨22, rfl⟩ ::ₕ
    W ⟨21, rfl⟩ ::ₕ
    W ⟨20, rfl⟩ ::ₕ
    W ⟨19, rfl⟩ ::ₕ
    W ⟨18, rfl⟩ ::ₕ
    W ⟨17, rfl⟩ ::ₕ
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
    W ⟨1, rfl⟩ ::ₕ
    W ⟨0, rfl⟩ ::ₕ .nil⟩

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
/-- Execute the actual sixteen-lane header and all sixteen source GEPs,
forwarding its complete typed payload without a memory change. -/
theorem continue16 {α : Type} (V : Input16.Valuation) (s : GlobalState)
    (off : BitVec 64)
    (ho : V ⟨8, rfl⟩ = PoisonOr.value off)
    (hl : V ⟨112, rfl⟩ = PoisonOr.value 1027#64)
    (hb : off.toNat ≤ 960)
    (k : (blockOutput agave_batch_16.cfgBlock_0).Valuation ×
      (HVector TyDenote.toType ([] : List SLLVM.Ty) ⊕ SuccArgs agave_batch_16.cfgSigs) → EffectM α) :
    StateT.run (agave_batch_16.cfgBlock_0.denote V >>= k) s =
      StateT.run (k (values16 V, .inr (next16 V))) s := by
  denote_step_all v
  simp only [BlockCom.run_bind_denote_lifetime]
  denote_step_all v
  denote_eval v 0 66
  have e : v50 = PoisonOr.value 0#1 := by
    rw [hv50, ho, hl]
    have hn : ¬1027 < off.toNat := by omega
    simp [LLVM.icmp, LLVM.icmp?, LLVM.icmp', BitVec.ult, hn]
  subst e
  clear hv50
  simp only [BlockCom.denote, Terminator.denote, Target.denote]
  subst_vars
  simp only [next16, values16, laneBinary, Ctxt.Valuation.ofHVector_cons,
    Ctxt.Valuation.ofHVector_nil, Ctxt.Valuation.cons_append, Ctxt.Valuation.nil_append]
  rfl

end AgaveLatticeHash.MLIR.BatchHeader16
