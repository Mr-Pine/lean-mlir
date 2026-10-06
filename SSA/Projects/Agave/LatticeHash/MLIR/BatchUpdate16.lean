/- Released under Apache 2.0 license as described in the file LICENSE. -/
import SSA.Projects.Agave.LatticeHash.MLIR.BatchCFG16
import SSA.Projects.Agave.LatticeHash.MLIR.BatchUpdate

namespace AgaveLatticeHash.MLIR.BatchUpdate16
open LeanMLIR SLLVM Firedancer
open InstCombine (LLVM)
set_option maxRecDepth 8192
set_option maxHeartbeats 2400000
private abbrev blockInput {Γ Γout : Ctxt SLLVM.Ty} {rets sigs}
    (_ : BlockCom Γ Γout rets sigs) := Γ
abbrev Input16 := blockInput agave_batch_16.cfgBlock_8
abbrev outputTypes16 : List SLLVM.Ty := [
  SLLVM.Ty.arith (.bitvec (.concrete 64)),
  SLLVM.Ty.arith (.vector 8 (.bitvec (.concrete 64))),
  SLLVM.Ty.arith (.vector 8 (.bitvec (.concrete 64))),
  SLLVM.Ty.arith (.bitvec (.concrete 64)),
  SLLVM.Ty.arith (.bitvec (.concrete 1)),
  SLLVM.Ty.arith (.bitvec (.concrete 64)),
  SLLVM.Ty.arith (.vector 8 (.bitvec (.concrete 64))),
  SLLVM.Ty.arith (.vector 8 (.bitvec (.concrete 64))),
  SLLVM.Ty.arith (.bitvec (.concrete 64)),
  SLLVM.Ty.arith (.bitvec (.concrete 1)),
  SLLVM.Ty.arith (.bitvec (.concrete 64)),
  SLLVM.Ty.arith (.vector 8 (.bitvec (.concrete 64))),
  SLLVM.Ty.arith (.vector 8 (.bitvec (.concrete 64))),
  SLLVM.Ty.arith (.bitvec (.concrete 64)),
  SLLVM.Ty.arith (.bitvec (.concrete 1)),
  SLLVM.Ty.arith (.bitvec (.concrete 64)),
  SLLVM.Ty.arith (.vector 8 (.bitvec (.concrete 64))),
  SLLVM.Ty.arith (.vector 8 (.bitvec (.concrete 64))),
  SLLVM.Ty.arith (.bitvec (.concrete 64)),
  SLLVM.Ty.arith (.bitvec (.concrete 1)),
  SLLVM.Ty.arith (.bitvec (.concrete 64)),
  SLLVM.Ty.arith (.vector 8 (.bitvec (.concrete 64))),
  SLLVM.Ty.arith (.vector 8 (.bitvec (.concrete 64))),
  SLLVM.Ty.arith (.bitvec (.concrete 64)),
  SLLVM.Ty.arith (.bitvec (.concrete 1)),
  SLLVM.Ty.arith (.bitvec (.concrete 64)),
  SLLVM.Ty.arith (.vector 8 (.bitvec (.concrete 64))),
  SLLVM.Ty.arith (.vector 8 (.bitvec (.concrete 64))),
  SLLVM.Ty.arith (.bitvec (.concrete 64)),
  SLLVM.Ty.arith (.bitvec (.concrete 1)),
  SLLVM.Ty.arith (.bitvec (.concrete 64)),
  SLLVM.Ty.arith (.vector 8 (.bitvec (.concrete 64))),
  SLLVM.Ty.arith (.vector 8 (.bitvec (.concrete 64))),
  SLLVM.Ty.arith (.bitvec (.concrete 64)),
  SLLVM.Ty.arith (.bitvec (.concrete 1)),
  SLLVM.Ty.arith (.bitvec (.concrete 64)),
  SLLVM.Ty.arith (.vector 8 (.bitvec (.concrete 64))),
  SLLVM.Ty.arith (.vector 8 (.bitvec (.concrete 64))),
  SLLVM.Ty.arith (.bitvec (.concrete 64)),
  SLLVM.Ty.arith (.bitvec (.concrete 1)),
  SLLVM.Ty.arith (.bitvec (.concrete 64)),
  SLLVM.Ty.arith (.vector 8 (.bitvec (.concrete 64))),
  SLLVM.Ty.arith (.vector 8 (.bitvec (.concrete 64))),
  SLLVM.Ty.arith (.bitvec (.concrete 64)),
  SLLVM.Ty.arith (.bitvec (.concrete 1)),
  SLLVM.Ty.arith (.bitvec (.concrete 64)),
  SLLVM.Ty.arith (.vector 8 (.bitvec (.concrete 64))),
  SLLVM.Ty.arith (.vector 8 (.bitvec (.concrete 64))),
  SLLVM.Ty.arith (.bitvec (.concrete 64)),
  SLLVM.Ty.arith (.bitvec (.concrete 1)),
  SLLVM.Ty.arith (.bitvec (.concrete 64)),
  SLLVM.Ty.arith (.vector 8 (.bitvec (.concrete 64))),
  SLLVM.Ty.arith (.vector 8 (.bitvec (.concrete 64))),
  SLLVM.Ty.arith (.bitvec (.concrete 64)),
  SLLVM.Ty.arith (.bitvec (.concrete 1)),
  SLLVM.Ty.arith (.bitvec (.concrete 64)),
  SLLVM.Ty.arith (.vector 8 (.bitvec (.concrete 64))),
  SLLVM.Ty.arith (.vector 8 (.bitvec (.concrete 64))),
  SLLVM.Ty.arith (.bitvec (.concrete 64)),
  SLLVM.Ty.arith (.bitvec (.concrete 1)),
  SLLVM.Ty.arith (.bitvec (.concrete 64)),
  SLLVM.Ty.arith (.vector 8 (.bitvec (.concrete 64))),
  SLLVM.Ty.arith (.vector 8 (.bitvec (.concrete 64))),
  SLLVM.Ty.arith (.bitvec (.concrete 64)),
  SLLVM.Ty.arith (.bitvec (.concrete 1)),
  SLLVM.Ty.arith (.bitvec (.concrete 64)),
  SLLVM.Ty.arith (.vector 8 (.bitvec (.concrete 64))),
  SLLVM.Ty.arith (.vector 8 (.bitvec (.concrete 64))),
  SLLVM.Ty.arith (.bitvec (.concrete 64)),
  SLLVM.Ty.arith (.bitvec (.concrete 1)),
  SLLVM.Ty.arith (.bitvec (.concrete 64)),
  SLLVM.Ty.arith (.vector 8 (.bitvec (.concrete 64))),
  SLLVM.Ty.arith (.vector 8 (.bitvec (.concrete 64))),
  SLLVM.Ty.arith (.bitvec (.concrete 64)),
  SLLVM.Ty.arith (.bitvec (.concrete 1)),
  SLLVM.Ty.arith (.vector 128 (.bitvec (.concrete 1))),
  SLLVM.Ty.arith (.bitvec (.concrete 64)),
  SLLVM.Ty.arith (.vector 8 (.bitvec (.concrete 64))),
  SLLVM.Ty.arith (.vector 8 (.bitvec (.concrete 64))),
  SLLVM.Ty.arith (.bitvec (.concrete 64)),
  SLLVM.Ty.arith (.bitvec (.concrete 1)),
  SLLVM.Ty.arith (.vector 128 (.bitvec (.concrete 1))),
  SLLVM.Ty.arith (.vector 16 (.bitvec (.concrete 32))),
  SLLVM.Ty.arith (.vector 16 (.bitvec (.concrete 32))),
  SLLVM.Ty.arith (.vector 16 (.bitvec (.concrete 32))),
  SLLVM.Ty.arith (.vector 16 (.bitvec (.concrete 32))),
  SLLVM.Ty.arith (.vector 16 (.bitvec (.concrete 32))),
  SLLVM.Ty.arith (.vector 16 (.bitvec (.concrete 32))),
  SLLVM.Ty.arith (.vector 16 (.bitvec (.concrete 32))),
  SLLVM.Ty.arith (.vector 16 (.bitvec (.concrete 32))),
  SLLVM.Ty.arith (.vector 16 (.bitvec (.concrete 32))),
  SLLVM.Ty.arith (.vector 16 (.bitvec (.concrete 32))),
  SLLVM.Ty.arith (.vector 16 (.bitvec (.concrete 32))),
  SLLVM.Ty.arith (.vector 16 (.bitvec (.concrete 32))),
  SLLVM.Ty.arith (.vector 16 (.bitvec (.concrete 32))),
  SLLVM.Ty.arith (.vector 16 (.bitvec (.concrete 32))),
  SLLVM.Ty.arith (.vector 16 (.bitvec (.concrete 32))),
  SLLVM.Ty.arith (.vector 16 (.bitvec (.concrete 32))),
  SLLVM.Ty.arith (.vector 16 (.bitvec (.concrete 1))),
  SLLVM.Ty.arith (.bitvec (.concrete 16)),
  SLLVM.Ty.arith (.bitvec (.concrete 16)),
  SLLVM.Ty.arith (.bitvec (.concrete 16)),
  SLLVM.Ty.arith (.bitvec (.concrete 8)),
  SLLVM.Ty.arith (.bitvec (.concrete 16)),
  SLLVM.Ty.arith (.bitvec (.concrete 16)),
  SLLVM.Ty.arith (.bitvec (.concrete 16)),
  SLLVM.Ty.arith (.bitvec (.concrete 8)),
  SLLVM.Ty.arith (.bitvec (.concrete 16)),
  SLLVM.Ty.arith (.bitvec (.concrete 16)),
  SLLVM.Ty.arith (.bitvec (.concrete 16)),
  SLLVM.Ty.arith (.bitvec (.concrete 8)),
  SLLVM.Ty.arith (.bitvec (.concrete 16)),
  SLLVM.Ty.arith (.bitvec (.concrete 16)),
  SLLVM.Ty.arith (.bitvec (.concrete 16)),
  SLLVM.Ty.arith (.bitvec (.concrete 8)),
  SLLVM.Ty.arith (.bitvec (.concrete 16)),
  SLLVM.Ty.arith (.bitvec (.concrete 16)),
  SLLVM.Ty.arith (.bitvec (.concrete 16)),
  SLLVM.Ty.arith (.bitvec (.concrete 8)),
  SLLVM.Ty.arith (.bitvec (.concrete 16)),
  SLLVM.Ty.arith (.bitvec (.concrete 16)),
  SLLVM.Ty.arith (.bitvec (.concrete 16)),
  SLLVM.Ty.arith (.bitvec (.concrete 8)),
  SLLVM.Ty.arith (.bitvec (.concrete 16)),
  SLLVM.Ty.arith (.bitvec (.concrete 16)),
  SLLVM.Ty.arith (.bitvec (.concrete 16)),
  SLLVM.Ty.arith (.bitvec (.concrete 8)),
  SLLVM.Ty.arith (.bitvec (.concrete 16)),
  SLLVM.Ty.arith (.bitvec (.concrete 16)),
  SLLVM.Ty.arith (.bitvec (.concrete 16)),
  SLLVM.Ty.arith (.bitvec (.concrete 8)),
  SLLVM.Ty.arith (.bitvec (.concrete 16)),
  SLLVM.Ty.arith (.bitvec (.concrete 8)),
  SLLVM.Ty.arith (.bitvec (.concrete 8)),
  SLLVM.Ty.arith (.bitvec (.concrete 8)),
  SLLVM.Ty.arith (.bitvec (.concrete 8)),
  SLLVM.Ty.arith (.bitvec (.concrete 8)),
  SLLVM.Ty.arith (.bitvec (.concrete 8)),
  SLLVM.Ty.arith (.bitvec (.concrete 8)),
  SLLVM.Ty.arith (.bitvec (.concrete 8)),
  SLLVM.Ty.arith (.bitvec (.concrete 8)),
  SLLVM.Ty.arith (.bitvec (.concrete 8)),
  SLLVM.Ty.arith (.bitvec (.concrete 8)),
  SLLVM.Ty.arith (.bitvec (.concrete 8)),
  SLLVM.Ty.arith (.bitvec (.concrete 8)),
  SLLVM.Ty.arith (.bitvec (.concrete 8)),
  SLLVM.Ty.arith (.bitvec (.concrete 8)),
  SLLVM.Ty.arith (.bitvec (.concrete 8)),
  SLLVM.Ty.arith (.bitvec (.concrete 8)),
  SLLVM.Ty.arith (.bitvec (.concrete 8)),
  SLLVM.Ty.arith (.bitvec (.concrete 8)),
  SLLVM.Ty.arith (.bitvec (.concrete 8)),
  SLLVM.Ty.arith (.bitvec (.concrete 8)),
  SLLVM.Ty.arith (.bitvec (.concrete 8))]
abbrev Output16 := Ctxt.ofList outputTypes16 ++ Input16

def xor16 (x y : Vector (LLVM.IntW 32) 16) : Vector (LLVM.IntW 32) 16 :=
  Vector.ofFn fun i => LLVM.xor x[i] y[i]

/-- Exact SSA contract of the emitted AVX512 feed-forward and offset update,
including every overflow flag and all duplicated scalar/vector offsets. -/
noncomputable def result16 (V : Input16.Valuation) : Output16.Valuation ×
    (HVector TyDenote.toType ([] : List SLLVM.Ty) ⊕ SuccArgs agave_batch_16.cfgSigs) :=
  let v0 := LLVM.Ty.extractelement (l := 16) (e := .bitvec (.concrete 8)) (V ⟨16, rfl⟩) (V ⟨146, rfl⟩)
  let v1 := LLVM.Ty.extractelement (l := 16) (e := .bitvec (.concrete 8)) (V ⟨16, rfl⟩) (V ⟨126, rfl⟩)
  let v2 := LLVM.shl v1 (V ⟨105, rfl⟩) {nsw := true, nuw := true}
  let v3 := LLVM.or v2 v0 {«disjoint» := true}
  let v4 := LLVM.Ty.extractelement (l := 16) (e := .bitvec (.concrete 8)) (V ⟨16, rfl⟩) (V ⟨130, rfl⟩)
  let v5 := LLVM.shl v4 (V ⟨104, rfl⟩) {nsw := true, nuw := true}
  let v6 := LLVM.or v5 v3 {«disjoint» := true}
  let v7 := LLVM.Ty.extractelement (l := 16) (e := .bitvec (.concrete 8)) (V ⟨16, rfl⟩) (V ⟨103, rfl⟩)
  let v8 := LLVM.shl v7 (V ⟨102, rfl⟩) {nsw := true, nuw := true}
  let v9 := LLVM.or v8 v6 {«disjoint» := true}
  let v10 := LLVM.Ty.extractelement (l := 16) (e := .bitvec (.concrete 8)) (V ⟨16, rfl⟩) (V ⟨101, rfl⟩)
  let v11 := LLVM.shl v10 (V ⟨100, rfl⟩) {nsw := true, nuw := true}
  let v12 := LLVM.or v11 v9 {«disjoint» := true}
  let v13 := LLVM.Ty.extractelement (l := 16) (e := .bitvec (.concrete 8)) (V ⟨16, rfl⟩) (V ⟨99, rfl⟩)
  let v14 := LLVM.shl v13 (V ⟨98, rfl⟩) {nsw := true, nuw := true}
  let v15 := LLVM.or v14 v12
  let v16 := LLVM.Ty.extractelement (l := 16) (e := .bitvec (.concrete 8)) (V ⟨16, rfl⟩) (V ⟨97, rfl⟩)
  let v17 := LLVM.shl v16 (V ⟨96, rfl⟩) {nsw := true, nuw := true}
  let v18 := LLVM.or v17 v15
  let v19 := LLVM.Ty.extractelement (l := 16) (e := .bitvec (.concrete 8)) (V ⟨16, rfl⟩) (V ⟨106, rfl⟩)
  let v20 := LLVM.shl v19 (V ⟨95, rfl⟩) {nsw := false, nuw := true}
  let v21 := LLVM.or v20 v18
  let v22 := LLVM.zext 16 v21
  let v23 := LLVM.Ty.extractelement (l := 16) (e := .bitvec (.concrete 8)) (V ⟨16, rfl⟩) (V ⟨124, rfl⟩)
  let v24 := LLVM.zext 16 v23 {«nneg» := true}
  let v25 := LLVM.shl v24 (V ⟨94, rfl⟩) {nsw := true, nuw := true}
  let v26 := LLVM.or v25 v22 {«disjoint» := true}
  let v27 := LLVM.Ty.extractelement (l := 16) (e := .bitvec (.concrete 8)) (V ⟨16, rfl⟩) (V ⟨93, rfl⟩)
  let v28 := LLVM.zext 16 v27 {«nneg» := true}
  let v29 := LLVM.shl v28 (V ⟨92, rfl⟩) {nsw := true, nuw := true}
  let v30 := LLVM.or v29 v26 {«disjoint» := true}
  let v31 := LLVM.Ty.extractelement (l := 16) (e := .bitvec (.concrete 8)) (V ⟨16, rfl⟩) (V ⟨91, rfl⟩)
  let v32 := LLVM.zext 16 v31 {«nneg» := true}
  let v33 := LLVM.shl v32 (V ⟨90, rfl⟩) {nsw := true, nuw := true}
  let v34 := LLVM.or v33 v30 {«disjoint» := true}
  let v35 := LLVM.Ty.extractelement (l := 16) (e := .bitvec (.concrete 8)) (V ⟨16, rfl⟩) (V ⟨89, rfl⟩)
  let v36 := LLVM.zext 16 v35 {«nneg» := true}
  let v37 := LLVM.shl v36 (V ⟨88, rfl⟩) {nsw := true, nuw := true}
  let v38 := LLVM.or v37 v34
  let v39 := LLVM.Ty.extractelement (l := 16) (e := .bitvec (.concrete 8)) (V ⟨16, rfl⟩) (V ⟨87, rfl⟩)
  let v40 := LLVM.zext 16 v39 {«nneg» := true}
  let v41 := LLVM.shl v40 (V ⟨86, rfl⟩) {nsw := true, nuw := true}
  let v42 := LLVM.or v41 v38
  let v43 := LLVM.Ty.extractelement (l := 16) (e := .bitvec (.concrete 8)) (V ⟨16, rfl⟩) (V ⟨85, rfl⟩)
  let v44 := LLVM.zext 16 v43 {«nneg» := true}
  let v45 := LLVM.shl v44 (V ⟨84, rfl⟩) {nsw := true, nuw := true}
  let v46 := LLVM.or v45 v42
  let v47 := LLVM.Ty.extractelement (l := 16) (e := .bitvec (.concrete 8)) (V ⟨16, rfl⟩) (V ⟨83, rfl⟩)
  let v48 := LLVM.zext 16 v47 {«nneg» := true}
  let v49 := LLVM.shl v48 (V ⟨82, rfl⟩) {nsw := true, nuw := true}
  let v50 := LLVM.or v49 v46
  let v51 := LLVM.Ty.extractelement (l := 16) (e := .bitvec (.concrete 8)) (V ⟨16, rfl⟩) (V ⟨81, rfl⟩)
  let v52 := LLVM.zext 16 v51 {«nneg» := true}
  let v53 := LLVM.shl v52 (V ⟨80, rfl⟩) {nsw := false, nuw := true}
  let v54 := LLVM.or v53 v50
  let v55 := bitcast (.bitvec (.concrete 16)) (.vector 16 (.bitvec (.concrete 1))) v54
  let v56 := xor16 (V ⟨5, rfl⟩) (V ⟨15, rfl⟩)
  let v57 := vselect v55 v56 (V ⟨17, rfl⟩)
  let v58 := xor16 (V ⟨1, rfl⟩) (V ⟨11, rfl⟩)
  let v59 := vselect v55 v58 (V ⟨18, rfl⟩)
  let v60 := xor16 (V ⟨13, rfl⟩) (V ⟨7, rfl⟩)
  let v61 := vselect v55 v60 (V ⟨19, rfl⟩)
  let v62 := xor16 (V ⟨9, rfl⟩) (V ⟨3, rfl⟩)
  let v63 := vselect v55 v62 (V ⟨20, rfl⟩)
  let v64 := xor16 (V ⟨10, rfl⟩) (V ⟨0, rfl⟩)
  let v65 := vselect v55 v64 (V ⟨21, rfl⟩)
  let v66 := xor16 (V ⟨6, rfl⟩) (V ⟨12, rfl⟩)
  let v67 := vselect v55 v66 (V ⟨22, rfl⟩)
  let v68 := xor16 (V ⟨2, rfl⟩) (V ⟨8, rfl⟩)
  let v69 := vselect v55 v68 (V ⟨23, rfl⟩)
  let v70 := xor16 (V ⟨14, rfl⟩) (V ⟨4, rfl⟩)
  let v71 := vselect v55 v70 (V ⟨24, rfl⟩)
  let v72 := bitcast (.vector 16 (.bitvec (.concrete 8))) (.vector 128 (.bitvec (.concrete 1))) (V ⟨16, rfl⟩)
  let v73 := LLVM.Ty.extractelement (l := 128) (e := .bitvec (.concrete 1)) v72 (V ⟨146, rfl⟩)
  let v74 := LLVM.add (V ⟨25, rfl⟩) (V ⟨161, rfl⟩) {nsw := true, nuw := true}
  let v75 := LLVM.Ty.insertelement (l := 8) (e := .bitvec (.concrete 64)) (V ⟨41, rfl⟩) v74 (V ⟨146, rfl⟩)
  let v76 := vselectScalar v73 v75 (V ⟨41, rfl⟩)
  let v77 := LLVM.select v73 v74 (V ⟨25, rfl⟩)
  let v78 := bitcast (.vector 16 (.bitvec (.concrete 8))) (.vector 128 (.bitvec (.concrete 1))) (V ⟨16, rfl⟩)
  let v79 := LLVM.Ty.extractelement (l := 128) (e := .bitvec (.concrete 1)) v78 (V ⟨124, rfl⟩)
  let v80 := LLVM.add (V ⟨26, rfl⟩) (V ⟨161, rfl⟩) {nsw := true, nuw := true}
  let v81 := LLVM.Ty.insertelement (l := 8) (e := .bitvec (.concrete 64)) v76 v80 (V ⟨126, rfl⟩)
  let v82 := vselectScalar v79 v81 v76
  let v83 := LLVM.select v79 v80 (V ⟨26, rfl⟩)
  let v84 := LLVM.trunc 1 v4 {nsw := false, nuw := true}
  let v85 := LLVM.add (V ⟨27, rfl⟩) (V ⟨161, rfl⟩) {nsw := true, nuw := true}
  let v86 := LLVM.Ty.insertelement (l := 8) (e := .bitvec (.concrete 64)) v82 v85 (V ⟨130, rfl⟩)
  let v87 := vselectScalar v84 v86 v82
  let v88 := LLVM.select v84 v85 (V ⟨27, rfl⟩)
  let v89 := LLVM.trunc 1 v7 {nsw := false, nuw := true}
  let v90 := LLVM.add (V ⟨28, rfl⟩) (V ⟨161, rfl⟩) {nsw := true, nuw := true}
  let v91 := LLVM.Ty.insertelement (l := 8) (e := .bitvec (.concrete 64)) v87 v90 (V ⟨103, rfl⟩)
  let v92 := vselectScalar v89 v91 v87
  let v93 := LLVM.select v89 v90 (V ⟨28, rfl⟩)
  let v94 := LLVM.trunc 1 v10 {nsw := false, nuw := true}
  let v95 := LLVM.add (V ⟨29, rfl⟩) (V ⟨161, rfl⟩) {nsw := true, nuw := true}
  let v96 := LLVM.Ty.insertelement (l := 8) (e := .bitvec (.concrete 64)) v92 v95 (V ⟨101, rfl⟩)
  let v97 := vselectScalar v94 v96 v92
  let v98 := LLVM.select v94 v95 (V ⟨29, rfl⟩)
  let v99 := LLVM.trunc 1 v13 {nsw := false, nuw := true}
  let v100 := LLVM.add (V ⟨30, rfl⟩) (V ⟨161, rfl⟩) {nsw := true, nuw := true}
  let v101 := LLVM.Ty.insertelement (l := 8) (e := .bitvec (.concrete 64)) v97 v100 (V ⟨99, rfl⟩)
  let v102 := vselectScalar v99 v101 v97
  let v103 := LLVM.select v99 v100 (V ⟨30, rfl⟩)
  let v104 := LLVM.trunc 1 v16 {nsw := false, nuw := true}
  let v105 := LLVM.add (V ⟨31, rfl⟩) (V ⟨161, rfl⟩) {nsw := true, nuw := true}
  let v106 := LLVM.Ty.insertelement (l := 8) (e := .bitvec (.concrete 64)) v102 v105 (V ⟨97, rfl⟩)
  let v107 := vselectScalar v104 v106 v102
  let v108 := LLVM.select v104 v105 (V ⟨31, rfl⟩)
  let v109 := LLVM.trunc 1 v19 {nsw := false, nuw := true}
  let v110 := LLVM.add (V ⟨32, rfl⟩) (V ⟨161, rfl⟩) {nsw := false, nuw := false}
  let v111 := LLVM.Ty.insertelement (l := 8) (e := .bitvec (.concrete 64)) v107 v110 (V ⟨106, rfl⟩)
  let v112 := vselectScalar v109 v111 v107
  let v113 := LLVM.select v109 v110 (V ⟨32, rfl⟩)
  let v114 := LLVM.trunc 1 v23 {nsw := false, nuw := true}
  let v115 := LLVM.add (V ⟨33, rfl⟩) (V ⟨161, rfl⟩) {nsw := false, nuw := false}
  let v116 := LLVM.Ty.insertelement (l := 8) (e := .bitvec (.concrete 64)) (V ⟨42, rfl⟩) v115 (V ⟨146, rfl⟩)
  let v117 := vselectScalar v114 v116 (V ⟨42, rfl⟩)
  let v118 := LLVM.select v114 v115 (V ⟨33, rfl⟩)
  let v119 := LLVM.trunc 1 v27 {nsw := false, nuw := true}
  let v120 := LLVM.add (V ⟨34, rfl⟩) (V ⟨161, rfl⟩) {nsw := false, nuw := false}
  let v121 := LLVM.Ty.insertelement (l := 8) (e := .bitvec (.concrete 64)) v117 v120 (V ⟨126, rfl⟩)
  let v122 := vselectScalar v119 v121 v117
  let v123 := LLVM.select v119 v120 (V ⟨34, rfl⟩)
  let v124 := LLVM.trunc 1 v31 {nsw := false, nuw := true}
  let v125 := LLVM.add (V ⟨35, rfl⟩) (V ⟨161, rfl⟩) {nsw := false, nuw := false}
  let v126 := LLVM.Ty.insertelement (l := 8) (e := .bitvec (.concrete 64)) v122 v125 (V ⟨130, rfl⟩)
  let v127 := vselectScalar v124 v126 v122
  let v128 := LLVM.select v124 v125 (V ⟨35, rfl⟩)
  let v129 := LLVM.trunc 1 v35 {nsw := false, nuw := true}
  let v130 := LLVM.add (V ⟨36, rfl⟩) (V ⟨161, rfl⟩) {nsw := false, nuw := false}
  let v131 := LLVM.Ty.insertelement (l := 8) (e := .bitvec (.concrete 64)) v127 v130 (V ⟨103, rfl⟩)
  let v132 := vselectScalar v129 v131 v127
  let v133 := LLVM.select v129 v130 (V ⟨36, rfl⟩)
  let v134 := LLVM.trunc 1 v39 {nsw := false, nuw := true}
  let v135 := LLVM.add (V ⟨37, rfl⟩) (V ⟨161, rfl⟩) {nsw := false, nuw := false}
  let v136 := LLVM.Ty.insertelement (l := 8) (e := .bitvec (.concrete 64)) v132 v135 (V ⟨101, rfl⟩)
  let v137 := vselectScalar v134 v136 v132
  let v138 := LLVM.select v134 v135 (V ⟨37, rfl⟩)
  let v139 := LLVM.trunc 1 v43 {nsw := false, nuw := true}
  let v140 := LLVM.add (V ⟨38, rfl⟩) (V ⟨161, rfl⟩) {nsw := false, nuw := false}
  let v141 := LLVM.Ty.insertelement (l := 8) (e := .bitvec (.concrete 64)) v137 v140 (V ⟨99, rfl⟩)
  let v142 := vselectScalar v139 v141 v137
  let v143 := LLVM.select v139 v140 (V ⟨38, rfl⟩)
  let v144 := LLVM.trunc 1 v47 {nsw := false, nuw := true}
  let v145 := LLVM.add (V ⟨39, rfl⟩) (V ⟨161, rfl⟩) {nsw := false, nuw := false}
  let v146 := LLVM.Ty.insertelement (l := 8) (e := .bitvec (.concrete 64)) v142 v145 (V ⟨97, rfl⟩)
  let v147 := vselectScalar v144 v146 v142
  let v148 := LLVM.select v144 v145 (V ⟨39, rfl⟩)
  let v149 := LLVM.trunc 1 v51 {nsw := false, nuw := true}
  let v150 := LLVM.add (V ⟨40, rfl⟩) (V ⟨161, rfl⟩) {nsw := false, nuw := false}
  let v151 := LLVM.Ty.insertelement (l := 8) (e := .bitvec (.concrete 64)) v147 v150 (V ⟨106, rfl⟩)
  let v152 := vselectScalar v149 v151 v147
  let v153 := LLVM.select v149 v150 (V ⟨40, rfl⟩)
  (Ctxt.Valuation.ofHVector (types := outputTypes16) (
    v153 ::ₕ
    v152 ::ₕ
    v151 ::ₕ
    v150 ::ₕ
    v149 ::ₕ
    v148 ::ₕ
    v147 ::ₕ
    v146 ::ₕ
    v145 ::ₕ
    v144 ::ₕ
    v143 ::ₕ
    v142 ::ₕ
    v141 ::ₕ
    v140 ::ₕ
    v139 ::ₕ
    v138 ::ₕ
    v137 ::ₕ
    v136 ::ₕ
    v135 ::ₕ
    v134 ::ₕ
    v133 ::ₕ
    v132 ::ₕ
    v131 ::ₕ
    v130 ::ₕ
    v129 ::ₕ
    v128 ::ₕ
    v127 ::ₕ
    v126 ::ₕ
    v125 ::ₕ
    v124 ::ₕ
    v123 ::ₕ
    v122 ::ₕ
    v121 ::ₕ
    v120 ::ₕ
    v119 ::ₕ
    v118 ::ₕ
    v117 ::ₕ
    v116 ::ₕ
    v115 ::ₕ
    v114 ::ₕ
    v113 ::ₕ
    v112 ::ₕ
    v111 ::ₕ
    v110 ::ₕ
    v109 ::ₕ
    v108 ::ₕ
    v107 ::ₕ
    v106 ::ₕ
    v105 ::ₕ
    v104 ::ₕ
    v103 ::ₕ
    v102 ::ₕ
    v101 ::ₕ
    v100 ::ₕ
    v99 ::ₕ
    v98 ::ₕ
    v97 ::ₕ
    v96 ::ₕ
    v95 ::ₕ
    v94 ::ₕ
    v93 ::ₕ
    v92 ::ₕ
    v91 ::ₕ
    v90 ::ₕ
    v89 ::ₕ
    v88 ::ₕ
    v87 ::ₕ
    v86 ::ₕ
    v85 ::ₕ
    v84 ::ₕ
    v83 ::ₕ
    v82 ::ₕ
    v81 ::ₕ
    v80 ::ₕ
    v79 ::ₕ
    v78 ::ₕ
    v77 ::ₕ
    v76 ::ₕ
    v75 ::ₕ
    v74 ::ₕ
    v73 ::ₕ
    v72 ::ₕ
    v71 ::ₕ
    v70 ::ₕ
    v69 ::ₕ
    v68 ::ₕ
    v67 ::ₕ
    v66 ::ₕ
    v65 ::ₕ
    v64 ::ₕ
    v63 ::ₕ
    v62 ::ₕ
    v61 ::ₕ
    v60 ::ₕ
    v59 ::ₕ
    v58 ::ₕ
    v57 ::ₕ
    v56 ::ₕ
    v55 ::ₕ
    v54 ::ₕ
    v53 ::ₕ
    v52 ::ₕ
    v51 ::ₕ
    v50 ::ₕ
    v49 ::ₕ
    v48 ::ₕ
    v47 ::ₕ
    v46 ::ₕ
    v45 ::ₕ
    v44 ::ₕ
    v43 ::ₕ
    v42 ::ₕ
    v41 ::ₕ
    v40 ::ₕ
    v39 ::ₕ
    v38 ::ₕ
    v37 ::ₕ
    v36 ::ₕ
    v35 ::ₕ
    v34 ::ₕ
    v33 ::ₕ
    v32 ::ₕ
    v31 ::ₕ
    v30 ::ₕ
    v29 ::ₕ
    v28 ::ₕ
    v27 ::ₕ
    v26 ::ₕ
    v25 ::ₕ
    v24 ::ₕ
    v23 ::ₕ
    v22 ::ₕ
    v21 ::ₕ
    v20 ::ₕ
    v19 ::ₕ
    v18 ::ₕ
    v17 ::ₕ
    v16 ::ₕ
    v15 ::ₕ
    v14 ::ₕ
    v13 ::ₕ
    v12 ::ₕ
    v11 ::ₕ
    v10 ::ₕ
    v9 ::ₕ
    v8 ::ₕ
    v7 ::ₕ
    v6 ::ₕ
    v5 ::ₕ
    v4 ::ₕ
    v3 ::ₕ
    v2 ::ₕ
    v1 ::ₕ
    v0 ::ₕ .nil) ++ V,
    .inr ⟨0, rfl, [v152, v112, v153, v148, v143, v138, v133, v128, v123, v118, v113, v108, v103, v98, v93, v88, v83, v77, v71, v69, v67, v65, v63, v61, v59, v57]ₕ⟩)

/-- Actual AVX512 block execution, for arbitrary poison-aware inputs. -/
theorem update16_continue {α : Type} (V : Input16.Valuation) (s : GlobalState)
    (k : Output16.Valuation ×
      (HVector TyDenote.toType ([] : List SLLVM.Ty) ⊕ SuccArgs agave_batch_16.cfgSigs) → EffectM α) :
    StateT.run (agave_batch_16.cfgBlock_8.denote V >>= k) s =
      StateT.run (k (result16 V)) s := by
  denote_step_all v
  simp only [BlockCom.run_bind_denote_lifetime]
  denote_eval v 0 153
  subst hv0 hv1 hv2 hv3 hv4 hv5 hv6 hv7 hv8 hv9 hv10 hv11 hv12 hv13 hv14 hv15 hv16 hv17 hv18 hv19 hv20 hv21 hv22 hv23 hv24 hv25 hv26 hv27 hv28 hv29 hv30 hv31 hv32 hv33 hv34 hv35 hv36 hv37 hv38 hv39 hv40 hv41 hv42 hv43 hv44 hv45 hv46 hv47 hv48 hv49 hv50 hv51 hv52 hv53 hv54 hv55 hv56 hv57 hv58 hv59 hv60 hv61 hv62 hv63 hv64 hv65 hv66 hv67 hv68 hv69 hv70 hv71 hv72 hv73 hv74 hv75 hv76 hv77 hv78 hv79 hv80 hv81 hv82 hv83 hv84 hv85 hv86 hv87 hv88 hv89 hv90 hv91 hv92 hv93 hv94 hv95 hv96 hv97 hv98 hv99 hv100 hv101 hv102 hv103 hv104 hv105 hv106 hv107 hv108 hv109 hv110 hv111 hv112 hv113 hv114 hv115 hv116 hv117 hv118 hv119 hv120 hv121 hv122 hv123 hv124 hv125 hv126 hv127 hv128 hv129 hv130 hv131 hv132 hv133 hv134 hv135 hv136 hv137 hv138 hv139 hv140 hv141 hv142 hv143 hv144 hv145 hv146 hv147 hv148 hv149 hv150 hv151 hv152 hv153
  simp only [BlockCom.denote, Terminator.denote, Target.denote]
  simp only [result16, Ctxt.Valuation.ofHVector_cons, Ctxt.Valuation.ofHVector_nil,
    Ctxt.Valuation.cons_append, Ctxt.Valuation.nil_append, pure_bind]
  simp only [xor16, InstCombine.binaryDenote, Fin.getElem_fin]
  rfl

/-- Exact SSA valuation and backedge, with unchanged memory. -/
theorem update16_denote (V : Input16.Valuation) (s : GlobalState) :
    StateT.run (agave_batch_16.cfgBlock_8.denote V) s = .value (result16 V, s) := by
  simpa only [bind_pure, EffectM.run_pure] using update16_continue V s pure

end AgaveLatticeHash.MLIR.BatchUpdate16
