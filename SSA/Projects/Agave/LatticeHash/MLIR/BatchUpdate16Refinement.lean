/- Released under Apache 2.0 license as described in the file LICENSE. -/
import SSA.Projects.Agave.LatticeHash.MLIR.BatchUpdate16
import SSA.Projects.Agave.LatticeHash.MLIR.BatchOffsets16
import SSA.Projects.Agave.LatticeHash.MLIR.BatchProof16
import SSA.Projects.Agave.LatticeHash.MLIR.BatchMask16

namespace AgaveLatticeHash.MLIR.BatchUpdate16
open LeanMLIR SLLVM Firedancer
open InstCombine (LLVM)
set_option maxRecDepth 8192
set_option maxHeartbeats 2400000

noncomputable def mask16 (V : Input16.Valuation) : Vector (LLVM.IntW 1) 16 :=
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
  v55

noncomputable def target16 (V : Input16.Valuation) : SuccArgs agave_batch_16.cfgSigs :=
  let v0 := LLVM.Ty.extractelement (l := 16) (e := .bitvec (.concrete 8)) (V ⟨16, rfl⟩) (V ⟨146, rfl⟩)
  let v1 := LLVM.Ty.extractelement (l := 16) (e := .bitvec (.concrete 8)) (V ⟨16, rfl⟩) (V ⟨126, rfl⟩)
  let v4 := LLVM.Ty.extractelement (l := 16) (e := .bitvec (.concrete 8)) (V ⟨16, rfl⟩) (V ⟨130, rfl⟩)
  let v7 := LLVM.Ty.extractelement (l := 16) (e := .bitvec (.concrete 8)) (V ⟨16, rfl⟩) (V ⟨103, rfl⟩)
  let v10 := LLVM.Ty.extractelement (l := 16) (e := .bitvec (.concrete 8)) (V ⟨16, rfl⟩) (V ⟨101, rfl⟩)
  let v13 := LLVM.Ty.extractelement (l := 16) (e := .bitvec (.concrete 8)) (V ⟨16, rfl⟩) (V ⟨99, rfl⟩)
  let v16 := LLVM.Ty.extractelement (l := 16) (e := .bitvec (.concrete 8)) (V ⟨16, rfl⟩) (V ⟨97, rfl⟩)
  let v19 := LLVM.Ty.extractelement (l := 16) (e := .bitvec (.concrete 8)) (V ⟨16, rfl⟩) (V ⟨106, rfl⟩)
  let v23 := LLVM.Ty.extractelement (l := 16) (e := .bitvec (.concrete 8)) (V ⟨16, rfl⟩) (V ⟨124, rfl⟩)
  let v27 := LLVM.Ty.extractelement (l := 16) (e := .bitvec (.concrete 8)) (V ⟨16, rfl⟩) (V ⟨93, rfl⟩)
  let v31 := LLVM.Ty.extractelement (l := 16) (e := .bitvec (.concrete 8)) (V ⟨16, rfl⟩) (V ⟨91, rfl⟩)
  let v35 := LLVM.Ty.extractelement (l := 16) (e := .bitvec (.concrete 8)) (V ⟨16, rfl⟩) (V ⟨89, rfl⟩)
  let v39 := LLVM.Ty.extractelement (l := 16) (e := .bitvec (.concrete 8)) (V ⟨16, rfl⟩) (V ⟨87, rfl⟩)
  let v43 := LLVM.Ty.extractelement (l := 16) (e := .bitvec (.concrete 8)) (V ⟨16, rfl⟩) (V ⟨85, rfl⟩)
  let v47 := LLVM.Ty.extractelement (l := 16) (e := .bitvec (.concrete 8)) (V ⟨16, rfl⟩) (V ⟨83, rfl⟩)
  let v51 := LLVM.Ty.extractelement (l := 16) (e := .bitvec (.concrete 8)) (V ⟨16, rfl⟩) (V ⟨81, rfl⟩)
  let v56 := xor16 (V ⟨5, rfl⟩) (V ⟨15, rfl⟩)
  let v57 := vselect (mask16 V) v56 (V ⟨17, rfl⟩)
  let v58 := xor16 (V ⟨1, rfl⟩) (V ⟨11, rfl⟩)
  let v59 := vselect (mask16 V) v58 (V ⟨18, rfl⟩)
  let v60 := xor16 (V ⟨13, rfl⟩) (V ⟨7, rfl⟩)
  let v61 := vselect (mask16 V) v60 (V ⟨19, rfl⟩)
  let v62 := xor16 (V ⟨9, rfl⟩) (V ⟨3, rfl⟩)
  let v63 := vselect (mask16 V) v62 (V ⟨20, rfl⟩)
  let v64 := xor16 (V ⟨10, rfl⟩) (V ⟨0, rfl⟩)
  let v65 := vselect (mask16 V) v64 (V ⟨21, rfl⟩)
  let v66 := xor16 (V ⟨6, rfl⟩) (V ⟨12, rfl⟩)
  let v67 := vselect (mask16 V) v66 (V ⟨22, rfl⟩)
  let v68 := xor16 (V ⟨2, rfl⟩) (V ⟨8, rfl⟩)
  let v69 := vselect (mask16 V) v68 (V ⟨23, rfl⟩)
  let v70 := xor16 (V ⟨14, rfl⟩) (V ⟨4, rfl⟩)
  let v71 := vselect (mask16 V) v70 (V ⟨24, rfl⟩)
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
  ⟨0, rfl, [v152, v112, v153, v148, v143, v138, v133, v128, v123, v118, v113, v108, v103, v98, v93, v88, v83, v77, v71, v69, v67, v65, v63, v61, v59, v57]ₕ⟩

theorem result16_snd (V : Input16.Valuation) : (result16 V).snd = .inr (target16 V) := rfl

open Blake3Compression in
structure Env16 (V : Input16.Valuation) (active : Fin 16 → Bool)
    (old x y : CV (Lanes 16)) (offsets : Vector (BitVec 64) 16) : Prop where
  bytes : V ⟨16, rfl⟩ = activeBytes16 active
  idx0 : V ⟨146, rfl⟩ = .value 0#64
  idx1 : V ⟨126, rfl⟩ = .value 1#64
  idx2 : V ⟨130, rfl⟩ = .value 2#64
  idx3 : V ⟨103, rfl⟩ = .value 3#64
  idx4 : V ⟨101, rfl⟩ = .value 4#64
  idx5 : V ⟨99, rfl⟩ = .value 5#64
  idx6 : V ⟨97, rfl⟩ = .value 6#64
  idx7 : V ⟨106, rfl⟩ = .value 7#64
  idx8 : V ⟨124, rfl⟩ = .value 8#64
  idx9 : V ⟨93, rfl⟩ = .value 9#64
  idx10 : V ⟨91, rfl⟩ = .value 10#64
  idx11 : V ⟨89, rfl⟩ = .value 11#64
  idx12 : V ⟨87, rfl⟩ = .value 12#64
  idx13 : V ⟨85, rfl⟩ = .value 13#64
  idx14 : V ⟨83, rfl⟩ = .value 14#64
  idx15 : V ⟨81, rfl⟩ = .value 15#64
  shift1 : V ⟨105, rfl⟩ = .value 1#8
  shift2 : V ⟨104, rfl⟩ = .value 2#8
  shift3 : V ⟨102, rfl⟩ = .value 3#8
  shift4 : V ⟨100, rfl⟩ = .value 4#8
  shift5 : V ⟨98, rfl⟩ = .value 5#8
  shift6 : V ⟨96, rfl⟩ = .value 6#8
  shift7 : V ⟨95, rfl⟩ = .value 7#8
  shift8 : V ⟨94, rfl⟩ = .value 8#16
  shift9 : V ⟨92, rfl⟩ = .value 9#16
  shift10 : V ⟨90, rfl⟩ = .value 10#16
  shift11 : V ⟨88, rfl⟩ = .value 11#16
  shift12 : V ⟨86, rfl⟩ = .value 12#16
  shift13 : V ⟨84, rfl⟩ = .value 13#16
  shift14 : V ⟨82, rfl⟩ = .value 14#16
  shift15 : V ⟨80, rfl⟩ = .value 15#16
  step : V ⟨161, rfl⟩ = .value 64#64
  off0 : V ⟨25, rfl⟩ = .value offsets[0]
  off1 : V ⟨26, rfl⟩ = .value offsets[1]
  off2 : V ⟨27, rfl⟩ = .value offsets[2]
  off3 : V ⟨28, rfl⟩ = .value offsets[3]
  off4 : V ⟨29, rfl⟩ = .value offsets[4]
  off5 : V ⟨30, rfl⟩ = .value offsets[5]
  off6 : V ⟨31, rfl⟩ = .value offsets[6]
  off7 : V ⟨32, rfl⟩ = .value offsets[7]
  off8 : V ⟨33, rfl⟩ = .value offsets[8]
  off9 : V ⟨34, rfl⟩ = .value offsets[9]
  off10 : V ⟨35, rfl⟩ = .value offsets[10]
  off11 : V ⟨36, rfl⟩ = .value offsets[11]
  off12 : V ⟨37, rfl⟩ = .value offsets[12]
  off13 : V ⟨38, rfl⟩ = .value offsets[13]
  off14 : V ⟨39, rfl⟩ = .value offsets[14]
  off15 : V ⟨40, rfl⟩ = .value offsets[15]
  low : V ⟨41, rfl⟩ = (Vector.ofFn fun i : Fin 8 => offsets[(⟨i.val, by omega⟩ : Fin 16)]).map PoisonOr.value
  high : V ⟨42, rfl⟩ = (Vector.ofFn fun i : Fin 8 => offsets[(⟨i.val+8, by omega⟩ : Fin 16)]).map PoisonOr.value
  old0 : V ⟨17, rfl⟩ = (Vector.ofFn (old 0)).map PoisonOr.value
  x0 : V ⟨5, rfl⟩ = (Vector.ofFn (x 0)).map PoisonOr.value
  y0 : V ⟨15, rfl⟩ = (Vector.ofFn (y 0)).map PoisonOr.value
  old1 : V ⟨18, rfl⟩ = (Vector.ofFn (old 1)).map PoisonOr.value
  x1 : V ⟨1, rfl⟩ = (Vector.ofFn (x 1)).map PoisonOr.value
  y1 : V ⟨11, rfl⟩ = (Vector.ofFn (y 1)).map PoisonOr.value
  old2 : V ⟨19, rfl⟩ = (Vector.ofFn (old 2)).map PoisonOr.value
  x2 : V ⟨13, rfl⟩ = (Vector.ofFn (x 2)).map PoisonOr.value
  y2 : V ⟨7, rfl⟩ = (Vector.ofFn (y 2)).map PoisonOr.value
  old3 : V ⟨20, rfl⟩ = (Vector.ofFn (old 3)).map PoisonOr.value
  x3 : V ⟨9, rfl⟩ = (Vector.ofFn (x 3)).map PoisonOr.value
  y3 : V ⟨3, rfl⟩ = (Vector.ofFn (y 3)).map PoisonOr.value
  old4 : V ⟨21, rfl⟩ = (Vector.ofFn (old 4)).map PoisonOr.value
  x4 : V ⟨10, rfl⟩ = (Vector.ofFn (x 4)).map PoisonOr.value
  y4 : V ⟨0, rfl⟩ = (Vector.ofFn (y 4)).map PoisonOr.value
  old5 : V ⟨22, rfl⟩ = (Vector.ofFn (old 5)).map PoisonOr.value
  x5 : V ⟨6, rfl⟩ = (Vector.ofFn (x 5)).map PoisonOr.value
  y5 : V ⟨12, rfl⟩ = (Vector.ofFn (y 5)).map PoisonOr.value
  old6 : V ⟨23, rfl⟩ = (Vector.ofFn (old 6)).map PoisonOr.value
  x6 : V ⟨2, rfl⟩ = (Vector.ofFn (x 6)).map PoisonOr.value
  y6 : V ⟨8, rfl⟩ = (Vector.ofFn (y 6)).map PoisonOr.value
  old7 : V ⟨24, rfl⟩ = (Vector.ofFn (old 7)).map PoisonOr.value
  x7 : V ⟨14, rfl⟩ = (Vector.ofFn (x 7)).map PoisonOr.value
  y7 : V ⟨4, rfl⟩ = (Vector.ofFn (y 7)).map PoisonOr.value

open Blake3Compression in
theorem mask16_eq (V : Input16.Valuation) (active : Fin 16 → Bool)
    (old x y : CV (Lanes 16)) (offsets : Vector (BitVec 64) 16)
    (hV : Env16 V active old x y offsets) :
    mask16 V = Vector.ofFn fun i => PoisonOr.value (BitVec.ofBool (active i)) := by
  have hm := BatchMask16.packMask16_exact active
  simp only [mask16, hV.bytes, hV.idx0, hV.idx1, hV.idx2, hV.idx3, hV.idx4, hV.idx5, hV.idx6, hV.idx7, hV.idx8, hV.idx9, hV.idx10, hV.idx11, hV.idx12, hV.idx13, hV.idx14, hV.idx15, hV.shift1, hV.shift2, hV.shift3, hV.shift4, hV.shift5, hV.shift6, hV.shift7, hV.shift8, hV.shift9, hV.shift10, hV.shift11, hV.shift12, hV.shift13, hV.shift14, hV.shift15, activeBytes16,
    BatchMask16.packMask16, BatchMask16.packMaskWord16]
  convert hm using 1
  rfl

theorem xor16_values (a b : Fin 16 → BitVec 32) :
    xor16 ((Vector.ofFn a).map PoisonOr.value) ((Vector.ofFn b).map PoisonOr.value) =
      (Vector.ofFn fun i => a i ^^^ b i).map PoisonOr.value := by
  apply Vector.ext
  intro i hi
  simp [xor16, LLVM.xor, Fin.getElem_fin]
  rfl

theorem select16_values (active : Fin 16 → Bool) (a b : Fin 16 → BitVec 32) :
    vselect (Vector.ofFn fun i => PoisonOr.value (BitVec.ofBool (active i)))
      ((Vector.ofFn a).map PoisonOr.value) ((Vector.ofFn b).map PoisonOr.value) =
      Vector.ofFn (fun i => PoisonOr.value (if active i then a i else b i)) := by
  apply Vector.ext
  intro i hi
  simp only [vselect, Vector.getElem_ofFn, Fin.getElem_fin, Vector.getElem_map, select_value]

theorem add_values (a b : BitVec w) :
    LLVM.add (.value a) (.value b) = PoisonOr.value (a+b) := rfl

open Blake3Compression in
theorem target16_eq (V : Input16.Valuation) (active : Fin 16 → Bool)
    (old x y : CV (Lanes 16)) (offsets : Vector (BitVec 64) 16)
    (hV : Env16 V active old x y offsets)
    (hb : ∀ i : Fin 16, offsets[i].toNat ≤ 960)
    (hm : mask16 V = Vector.ofFn fun i => PoisonOr.value (BitVec.ofBool (active i))) :
    target16 V = headerTarget16
      (fun w lane => if active lane then x w lane ^^^ y w lane else old w lane)
      (Vector.ofFn fun i => if active i then offsets[i]+64 else offsets[i]) := by
  simp only [target16, hm, hV.bytes, hV.idx0, hV.idx1, hV.idx2, hV.idx3, hV.idx4, hV.idx5, hV.idx6, hV.idx7, hV.idx8, hV.idx9, hV.idx10, hV.idx11, hV.idx12, hV.idx13, hV.idx14, hV.idx15, hV.step, hV.off0, hV.off1, hV.off2, hV.off3, hV.off4, hV.off5, hV.off6, hV.off7, hV.off8, hV.off9, hV.off10, hV.off11, hV.off12, hV.off13, hV.off14, hV.off15, hV.low, hV.high, hV.old0, hV.x0, hV.y0, hV.old1, hV.x1, hV.y1, hV.old2, hV.x2, hV.y2, hV.old3, hV.x3, hV.y3, hV.old4, hV.x4, hV.y4, hV.old5, hV.x5, hV.y5, hV.old6, hV.x6, hV.y6, hV.old7, hV.x7, hV.y7]
  have hab0 : LLVM.Ty.extractelement (e := .bitvec (.concrete 1))
      (bitcast (.vector 16 (.bitvec (.concrete 8))) (.vector 128 (.bitvec (.concrete 1)))
        (activeBytes16 active)) (.value 0#64) =
      PoisonOr.value (BitVec.ofBool (active 0)) := active_bit active 0
  have hab1 : LLVM.Ty.extractelement (e := .bitvec (.concrete 1))
      (bitcast (.vector 16 (.bitvec (.concrete 8))) (.vector 128 (.bitvec (.concrete 1)))
        (activeBytes16 active)) (.value 8#64) =
      PoisonOr.value (BitVec.ofBool (active 1)) := active_bit active 1
  have hae2 : LLVM.Ty.extractelement (e := .bitvec (.concrete 8)) (activeBytes16 active)
      (.value 2#64) = PoisonOr.value ((BitVec.ofBool (active 2)).zeroExtend 8) := extract_active active 2
  have hae3 : LLVM.Ty.extractelement (e := .bitvec (.concrete 8)) (activeBytes16 active)
      (.value 3#64) = PoisonOr.value ((BitVec.ofBool (active 3)).zeroExtend 8) := extract_active active 3
  have hae4 : LLVM.Ty.extractelement (e := .bitvec (.concrete 8)) (activeBytes16 active)
      (.value 4#64) = PoisonOr.value ((BitVec.ofBool (active 4)).zeroExtend 8) := extract_active active 4
  have hae5 : LLVM.Ty.extractelement (e := .bitvec (.concrete 8)) (activeBytes16 active)
      (.value 5#64) = PoisonOr.value ((BitVec.ofBool (active 5)).zeroExtend 8) := extract_active active 5
  have hae6 : LLVM.Ty.extractelement (e := .bitvec (.concrete 8)) (activeBytes16 active)
      (.value 6#64) = PoisonOr.value ((BitVec.ofBool (active 6)).zeroExtend 8) := extract_active active 6
  have hae7 : LLVM.Ty.extractelement (e := .bitvec (.concrete 8)) (activeBytes16 active)
      (.value 7#64) = PoisonOr.value ((BitVec.ofBool (active 7)).zeroExtend 8) := extract_active active 7
  have hae8 : LLVM.Ty.extractelement (e := .bitvec (.concrete 8)) (activeBytes16 active)
      (.value 8#64) = PoisonOr.value ((BitVec.ofBool (active 8)).zeroExtend 8) := extract_active active 8
  have hae9 : LLVM.Ty.extractelement (e := .bitvec (.concrete 8)) (activeBytes16 active)
      (.value 9#64) = PoisonOr.value ((BitVec.ofBool (active 9)).zeroExtend 8) := extract_active active 9
  have hae10 : LLVM.Ty.extractelement (e := .bitvec (.concrete 8)) (activeBytes16 active)
      (.value 10#64) = PoisonOr.value ((BitVec.ofBool (active 10)).zeroExtend 8) := extract_active active 10
  have hae11 : LLVM.Ty.extractelement (e := .bitvec (.concrete 8)) (activeBytes16 active)
      (.value 11#64) = PoisonOr.value ((BitVec.ofBool (active 11)).zeroExtend 8) := extract_active active 11
  have hae12 : LLVM.Ty.extractelement (e := .bitvec (.concrete 8)) (activeBytes16 active)
      (.value 12#64) = PoisonOr.value ((BitVec.ofBool (active 12)).zeroExtend 8) := extract_active active 12
  have hae13 : LLVM.Ty.extractelement (e := .bitvec (.concrete 8)) (activeBytes16 active)
      (.value 13#64) = PoisonOr.value ((BitVec.ofBool (active 13)).zeroExtend 8) := extract_active active 13
  have hae14 : LLVM.Ty.extractelement (e := .bitvec (.concrete 8)) (activeBytes16 active)
      (.value 14#64) = PoisonOr.value ((BitVec.ofBool (active 14)).zeroExtend 8) := extract_active active 14
  have hae15 : LLVM.Ty.extractelement (e := .bitvec (.concrete 8)) (activeBytes16 active)
      (.value 15#64) = PoisonOr.value ((BitVec.ofBool (active 15)).zeroExtend 8) := extract_active active 15
  simp only [hab0, hab1, hae2, hae3, hae4, hae5, hae6, hae7, hae8, hae9, hae10, hae11, hae12, hae13, hae14, hae15, trunc_active]
  rw [add64_safe offsets[0] (hb 0), add64_safe offsets[1] (hb 1), add64_safe offsets[2] (hb 2), add64_safe offsets[3] (hb 3), add64_safe offsets[4] (hb 4), add64_safe offsets[5] (hb 5), add64_safe offsets[6] (hb 6)]
  simp only [add_values]
  rw [xor16_values (x 0) (y 0), xor16_values (x 1) (y 1), xor16_values (x 2) (y 2), xor16_values (x 3) (y 3), xor16_values (x 4) (y 4), xor16_values (x 5) (y 5), xor16_values (x 6) (y 6), xor16_values (x 7) (y 7)]
  rw [select16_values active (fun lane => x 0 lane ^^^ y 0 lane) (old 0), select16_values active (fun lane => x 1 lane ^^^ y 1 lane) (old 1), select16_values active (fun lane => x 2 lane ^^^ y 2 lane) (old 2), select16_values active (fun lane => x 3 lane ^^^ y 3 lane) (old 3), select16_values active (fun lane => x 4 lane ^^^ y 4 lane) (old 4), select16_values active (fun lane => x 5 lane ^^^ y 5 lane) (old 5), select16_values active (fun lane => x 6 lane ^^^ y 6 lane) (old 6), select16_values active (fun lane => x 7 lane ^^^ y 7 lane) (old 7)]
  have hlo :
      (let v0 := vselectScalar (.value (BitVec.ofBool (active 0)))
        (LLVM.Ty.insertelement (e := .bitvec (.concrete 64)) ((Vector.ofFn fun i : Fin 8 => offsets[(⟨i.val, by omega⟩ : Fin 16)]).map PoisonOr.value)
          (.value (offsets[0]+64)) (.value 0#64)) ((Vector.ofFn fun i : Fin 8 => offsets[(⟨i.val, by omega⟩ : Fin 16)]).map PoisonOr.value)
       let v1 := vselectScalar (.value (BitVec.ofBool (active 1)))
        (LLVM.Ty.insertelement (e := .bitvec (.concrete 64)) (v0)
          (.value (offsets[1]+64)) (.value 1#64)) (v0)
       let v2 := vselectScalar (.value (BitVec.ofBool (active 2)))
        (LLVM.Ty.insertelement (e := .bitvec (.concrete 64)) (v1)
          (.value (offsets[2]+64)) (.value 2#64)) (v1)
       let v3 := vselectScalar (.value (BitVec.ofBool (active 3)))
        (LLVM.Ty.insertelement (e := .bitvec (.concrete 64)) (v2)
          (.value (offsets[3]+64)) (.value 3#64)) (v2)
       let v4 := vselectScalar (.value (BitVec.ofBool (active 4)))
        (LLVM.Ty.insertelement (e := .bitvec (.concrete 64)) (v3)
          (.value (offsets[4]+64)) (.value 4#64)) (v3)
       let v5 := vselectScalar (.value (BitVec.ofBool (active 5)))
        (LLVM.Ty.insertelement (e := .bitvec (.concrete 64)) (v4)
          (.value (offsets[5]+64)) (.value 5#64)) (v4)
       let v6 := vselectScalar (.value (BitVec.ofBool (active 6)))
        (LLVM.Ty.insertelement (e := .bitvec (.concrete 64)) (v5)
          (.value (offsets[6]+64)) (.value 6#64)) (v5)
       let v7 := vselectScalar (.value (BitVec.ofBool (active 7)))
        (LLVM.Ty.insertelement (e := .bitvec (.concrete 64)) (v6)
          (.value (offsets[7]+64#64)) (.value 7#64)) (v6)
       v7) = Vector.ofFn (fun i : Fin 8 => PoisonOr.value
        (if active ⟨i.val, by omega⟩ then offsets[(⟨i.val, by omega⟩ : Fin 16)]+64
          else offsets[(⟨i.val, by omega⟩ : Fin 16)])) := by
    exact updateHalf_eq (Vector.ofFn fun i : Fin 8 => offsets[(⟨i.val, by omega⟩ : Fin 16)])
      (Vector.ofFn fun i : Fin 8 => offsets[(⟨i.val, by omega⟩ : Fin 16)] + 64) (fun i : Fin 8 => active ⟨i.val, by omega⟩)
  have hhi :
      (let v0 := vselectScalar (.value (BitVec.ofBool (active 8)))
        (LLVM.Ty.insertelement (e := .bitvec (.concrete 64)) ((Vector.ofFn fun i : Fin 8 => offsets[(⟨i.val+8, by omega⟩ : Fin 16)]).map PoisonOr.value)
          (.value (offsets[8]+64#64)) (.value 0#64)) ((Vector.ofFn fun i : Fin 8 => offsets[(⟨i.val+8, by omega⟩ : Fin 16)]).map PoisonOr.value)
       let v1 := vselectScalar (.value (BitVec.ofBool (active 9)))
        (LLVM.Ty.insertelement (e := .bitvec (.concrete 64)) (v0)
          (.value (offsets[9]+64#64)) (.value 1#64)) (v0)
       let v2 := vselectScalar (.value (BitVec.ofBool (active 10)))
        (LLVM.Ty.insertelement (e := .bitvec (.concrete 64)) (v1)
          (.value (offsets[10]+64#64)) (.value 2#64)) (v1)
       let v3 := vselectScalar (.value (BitVec.ofBool (active 11)))
        (LLVM.Ty.insertelement (e := .bitvec (.concrete 64)) (v2)
          (.value (offsets[11]+64#64)) (.value 3#64)) (v2)
       let v4 := vselectScalar (.value (BitVec.ofBool (active 12)))
        (LLVM.Ty.insertelement (e := .bitvec (.concrete 64)) (v3)
          (.value (offsets[12]+64#64)) (.value 4#64)) (v3)
       let v5 := vselectScalar (.value (BitVec.ofBool (active 13)))
        (LLVM.Ty.insertelement (e := .bitvec (.concrete 64)) (v4)
          (.value (offsets[13]+64#64)) (.value 5#64)) (v4)
       let v6 := vselectScalar (.value (BitVec.ofBool (active 14)))
        (LLVM.Ty.insertelement (e := .bitvec (.concrete 64)) (v5)
          (.value (offsets[14]+64#64)) (.value 6#64)) (v5)
       let v7 := vselectScalar (.value (BitVec.ofBool (active 15)))
        (LLVM.Ty.insertelement (e := .bitvec (.concrete 64)) (v6)
          (.value (offsets[15]+64#64)) (.value 7#64)) (v6)
       v7) = Vector.ofFn (fun i : Fin 8 => PoisonOr.value
        (if active ⟨i.val+8, by omega⟩ then offsets[(⟨i.val+8, by omega⟩ : Fin 16)]+64
          else offsets[(⟨i.val+8, by omega⟩ : Fin 16)])) := by
    exact updateHalf_eq (Vector.ofFn fun i : Fin 8 => offsets[(⟨i.val+8, by omega⟩ : Fin 16)])
      (Vector.ofFn fun i : Fin 8 => offsets[(⟨i.val+8, by omega⟩ : Fin 16)] + 64) (fun i : Fin 8 => active ⟨i.val+8, by omega⟩)
  dsimp only at hlo hhi
  simp only [Fin.getElem_fin] at hlo hhi
  simp only [select_value, headerTarget16, Vector.getElem_ofFn, Fin.getElem_fin]
  rw [hhi]
  rw [hlo]
  rfl

open Blake3Compression in
/-- Actual emitted feed-forward, mask selection and all offset aliases agree
with the mathematical header payload. Memory is unchanged. -/
theorem update16_refines (V : Input16.Valuation) (s : GlobalState)
    (active : Fin 16 → Bool) (old x y : CV (Lanes 16))
    (offsets : Vector (BitVec 64) 16) (hV : Env16 V active old x y offsets)
    (hb : ∀ i : Fin 16, offsets[i].toNat ≤ 960) :
    StateT.run (agave_batch_16.cfgBlock_8.denote V) s =
      .value (((result16 V).fst, .inr (headerTarget16
        (fun w lane => if active lane then x w lane ^^^ y w lane else old w lane)
        (Vector.ofFn fun i => if active i then offsets[i]+64 else offsets[i]))), s) := by
  have ht := target16_eq V active old x y offsets hV hb (mask16_eq V active old x y offsets hV)
  have hs := (result16_snd V).trans (congrArg Sum.inr ht)
  have he : result16 V = ((result16 V).fst, .inr (headerTarget16
      (fun w lane => if active lane then x w lane ^^^ y w lane else old w lane)
      (Vector.ofFn fun i => if active i then offsets[i]+64 else offsets[i]))) :=
    Prod.ext rfl hs
  rw [update16_denote, he]

/-- The masked machine update advances the existing scalar-prefix invariant.
The only compression premise is the primitive's independently proved result
on this iteration's scalar block. -/
theorem headerTarget16_stateAt_next (ms : Fin 16 → AgaveConcrete.Message) (iteration : Nat)
    (fresh : Blake3Compression.CV (Blake3Compression.Lanes 16))
    (hnew : ∀ lane, iteration < AgaveBatchControl.rootIndex (ms lane).length → ∀ w,
      fresh w lane = AgaveConcrete.compress
        (AgaveBatchControl.stateAt AgaveConcrete.compress AgaveConcrete.iv
          (AgaveConcrete.bytes (ms lane)) (ms lane).length iteration).cv
        (AgaveBatchControl.scalarBlock (AgaveConcrete.bytes (ms lane)) (ms lane).length
          (min iteration (AgaveBatchControl.rootIndex (ms lane).length)))
        0 0 64 (if min iteration (AgaveBatchControl.rootIndex (ms lane).length) = 0 then 1 else 0) w) :
    headerTarget16
      (fun w lane => if decide (iteration < AgaveBatchControl.rootIndex (ms lane).length) then
        fresh w lane else
        (AgaveBatchControl.stateAt AgaveConcrete.compress AgaveConcrete.iv
          (AgaveConcrete.bytes (ms lane)) (ms lane).length iteration).cv w)
      (Vector.ofFn fun lane =>
        if decide (iteration < AgaveBatchControl.rootIndex (ms lane).length) then
          BitVec.ofNat 64 (batchOffset (ms lane).length iteration + 64)
        else BitVec.ofNat 64 (batchOffset (ms lane).length iteration)) =
      headerAt16 ms (iteration + 1) := by
  unfold headerAt16
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

def stateCV16 (ms : Fin 16 → AgaveConcrete.Message) (iteration : Nat) :
    Blake3Compression.CV (Blake3Compression.Lanes 16) :=
  fun w lane => (AgaveBatchControl.stateAt AgaveConcrete.compress AgaveConcrete.iv
    (AgaveConcrete.bytes (ms lane)) (ms lane).length iteration).cv w

def activeAt16 (ms : Fin 16 → AgaveConcrete.Message) (iteration : Nat) : Fin 16 → Bool :=
  fun lane => decide (iteration < AgaveBatchControl.rootIndex (ms lane).length)

def offsetsAt16 (ms : Fin 16 → AgaveConcrete.Message) (iteration : Nat) : Vector (BitVec 64) 16 :=
  Vector.ofFn fun lane => BitVec.ofNat 64 (batchOffset (ms lane).length iteration)

def advancedAt16 (ms : Fin 16 → AgaveConcrete.Message) (iteration : Nat) : Vector (BitVec 64) 16 :=
  Vector.ofFn fun lane => BitVec.ofNat 64 (batchOffset (ms lane).length iteration + 64)

/-- Composition-ready actual backedge theorem: the independent compression
contract and the input representation produce the next scalar-prefix state. -/
theorem update16_stateAt (V : Input16.Valuation) (s : GlobalState)
    (ms : Fin 16 → AgaveConcrete.Message) (iteration : Nat)
    (x y : Blake3Compression.CV (Blake3Compression.Lanes 16))
    (henv : Env16 V (activeAt16 ms iteration) (stateCV16 ms iteration) x y
      (offsetsAt16 ms iteration))
    (hms : ∀ lane, (ms lane).length ≤ 1024)
    (hcompress : ∀ lane, iteration < AgaveBatchControl.rootIndex (ms lane).length → ∀ w,
      x w lane ^^^ y w lane = AgaveConcrete.compress
        (AgaveBatchControl.stateAt AgaveConcrete.compress AgaveConcrete.iv
          (AgaveConcrete.bytes (ms lane)) (ms lane).length iteration).cv
        (AgaveBatchControl.scalarBlock (AgaveConcrete.bytes (ms lane)) (ms lane).length
          (min iteration (AgaveBatchControl.rootIndex (ms lane).length)))
        0 0 64 (if min iteration (AgaveBatchControl.rootIndex (ms lane).length) = 0 then 1 else 0) w) :
    StateT.run (agave_batch_16.cfgBlock_8.denote V) s =
      .value (((result16 V).1, .inr (headerAt16 ms (iteration + 1))), s) := by
  have hb (i : Fin 16) : (offsetsAt16 ms iteration)[i].toNat ≤ 960 := by
    simp only [offsetsAt16, Fin.getElem_fin, Vector.getElem_ofFn, BitVec.toNat_ofNat]
    exact Nat.le_trans (Nat.mod_le ..) (batchOffset_le_960 _ _ (hms i))
  rw [update16_refines V s _ _ x y _ henv hb]
  have ht := headerTarget16_stateAt_next ms iteration (fun w lane => x w lane ^^^ y w lane) hcompress
  have hoff : (Vector.ofFn fun i => if activeAt16 ms iteration i then
      (offsetsAt16 ms iteration)[i] + 64 else (offsetsAt16 ms iteration)[i]) =
      (Vector.ofFn fun lane => if decide (iteration < AgaveBatchControl.rootIndex (ms lane).length) then
        BitVec.ofNat 64 (batchOffset (ms lane).length iteration + 64)
        else BitVec.ofNat 64 (batchOffset (ms lane).length iteration)) := by
    apply Vector.ext
    intro i hi
    simp [activeAt16, offsetsAt16, advancedAt16, BitVec.ofNat_add]
  rw [hoff]
  exact congrArg (fun t : SuccArgs agave_batch_16.cfgSigs =>
    PoisonOr.value (((result16 V).1, Sum.inr t), s)) ht

end AgaveLatticeHash.MLIR.BatchUpdate16
