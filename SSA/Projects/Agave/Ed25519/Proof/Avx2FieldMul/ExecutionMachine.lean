import SSA.Projects.Agave.Ed25519.Proof.ReduceBitcast
import Mathlib.Data.Fin.VecNotation

/-! A poison-free, wrapping bitvector model in the exact SSA instruction order
of `Program.program`.  Unobserved poison/undef lanes are represented by zero;
`ExecutionKernel.kernel_call` proves that the extracted program never observes
those choices.  The model does not perform field arithmetic in `Nat`. -/
namespace Agave.Ed25519.Avx2FieldMul.Execution

abbrev Blocks := Fin 5 → V32

-- This declaration is a finite straight-line trace. Explicit index proofs avoid
-- running the default bounds tactic over hundreds of preceding SSA lets.
set_option maxHeartbeats 800000 in
/-- Five packed output vectors in the source register order. -/
def wordTrace (a b : Blocks) : Blocks :=
  let v0 : BitVec 32 := 0
  let v1 : BitVec 32 := 0
  let v2 : Vector (BitVec 32) 8 := Vector.replicate 8 0
  let v3 : BitVec 32 := 0
  let v4 : Vector (BitVec 32) 8 := v2.set 0 v1 (by decide)
  let v5 : BitVec 32 := 1
  let v6 : Vector (BitVec 32) 8 := v4.set 1 v1 (by decide)
  let v7 : BitVec 32 := 2
  let v8 : Vector (BitVec 32) 8 := v6.set 2 v0 (by decide)
  let v9 : BitVec 32 := 3
  let v10 : Vector (BitVec 32) 8 := v8.set 3 v0 (by decide)
  let v11 : BitVec 32 := 4
  let v12 : Vector (BitVec 32) 8 := v10.set 4 v1 (by decide)
  let v13 : BitVec 32 := 5
  let v14 : Vector (BitVec 32) 8 := v12.set 5 v1 (by decide)
  let v15 : BitVec 32 := 6
  let v16 : Vector (BitVec 32) 8 := v14.set 6 v0 (by decide)
  let v17 : BitVec 32 := 7
  let v18 : Vector (BitVec 32) 8 := v16.set 7 v0 (by decide)
  let v19 : Vector (BitVec 32) 8 := Vector.replicate 8 0
  let v20 : BitVec 32 := 0
  let v21 : Vector (BitVec 32) 8 := v19.set 0 v0 (by decide)
  let v22 : BitVec 32 := 1
  let v23 : Vector (BitVec 32) 8 := v21.set 1 v0 (by decide)
  let v24 : BitVec 32 := 2
  let v25 : Vector (BitVec 32) 8 := v23.set 2 v1 (by decide)
  let v26 : BitVec 32 := 3
  let v27 : Vector (BitVec 32) 8 := v25.set 3 v1 (by decide)
  let v28 : BitVec 32 := 4
  let v29 : Vector (BitVec 32) 8 := v27.set 4 v0 (by decide)
  let v30 : BitVec 32 := 5
  let v31 : Vector (BitVec 32) 8 := v29.set 5 v0 (by decide)
  let v32 : BitVec 32 := 6
  let v33 : Vector (BitVec 32) 8 := v31.set 6 v1 (by decide)
  let v34 : BitVec 32 := 7
  let v35 : Vector (BitVec 32) 8 := v33.set 7 v1 (by decide)
  let v36 : BitVec 64 := 32
  let v37 : BitVec 64 := 64
  let v38 : BitVec 64 := 96
  let v39 : BitVec 64 := 128
  let v40 : Vector (BitVec 64) 4 := Vector.replicate 4 19
  let v41 : Vector (BitVec 32) 8 := Vector.replicate 8 1
  let v42 : Vector (BitVec 64) 4 := Vector.replicate 4 4294967295
  let v43 : Vector (BitVec 64) 4 := Vector.replicate 4 26
  let v44 : Vector (BitVec 64) 4 := Vector.replicate 4 67108863
  let v45 : Vector (BitVec 64) 4 := Vector.replicate 4 25
  let v46 : Vector (BitVec 64) 4 := Vector.replicate 4 33554431
  let v47 : Vector (BitVec 64) 4 := Vector.replicate 4 51
  let v48 : BitVec 32 := 67108863
  let v49 : Vector (BitVec 32) 8 := Vector.replicate 8 0
  let v50 : BitVec 32 := 0
  let v51 : Vector (BitVec 32) 8 := v49.set 0 v48 (by decide)
  let v52 : BitVec 32 := 1
  let v53 : Vector (BitVec 32) 8 := v51.set 1 v0 (by decide)
  let v54 : BitVec 32 := 2
  let v55 : Vector (BitVec 32) 8 := v53.set 2 v48 (by decide)
  let v56 : BitVec 32 := 3
  let v57 : Vector (BitVec 32) 8 := v55.set 3 v0 (by decide)
  let v58 : BitVec 32 := 4
  let v59 : Vector (BitVec 32) 8 := v57.set 4 v48 (by decide)
  let v60 : BitVec 32 := 5
  let v61 : Vector (BitVec 32) 8 := v59.set 5 v0 (by decide)
  let v62 : BitVec 32 := 6
  let v63 : Vector (BitVec 32) 8 := v61.set 6 v48 (by decide)
  let v64 : BitVec 32 := 7
  let v65 : Vector (BitVec 32) 8 := v63.set 7 v0 (by decide)
  let v66 : BitVec 32 := 33554431
  let v67 : Vector (BitVec 32) 8 := Vector.replicate 8 0
  let v68 : BitVec 32 := 0
  let v69 : Vector (BitVec 32) 8 := v67.set 0 v66 (by decide)
  let v70 : BitVec 32 := 1
  let v71 : Vector (BitVec 32) 8 := v69.set 1 v0 (by decide)
  let v72 : BitVec 32 := 2
  let v73 : Vector (BitVec 32) 8 := v71.set 2 v66 (by decide)
  let v74 : BitVec 32 := 3
  let v75 : Vector (BitVec 32) 8 := v73.set 3 v0 (by decide)
  let v76 : BitVec 32 := 4
  let v77 : Vector (BitVec 32) 8 := v75.set 4 v66 (by decide)
  let v78 : BitVec 32 := 5
  let v79 : Vector (BitVec 32) 8 := v77.set 5 v0 (by decide)
  let v80 : BitVec 32 := 6
  let v81 : Vector (BitVec 32) 8 := v79.set 6 v66 (by decide)
  let v82 : BitVec 32 := 7
  let v83 : Vector (BitVec 32) 8 := v81.set 7 v0 (by decide)
  let v84 : Vector (BitVec 32) 8 := a 0
  let v85 : Vector (BitVec 32) 8 := #v[v84[0]'(by decide), v18[0]'(by decide), v84[1]'(by decide), v18[1]'(by decide), v84[4]'(by decide), v18[4]'(by decide), v84[5]'(by decide), v18[5]'(by decide)]
  let v86 : Vector (BitVec 32) 8 := #v[v84[2]'(by decide), v35[2]'(by decide), v84[3]'(by decide), v35[3]'(by decide), v84[6]'(by decide), v35[6]'(by decide), v84[7]'(by decide), v35[7]'(by decide)]
  let v87 : Vector (BitVec 64) 4 := join64 v85
  let v88 : Vector (BitVec 64) 4 := join64 v86
  let v90 : Vector (BitVec 32) 8 := a 1
  let v91 : Vector (BitVec 32) 8 := #v[v90[0]'(by decide), v18[0]'(by decide), v90[1]'(by decide), v18[1]'(by decide), v90[4]'(by decide), v18[4]'(by decide), v90[5]'(by decide), v18[5]'(by decide)]
  let v92 : Vector (BitVec 32) 8 := #v[v90[2]'(by decide), v35[2]'(by decide), v90[3]'(by decide), v35[3]'(by decide), v90[6]'(by decide), v35[6]'(by decide), v90[7]'(by decide), v35[7]'(by decide)]
  let v93 : Vector (BitVec 64) 4 := join64 v91
  let v94 : Vector (BitVec 64) 4 := join64 v92
  let v96 : Vector (BitVec 32) 8 := a 2
  let v97 : Vector (BitVec 32) 8 := #v[v96[0]'(by decide), v18[0]'(by decide), v96[1]'(by decide), v18[1]'(by decide), v96[4]'(by decide), v18[4]'(by decide), v96[5]'(by decide), v18[5]'(by decide)]
  let v98 : Vector (BitVec 32) 8 := #v[v96[2]'(by decide), v35[2]'(by decide), v96[3]'(by decide), v35[3]'(by decide), v96[6]'(by decide), v35[6]'(by decide), v96[7]'(by decide), v35[7]'(by decide)]
  let v99 : Vector (BitVec 64) 4 := join64 v97
  let v100 : Vector (BitVec 64) 4 := join64 v98
  let v102 : Vector (BitVec 32) 8 := a 3
  let v103 : Vector (BitVec 32) 8 := #v[v102[0]'(by decide), v18[0]'(by decide), v102[1]'(by decide), v18[1]'(by decide), v102[4]'(by decide), v18[4]'(by decide), v102[5]'(by decide), v18[5]'(by decide)]
  let v104 : Vector (BitVec 32) 8 := #v[v102[2]'(by decide), v35[2]'(by decide), v102[3]'(by decide), v35[3]'(by decide), v102[6]'(by decide), v35[6]'(by decide), v102[7]'(by decide), v35[7]'(by decide)]
  let v105 : Vector (BitVec 64) 4 := join64 v103
  let v106 : Vector (BitVec 64) 4 := join64 v104
  let v108 : Vector (BitVec 32) 8 := a 4
  let v109 : Vector (BitVec 32) 8 := #v[v108[0]'(by decide), v18[0]'(by decide), v108[1]'(by decide), v18[1]'(by decide), v108[4]'(by decide), v18[4]'(by decide), v108[5]'(by decide), v18[5]'(by decide)]
  let v110 : Vector (BitVec 32) 8 := #v[v108[2]'(by decide), v35[2]'(by decide), v108[3]'(by decide), v35[3]'(by decide), v108[6]'(by decide), v35[6]'(by decide), v108[7]'(by decide), v35[7]'(by decide)]
  let v111 : Vector (BitVec 64) 4 := join64 v109
  let v112 : Vector (BitVec 64) 4 := join64 v110
  let v113 : Vector (BitVec 32) 8 := b 0
  let v114 : Vector (BitVec 32) 8 := #v[v113[0]'(by decide), v18[0]'(by decide), v113[1]'(by decide), v18[1]'(by decide), v113[4]'(by decide), v18[4]'(by decide), v113[5]'(by decide), v18[5]'(by decide)]
  let v115 : Vector (BitVec 32) 8 := #v[v113[2]'(by decide), v35[2]'(by decide), v113[3]'(by decide), v35[3]'(by decide), v113[6]'(by decide), v35[6]'(by decide), v113[7]'(by decide), v35[7]'(by decide)]
  let v116 : Vector (BitVec 64) 4 := join64 v114
  let v117 : Vector (BitVec 64) 4 := join64 v115
  let v119 : Vector (BitVec 32) 8 := b 1
  let v120 : Vector (BitVec 32) 8 := #v[v119[0]'(by decide), v18[0]'(by decide), v119[1]'(by decide), v18[1]'(by decide), v119[4]'(by decide), v18[4]'(by decide), v119[5]'(by decide), v18[5]'(by decide)]
  let v121 : Vector (BitVec 32) 8 := #v[v119[2]'(by decide), v35[2]'(by decide), v119[3]'(by decide), v35[3]'(by decide), v119[6]'(by decide), v35[6]'(by decide), v119[7]'(by decide), v35[7]'(by decide)]
  let v122 : Vector (BitVec 64) 4 := join64 v120
  let v123 : Vector (BitVec 64) 4 := join64 v121
  let v125 : Vector (BitVec 32) 8 := b 2
  let v126 : Vector (BitVec 32) 8 := #v[v125[0]'(by decide), v18[0]'(by decide), v125[1]'(by decide), v18[1]'(by decide), v125[4]'(by decide), v18[4]'(by decide), v125[5]'(by decide), v18[5]'(by decide)]
  let v127 : Vector (BitVec 32) 8 := #v[v125[2]'(by decide), v35[2]'(by decide), v125[3]'(by decide), v35[3]'(by decide), v125[6]'(by decide), v35[6]'(by decide), v125[7]'(by decide), v35[7]'(by decide)]
  let v128 : Vector (BitVec 64) 4 := join64 v126
  let v129 : Vector (BitVec 64) 4 := join64 v127
  let v131 : Vector (BitVec 32) 8 := b 3
  let v132 : Vector (BitVec 32) 8 := #v[v131[0]'(by decide), v18[0]'(by decide), v131[1]'(by decide), v18[1]'(by decide), v131[4]'(by decide), v18[4]'(by decide), v131[5]'(by decide), v18[5]'(by decide)]
  let v133 : Vector (BitVec 32) 8 := #v[v131[2]'(by decide), v35[2]'(by decide), v131[3]'(by decide), v35[3]'(by decide), v131[6]'(by decide), v35[6]'(by decide), v131[7]'(by decide), v35[7]'(by decide)]
  let v134 : Vector (BitVec 64) 4 := join64 v132
  let v135 : Vector (BitVec 64) 4 := join64 v133
  let v137 : Vector (BitVec 32) 8 := b 4
  let v138 : Vector (BitVec 32) 8 := #v[v137[0]'(by decide), v18[0]'(by decide), v137[1]'(by decide), v18[1]'(by decide), v137[4]'(by decide), v18[4]'(by decide), v137[5]'(by decide), v18[5]'(by decide)]
  let v139 : Vector (BitVec 32) 8 := #v[v137[2]'(by decide), v35[2]'(by decide), v137[3]'(by decide), v35[3]'(by decide), v137[6]'(by decide), v35[6]'(by decide), v137[7]'(by decide), v35[7]'(by decide)]
  let v140 : Vector (BitVec 64) 4 := join64 v138
  let v141 : Vector (BitVec 64) 4 := join64 v139
  let v142 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v117 v40
  let v143 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v122 v40
  let v144 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v123 v40
  let v145 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v128 v40
  let v146 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v129 v40
  let v147 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v134 v40
  let v148 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v135 v40
  let v149 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v140 v40
  let v150 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v141 v40
  let v151 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v116 v87
  let v152 : Vector (BitVec 32) 8 := Vector.zipWith (fun (x y : BitVec 32) => x <<< y.toNat) v86 v41
  let v153 : Vector (BitVec 64) 4 := join64 v152
  let v154 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x &&& y) v150 v42
  let v155 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v154 v153
  let v156 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x &&& y) v149 v42
  let v157 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v156 v93
  let v158 : Vector (BitVec 32) 8 := Vector.zipWith (fun (x y : BitVec 32) => x <<< y.toNat) v92 v41
  let v159 : Vector (BitVec 64) 4 := join64 v158
  let v160 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x &&& y) v148 v42
  let v161 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v160 v159
  let v162 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x &&& y) v147 v42
  let v163 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v162 v99
  let v164 : Vector (BitVec 32) 8 := Vector.zipWith (fun (x y : BitVec 32) => x <<< y.toNat) v98 v41
  let v165 : Vector (BitVec 64) 4 := join64 v164
  let v166 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x &&& y) v146 v42
  let v167 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v166 v165
  let v168 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x &&& y) v145 v42
  let v169 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v168 v105
  let v170 : Vector (BitVec 32) 8 := Vector.zipWith (fun (x y : BitVec 32) => x <<< y.toNat) v104 v41
  let v171 : Vector (BitVec 64) 4 := join64 v170
  let v172 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x &&& y) v144 v42
  let v173 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v172 v171
  let v174 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x &&& y) v143 v42
  let v175 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v174 v111
  let v176 : Vector (BitVec 32) 8 := Vector.zipWith (fun (x y : BitVec 32) => x <<< y.toNat) v110 v41
  let v177 : Vector (BitVec 64) 4 := join64 v176
  let v178 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x &&& y) v142 v42
  let v179 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v178 v177
  let v180 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v179 v151
  let v181 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v180 v175
  let v182 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v181 v173
  let v183 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v182 v169
  let v184 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v183 v167
  let v185 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v184 v163
  let v186 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v185 v161
  let v187 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v186 v157
  let v188 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v187 v155
  let v189 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v117 v87
  let v190 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v116 v88
  let v191 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v154 v93
  let v192 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v156 v94
  let v193 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v160 v99
  let v194 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v162 v100
  let v195 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v166 v105
  let v196 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v168 v106
  let v197 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v172 v111
  let v198 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v174 v112
  let v199 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v122 v87
  let v200 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v117 v153
  let v201 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v116 v93
  let v202 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v154 v159
  let v203 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v156 v99
  let v204 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v160 v165
  let v205 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v162 v105
  let v206 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v166 v171
  let v207 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v168 v111
  let v208 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v172 v177
  let v209 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v123 v87
  let v210 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v122 v88
  let v211 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v117 v93
  let v212 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v116 v94
  let v213 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v154 v99
  let v214 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v156 v100
  let v215 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v160 v105
  let v216 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v162 v106
  let v217 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v166 v111
  let v218 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v168 v112
  let v219 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v128 v87
  let v220 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v123 v153
  let v221 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v122 v93
  let v222 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v117 v159
  let v223 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v116 v99
  let v224 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v154 v165
  let v225 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v156 v105
  let v226 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v160 v171
  let v227 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v162 v111
  let v228 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v166 v177
  let v229 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v223 v222
  let v230 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v229 v221
  let v231 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v230 v220
  let v232 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v231 v219
  let v233 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v232 v228
  let v234 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v233 v227
  let v235 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v234 v226
  let v236 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v235 v225
  let v237 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v236 v224
  let v238 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v129 v87
  let v239 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v128 v88
  let v240 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v123 v93
  let v241 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v122 v94
  let v242 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v117 v99
  let v243 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v116 v100
  let v244 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v154 v105
  let v245 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v156 v106
  let v246 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v160 v111
  let v247 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v162 v112
  let v248 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v134 v87
  let v249 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v129 v153
  let v250 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v128 v93
  let v251 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v123 v159
  let v252 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v122 v99
  let v253 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v117 v165
  let v254 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v116 v105
  let v255 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v154 v171
  let v256 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v156 v111
  let v257 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v160 v177
  let v258 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v135 v87
  let v259 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v134 v88
  let v260 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v129 v93
  let v261 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v128 v94
  let v262 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v123 v99
  let v263 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v122 v100
  let v264 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v117 v105
  let v265 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v116 v106
  let v266 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v154 v111
  let v267 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v156 v112
  let v268 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v140 v87
  let v269 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v135 v153
  let v270 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v134 v93
  let v271 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v129 v159
  let v272 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v128 v99
  let v273 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v123 v165
  let v274 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v122 v105
  let v275 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v117 v171
  let v276 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v116 v111
  let v277 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v154 v177
  let v278 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v141 v87
  let v279 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v140 v88
  let v280 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v135 v93
  let v281 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v134 v94
  let v282 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v129 v99
  let v283 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v128 v100
  let v284 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v123 v105
  let v285 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v122 v106
  let v286 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v117 v111
  let v287 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v116 v112
  let v288 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x >>> y.toNat) v188 v43
  let v289 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v190 v189
  let v290 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v289 v197
  let v291 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v290 v198
  let v292 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v291 v195
  let v293 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v292 v196
  let v294 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v293 v193
  let v295 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v294 v194
  let v296 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v295 v191
  let v297 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v296 v192
  let v298 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v297 v288
  let v299 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x &&& y) v188 v44
  let v300 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x >>> y.toNat) v237 v43
  let v301 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v243 v242
  let v302 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v301 v240
  let v303 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v302 v241
  let v304 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v303 v238
  let v305 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v304 v239
  let v306 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v305 v246
  let v307 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v306 v247
  let v308 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v307 v244
  let v309 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v308 v245
  let v310 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v309 v300
  let v311 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x &&& y) v237 v44
  let v312 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x >>> y.toNat) v298 v45
  let v313 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v201 v200
  let v314 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v313 v199
  let v315 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v314 v208
  let v316 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v315 v207
  let v317 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v316 v206
  let v318 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v317 v205
  let v319 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v318 v204
  let v320 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v319 v203
  let v321 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v320 v202
  let v322 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v321 v312
  let v323 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x &&& y) v298 v46
  let v324 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x >>> y.toNat) v310 v45
  let v325 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v254 v253
  let v326 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v325 v251
  let v327 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v326 v252
  let v328 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v327 v250
  let v329 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v328 v249
  let v330 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v329 v248
  let v331 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v330 v257
  let v332 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v331 v256
  let v333 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v332 v255
  let v334 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v333 v324
  let v335 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x &&& y) v310 v46
  let v336 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x >>> y.toNat) v322 v43
  let v337 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v212 v211
  let v338 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v337 v209
  let v339 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v338 v210
  let v340 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v339 v217
  let v341 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v340 v218
  let v342 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v341 v215
  let v343 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v342 v216
  let v344 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v343 v213
  let v345 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v344 v214
  let v346 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v345 v336
  let v347 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x >>> y.toNat) v334 v43
  let v348 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v265 v264
  let v349 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v348 v262
  let v350 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v349 v263
  let v351 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v350 v260
  let v352 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v351 v261
  let v353 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v352 v258
  let v354 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v353 v259
  let v355 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v354 v266
  let v356 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v355 v267
  let v357 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v356 v347
  let v358 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x >>> y.toNat) v346 v45
  let v359 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v358 v311
  let v360 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x >>> y.toNat) v357 v45
  let v361 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v275 v276
  let v362 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v361 v274
  let v363 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v362 v273
  let v364 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v363 v272
  let v365 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v364 v271
  let v366 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v365 v270
  let v367 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v366 v269
  let v368 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v367 v268
  let v369 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v368 v277
  let v370 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v369 v360
  let v371 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x >>> y.toNat) v359 v43
  let v372 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v371 v335
  let v373 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x >>> y.toNat) v370 v43
  let v374 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v287 v286
  let v375 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v374 v284
  let v376 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v375 v285
  let v377 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v376 v282
  let v378 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v377 v283
  let v379 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v378 v280
  let v380 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v379 v281
  let v381 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v380 v278
  let v382 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v381 v279
  let v383 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v382 v373
  let v384 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x >>> y.toNat) v383 v45
  let v385 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x &&& y) v384 v44
  let v386 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x >>> y.toNat) v383 v47
  let v387 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v385 v40
  let v388 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v386 v40
  let v389 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v387 v299
  let v390 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v388 v323
  let v391 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x >>> y.toNat) v389 v43
  let v392 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v390 v391
  let v393 : Vector (BitVec 32) 8 := split32 v389
  let v394 : Vector (BitVec 32) 8 := Vector.zipWith (fun (x y : BitVec 32) => x &&& y) v393 v65
  let v395 : Vector (BitVec 32) 8 := split32 v392
  let v396 : Vector (BitVec 32) 8 := #v[v394[0]'(by decide), v394[2]'(by decide), v395[0]'(by decide), v395[2]'(by decide), v394[4]'(by decide), v394[6]'(by decide), v395[4]'(by decide), v395[6]'(by decide)]
  let v397 : Vector (BitVec 32) 8 := split32 v322
  let v398 : Vector (BitVec 32) 8 := Vector.zipWith (fun (x y : BitVec 32) => x &&& y) v397 v65
  let v399 : Vector (BitVec 32) 8 := split32 v346
  let v400 : Vector (BitVec 32) 8 := Vector.zipWith (fun (x y : BitVec 32) => x &&& y) v399 v83
  let v401 : Vector (BitVec 32) 8 := #v[v398[0]'(by decide), v398[2]'(by decide), v400[0]'(by decide), v400[2]'(by decide), v398[4]'(by decide), v398[6]'(by decide), v400[4]'(by decide), v400[6]'(by decide)]
  let v402 : Vector (BitVec 32) 8 := split32 v372
  let v403 : Vector (BitVec 32) 8 := split32 v359
  let v404 : Vector (BitVec 32) 8 := Vector.zipWith (fun (x y : BitVec 32) => x &&& y) v403 v65
  let v405 : Vector (BitVec 32) 8 := #v[v404[0]'(by decide), v404[2]'(by decide), v402[0]'(by decide), v402[2]'(by decide), v404[4]'(by decide), v404[6]'(by decide), v402[4]'(by decide), v402[6]'(by decide)]
  let v406 : Vector (BitVec 32) 8 := split32 v334
  let v407 : Vector (BitVec 32) 8 := Vector.zipWith (fun (x y : BitVec 32) => x &&& y) v406 v65
  let v408 : Vector (BitVec 32) 8 := split32 v357
  let v409 : Vector (BitVec 32) 8 := Vector.zipWith (fun (x y : BitVec 32) => x &&& y) v408 v83
  let v410 : Vector (BitVec 32) 8 := #v[v407[0]'(by decide), v407[2]'(by decide), v409[0]'(by decide), v409[2]'(by decide), v407[4]'(by decide), v407[6]'(by decide), v409[4]'(by decide), v409[6]'(by decide)]
  let v411 : Vector (BitVec 32) 8 := split32 v370
  let v412 : Vector (BitVec 32) 8 := Vector.zipWith (fun (x y : BitVec 32) => x &&& y) v411 v65
  let v413 : Vector (BitVec 32) 8 := split32 v383
  let v414 : Vector (BitVec 32) 8 := Vector.zipWith (fun (x y : BitVec 32) => x &&& y) v413 v83
  let v415 : Vector (BitVec 32) 8 := #v[v412[0]'(by decide), v412[2]'(by decide), v414[0]'(by decide), v414[2]'(by decide), v412[4]'(by decide), v412[6]'(by decide), v414[4]'(by decide), v414[6]'(by decide)]
  ![v396, v401, v405, v410, v415]

/-- Logical A/B/C/D elements extracted from the physical packed input. -/
def unpackBlocks (a : Blocks) : Fin 4 → (Fin 10 → BitVec 32) :=
  ![![(a 0)[0]'(by decide), (a 0)[2]'(by decide), (a 1)[0]'(by decide), (a 1)[2]'(by decide),
      (a 2)[0]'(by decide), (a 2)[2]'(by decide), (a 3)[0]'(by decide), (a 3)[2]'(by decide),
      (a 4)[0]'(by decide), (a 4)[2]'(by decide)],
    ![(a 0)[1]'(by decide), (a 0)[3]'(by decide), (a 1)[1]'(by decide), (a 1)[3]'(by decide),
      (a 2)[1]'(by decide), (a 2)[3]'(by decide), (a 3)[1]'(by decide), (a 3)[3]'(by decide),
      (a 4)[1]'(by decide), (a 4)[3]'(by decide)],
    ![(a 0)[4]'(by decide), (a 0)[6]'(by decide), (a 1)[4]'(by decide), (a 1)[6]'(by decide),
      (a 2)[4]'(by decide), (a 2)[6]'(by decide), (a 3)[4]'(by decide), (a 3)[6]'(by decide),
      (a 4)[4]'(by decide), (a 4)[6]'(by decide)],
    ![(a 0)[5]'(by decide), (a 0)[7]'(by decide), (a 1)[5]'(by decide), (a 1)[7]'(by decide),
      (a 2)[5]'(by decide), (a 2)[7]'(by decide), (a 3)[5]'(by decide), (a 3)[7]'(by decide),
      (a 4)[5]'(by decide), (a 4)[7]'(by decide)]]

end Agave.Ed25519.Avx2FieldMul.Execution
