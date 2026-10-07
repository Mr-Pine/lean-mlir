import SSA.Projects.Agave.Ed25519.Proof.SerialPoint.ResidualWordRefinement

namespace Agave.Ed25519.SerialPoint.Execution
open SerialFieldMul
attribute [local irreducible] machine

/-- Exact word trace of the pinned affine_add compiler body, including its 3 field calls. -/
def affineAddWordTrace (p c : PointWords) : PointWords :=
  let v0 : BitVec 32 := 1
  let v1 : BitVec 64 := 40
  let v2 : BitVec 64 := 48
  let v3 : BitVec 64 := 56
  let v4 : BitVec 64 := 64
  let v5 : BitVec 64 := 72
  let v6 : BitVec 64 := 8
  let v7 : BitVec 64 := 16
  let v8 : BitVec 64 := 24
  let v9 : BitVec 64 := 32
  let v10 : BitVec 64 := 36028797018963664
  let v11 : BitVec 64 := 36028797018963952
  let v12 : BitVec 64 := 51
  let v13 : BitVec 64 := 2251799813685247
  let v14 : BitVec 64 := 19
  let v15 : BitVec 64 := 120
  let v16 : BitVec 64 := 80
  let v17 : BitVec 64 := 88
  let v18 : BitVec 64 := 96
  let v19 : BitVec 64 := 104
  let v20 : BitVec 64 := 112
  let v21 : BitVec 64 := 1
  let v22 : BitVec 64 := 128
  let v23 : BitVec 64 := 136
  let v24 : BitVec 64 := 144
  let v25 : BitVec 64 := 152
  let v32 := p 5
  let v34 := p 6
  let v36 := p 7
  let v38 := p 8
  let v40 := p 9
  let v41 := p 0
  let v42 := v41 + v32
  let v44 := p 1
  let v45 := v44 + v34
  let v47 := p 2
  let v48 := v47 + v36
  let v50 := p 3
  let v51 := v50 + v38
  let v53 := p 4
  let v54 := v53 + v40
  let v59 := v32 + v10
  let v60 := v59 - v41
  let v61 := v34 + v11
  let v62 := v61 - v44
  let v63 := v36 + v11
  let v64 := v63 - v47
  let v65 := v38 + v11
  let v66 := v65 - v50
  let v67 := v40 + v11
  let v68 := v67 - v53
  let v69 := v60 >>> v12
  let v70 := v62 >>> v12
  let v71 := v64 >>> v12
  let v72 := v66 >>> v12
  let v73 := v68 >>> v12
  let v74 := v60 &&& v13
  let v75 := v62 &&& v13
  let v76 := v64 &&& v13
  let v77 := v66 &&& v13
  let v78 := v68 &&& v13
  let v79 := v73 * v14
  let v80 := v79 + v74
  let v81 := v75 + v69
  let v82 := v76 + v70
  let v83 := v77 + v71
  let v84 := v78 + v72
  let call0 := machine (![v42, v45, v48, v51, v54]) (![c 0, c 1, c 2, c 3, c 4])
  let call1 := machine (![v80, v81, v82, v83, v84]) (![c 5, c 6, c 7, c 8, c 9])
  let call2 := machine (![p 15, p 16, p 17, p 18, p 19]) (![c 10, c 11, c 12, c 13, c 14])
  let v93 := p 10
  let v95 := p 11
  let v97 := p 12
  let v99 := p 13
  let v101 := p 14
  let v102 := v93 <<< v21
  let v103 := v95 <<< v21
  let v104 := v97 <<< v21
  let v105 := v99 <<< v21
  let v106 := v101 <<< v21
  let v107 := call0 0
  let v108 := v107 + v10
  let v109 := call1 0
  let v110 := v108 - v109
  let v112 := call0 1
  let v113 := v112 + v11
  let v115 := call1 1
  let v116 := v113 - v115
  let v118 := call0 2
  let v119 := v118 + v11
  let v121 := call1 2
  let v122 := v119 - v121
  let v124 := call0 3
  let v125 := v124 + v11
  let v127 := call1 3
  let v128 := v125 - v127
  let v130 := call0 4
  let v131 := v130 + v11
  let v133 := call1 4
  let v134 := v131 - v133
  let v135 := v110 >>> v12
  let v136 := v116 >>> v12
  let v137 := v122 >>> v12
  let v138 := v128 >>> v12
  let v139 := v134 >>> v12
  let v140 := v110 &&& v13
  let v141 := v116 &&& v13
  let v142 := v122 &&& v13
  let v143 := v128 &&& v13
  let v144 := v134 &&& v13
  let v145 := v139 * v14
  let v146 := v145 + v140
  let v147 := v141 + v135
  let v148 := v142 + v136
  let v149 := v143 + v137
  let v150 := v144 + v138
  let v151 := v109 + v107
  let v152 := v115 + v112
  let v153 := v121 + v118
  let v154 := v127 + v124
  let v155 := v133 + v130
  let v156 := call2 0
  let v157 := v156 + v102
  let v159 := call2 1
  let v160 := v159 + v103
  let v162 := call2 2
  let v163 := v162 + v104
  let v165 := call2 3
  let v166 := v165 + v105
  let v168 := call2 4
  let v169 := v168 + v106
  let v170 := v102 + v10
  let v171 := v170 - v156
  let v172 := v103 + v11
  let v173 := v172 - v159
  let v174 := v104 + v11
  let v175 := v174 - v162
  let v176 := v105 + v11
  let v177 := v176 - v165
  let v178 := v106 + v11
  let v179 := v178 - v168
  let v180 := v171 >>> v12
  let v181 := v173 >>> v12
  let v182 := v175 >>> v12
  let v183 := v177 >>> v12
  let v184 := v179 >>> v12
  let v185 := v171 &&& v13
  let v186 := v173 &&& v13
  let v187 := v175 &&& v13
  let v188 := v177 &&& v13
  let v189 := v179 &&& v13
  let v190 := v184 * v14
  let v191 := v190 + v185
  let v192 := v186 + v180
  let v193 := v187 + v181
  let v194 := v188 + v182
  let v195 := v189 + v183
  ![v146, v147, v148, v149, v150, v151, v152, v153, v154, v155, v157, v160, v163, v166, v169, v191, v192, v193, v194, v195]

private theorem addWord_vector (a b : FieldWords) :
    addWord a b = ![b 0+a 0, b 1+a 1, b 2+a 2, b 3+a 3, b 4+a 4] := by
  funext i
  fin_cases i <;> simp [addWord, add_comm]

private theorem subWord_vector (a b : FieldWords) :
    subWord a b =
      let d0 := a 0 + 36028797018963664#64 - b 0
      let d1 := a 1 + 36028797018963952#64 - b 1
      let d2 := a 2 + 36028797018963952#64 - b 2
      let d3 := a 3 + 36028797018963952#64 - b 3
      let d4 := a 4 + 36028797018963952#64 - b 4
      ![(d4 >>> 51#64)*19 + (d0 &&& 2251799813685247#64),
        (d1 &&& 2251799813685247#64) + (d0 >>> 51#64),
        (d2 &&& 2251799813685247#64) + (d1 >>> 51#64),
        (d3 &&& 2251799813685247#64) + (d2 >>> 51#64),
        (d4 &&& 2251799813685247#64) + (d3 >>> 51#64)] := by
  funext i
  fin_cases i <;> simp [subWord, weakWord, biasedSubWord, bias, add_comm]

private theorem shl_one64 (x : BitVec 64) : x <<< (1 : Nat) = x+x := by
  rw [BitVec.shiftLeft_eq_mul_twoPow]
  change x*2 = x+x
  exact BitVec.mul_two


set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem affineAddWordTrace_eq (p c : PointWords) :
    affineAddWordTrace p c = pointToWords (affineAddWord (pointFromWords p) (affineCacheFromWords c)) := by
  simp [affineAddWordTrace, affineAddWord, cachedAddWord, affineAddWord, swapXY, swapZT,
    pointToWords, pointFromWords, affineCacheFromWords, addWord_vector, subWord_vector, shl_one64]

theorem affineAddWordTrace_unsigned (p c : PointWords)
    (hp : PointTight (unsignedPoint (pointFromWords p)))
    (hc : PointBounded (unsignedPoint (affineCacheFromWords c))) :
    unsignedPoint (pointFromWords (affineAddWordTrace p c)) =
      affineAddCompleted (unsignedPoint (pointFromWords p)) (unsigned (affineCacheFromWords c).X) (unsigned (affineCacheFromWords c).Y) (unsigned (affineCacheFromWords c).T) := by
  rw [affineAddWordTrace_eq, pointFromWords_toWords]
  exact affineAddWord_unsigned _ _ hp hc

end Agave.Ed25519.SerialPoint.Execution
