import SSA.Projects.Agave.Ed25519.Proof.SerialPoint.PointLayout

namespace Agave.Ed25519.SerialPoint.Execution
open SerialFieldMul

attribute [local irreducible] machine

/-- Exact compiler order of cached-add word arithmetic and its four field calls. -/
def cachedAddWordTrace (p c : PointWords) : PointWords :=
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
  let v17 : BitVec 64 := 1
  let v18 : BitVec 64 := 88
  let v19 : BitVec 64 := 96
  let v20 : BitVec 64 := 104
  let v21 : BitVec 64 := 112
  let v22 : BitVec 64 := 128
  let v23 : BitVec 64 := 136
  let v24 : BitVec 64 := 144
  let v25 : BitVec 64 := 152
  let v33 := p 5
  let v35 := p 6
  let v37 := p 7
  let v39 := p 8
  let v41 := p 9
  let v42 := p 0
  let v43 := v42 + v33
  let v45 := p 1
  let v46 := v45 + v35
  let v48 := p 2
  let v49 := v48 + v37
  let v51 := p 3
  let v52 := v51 + v39
  let v54 := p 4
  let v55 := v54 + v41
  let v60 := v33 + v10
  let v61 := v60 - v42
  let v62 := v35 + v11
  let v63 := v62 - v45
  let v64 := v37 + v11
  let v65 := v64 - v48
  let v66 := v39 + v11
  let v67 := v66 - v51
  let v68 := v41 + v11
  let v69 := v68 - v54
  let v70 := v61 >>> v12
  let v71 := v63 >>> v12
  let v72 := v65 >>> v12
  let v73 := v67 >>> v12
  let v74 := v69 >>> v12
  let v75 := v61 &&& v13
  let v76 := v63 &&& v13
  let v77 := v65 &&& v13
  let v78 := v67 &&& v13
  let v79 := v69 &&& v13
  let v80 := v74 * v14
  let v81 := v80 + v75
  let v82 := v76 + v70
  let v83 := v77 + v71
  let v84 := v78 + v72
  let v85 := v79 + v73
  let call0 := machine (![v43, v46, v49, v52, v55]) (![c 0, c 1, c 2, c 3, c 4])
  let call1 := machine (![v81, v82, v83, v84, v85]) (![c 5, c 6, c 7, c 8, c 9])
  let call2 := machine (![p 15, p 16, p 17, p 18, p 19]) (![c 15, c 16, c 17, c 18, c 19])
  let call3 := machine (![p 10, p 11, p 12, p 13, p 14]) (![c 10, c 11, c 12, c 13, c 14])
  let v95 := call3 0
  let v97 := call3 1
  let v99 := call3 2
  let v101 := call3 3
  let v103 := call3 4
  let v104 := v95 <<< v17
  let v105 := v97 <<< v17
  let v106 := v99 <<< v17
  let v107 := v101 <<< v17
  let v108 := v103 <<< v17
  let v109 := call0 0
  let v110 := v109 + v10
  let v111 := call1 0
  let v112 := v110 - v111
  let v114 := call0 1
  let v115 := v114 + v11
  let v117 := call1 1
  let v118 := v115 - v117
  let v120 := call0 2
  let v121 := v120 + v11
  let v123 := call1 2
  let v124 := v121 - v123
  let v126 := call0 3
  let v127 := v126 + v11
  let v129 := call1 3
  let v130 := v127 - v129
  let v132 := call0 4
  let v133 := v132 + v11
  let v135 := call1 4
  let v136 := v133 - v135
  let v137 := v112 >>> v12
  let v138 := v118 >>> v12
  let v139 := v124 >>> v12
  let v140 := v130 >>> v12
  let v141 := v136 >>> v12
  let v142 := v112 &&& v13
  let v143 := v118 &&& v13
  let v144 := v124 &&& v13
  let v145 := v130 &&& v13
  let v146 := v136 &&& v13
  let v147 := v141 * v14
  let v148 := v147 + v142
  let v149 := v143 + v137
  let v150 := v144 + v138
  let v151 := v145 + v139
  let v152 := v146 + v140
  let v153 := v111 + v109
  let v154 := v117 + v114
  let v155 := v123 + v120
  let v156 := v129 + v126
  let v157 := v135 + v132
  let v158 := call2 0
  let v159 := v158 + v104
  let v161 := call2 1
  let v162 := v161 + v105
  let v164 := call2 2
  let v165 := v164 + v106
  let v167 := call2 3
  let v168 := v167 + v107
  let v170 := call2 4
  let v171 := v170 + v108
  let v172 := v104 + v10
  let v173 := v172 - v158
  let v174 := v105 + v11
  let v175 := v174 - v161
  let v176 := v106 + v11
  let v177 := v176 - v164
  let v178 := v107 + v11
  let v179 := v178 - v167
  let v180 := v108 + v11
  let v181 := v180 - v170
  let v182 := v173 >>> v12
  let v183 := v175 >>> v12
  let v184 := v177 >>> v12
  let v185 := v179 >>> v12
  let v186 := v181 >>> v12
  let v187 := v173 &&& v13
  let v188 := v175 &&& v13
  let v189 := v177 &&& v13
  let v190 := v179 &&& v13
  let v191 := v181 &&& v13
  let v192 := v186 * v14
  let v193 := v192 + v187
  let v194 := v188 + v182
  let v195 := v189 + v183
  let v196 := v190 + v184
  let v197 := v191 + v185
  ![v148, v149, v150, v151, v152, v153, v154, v155, v156, v157, v159, v162, v165, v168, v171, v193, v194, v195, v196, v197]

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
/-- Compiler temporaries, carries, shifts and the four field calls give exactly
our coordinate word schedule, with the physical cache permutation applied. -/
theorem cachedAddWordTrace_eq (p c : PointWords) :
    cachedAddWordTrace p c = pointToWords (cachedAddWord (pointFromWords p) (cacheFromWords c)) := by
  simp [cachedAddWordTrace, cachedAddWord, pointToWords, pointFromWords,
    cacheFromWords, addWord_vector, subWord_vector, shl_one64]


/-- The exact flat compiler word trace refines the previously proved natural
cached-add formula, deriving every arithmetic bound from the caller invariant. -/
theorem cachedAddWordTrace_unsigned (p c : PointWords)
    (hp : PointTight (unsignedPoint (pointFromWords p)))
    (hc : PointBounded (unsignedPoint (cacheFromWords c))) :
    unsignedPoint (pointFromWords (cachedAddWordTrace p c)) =
      cachedAddCompleted (unsignedPoint (pointFromWords p))
        (unsignedPoint (cacheFromWords c)) := by
  rw [cachedAddWordTrace_eq, pointFromWords_toWords]
  exact cachedAddWord_unsigned _ _ hp hc

end Agave.Ed25519.SerialPoint.Execution
