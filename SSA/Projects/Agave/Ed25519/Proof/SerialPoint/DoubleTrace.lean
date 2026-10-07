import SSA.Projects.Agave.Ed25519.Proof.SerialPoint.DoubleWord
import SSA.Projects.Agave.Ed25519.Proof.SerialPoint.PointLayout

namespace Agave.Ed25519.SerialPoint.Execution
open SerialFieldMul

attribute [local irreducible] machine squareMachine

/-- Exact word operations and four square calls of the pinned double body.
The two-lane loads/adds/stores are represented by their respective lane words. -/
def doubleWordTrace (p : PointWords) : PointWords :=
  let v0 : BitVec 32 := 1
  let v1 : BitVec 64 := 40
  let v2 : BitVec 64 := 80
  let v3 : BitVec 64 := 1
  let v4 : BitVec 64 := 8
  let v5 : BitVec 64 := 16
  let v6 : BitVec 64 := 24
  let v7 : BitVec 64 := 32
  let v8 : BitVec 64 := 56
  let v9 : BitVec 64 := 72
  let v10 : BitVec 64 := 36028797018963664
  let v11 : BitVec 64 := 36028797018963952
  let v12 : BitVec 64 := 51
  let v13 : BitVec 64 := 2251799813685247
  let v14 : BitVec 64 := 19
  let v15 : BitVec 64 := 48
  let v16 : BitVec 64 := 64
  let v17 : BitVec 64 := 88
  let v18 : BitVec 64 := 96
  let v19 : BitVec 64 := 104
  let v20 : BitVec 64 := 112
  let v21 : BitVec 64 := 120
  let v22 : BitVec 64 := 128
  let v23 : BitVec 64 := 136
  let v24 : BitVec 64 := 144
  let v25 : BitVec 64 := 152
  let call0 := squareMachine (![p 0, p 1, p 2, p 3, p 4])
  let call1 := squareMachine (![p 5, p 6, p 7, p 8, p 9])
  let call2 := squareMachine (![p 10, p 11, p 12, p 13, p 14])
  let v33 := call2 0
  let v34 := v33 <<< v3
  let v36 := call2 1
  let v37 := v36 <<< v3
  let v39 := call2 2
  let v40 := v39 <<< v3
  let v42 := call2 3
  let v43 := v42 <<< v3
  let v45 := call2 4
  let v46 := v45 <<< v3
  let v49 := p 4
  let v52 := p 9
  let v53 := v52 + v49
  let v54_0 := p 0
  let v54_1 := p 1
  let v55_0 := p 5
  let v55_1 := p 6
  let v56_0 := v55_0 + v54_0
  let v56_1 := v55_1 + v54_1
  let v58_0 := p 2
  let v58_1 := p 3
  let v59_0 := p 7
  let v59_1 := p 8
  let v60_0 := v59_0 + v58_0
  let v60_1 := v59_1 + v58_1
  let call3 := squareMachine (![v56_0, v56_1, v60_0, v60_1, v53])
  let v62 := call1 0
  let v64 := call1 1
  let v66 := call1 2
  let v68 := call1 3
  let v70 := call1 4
  let v71 := call0 0
  let v72 := v71 + v62
  let v74 := call0 1
  let v75 := v74 + v64
  let v77 := call0 2
  let v78 := v77 + v66
  let v80 := call0 3
  let v81 := v80 + v68
  let v83 := call0 4
  let v84 := v83 + v70
  let v85 := v62 + v10
  let v86 := v85 - v71
  let v87 := v64 + v11
  let v88 := v87 - v74
  let v89 := v66 + v11
  let v90 := v89 - v77
  let v91 := v68 + v11
  let v92 := v91 - v80
  let v93 := v70 + v11
  let v94 := v93 - v83
  let v95 := v86 >>> v12
  let v96 := v88 >>> v12
  let v97 := v90 >>> v12
  let v98 := v92 >>> v12
  let v99 := v94 >>> v12
  let v100 := v86 &&& v13
  let v101 := v88 &&& v13
  let v102 := v90 &&& v13
  let v103 := v92 &&& v13
  let v104 := v94 &&& v13
  let v105 := v99 * v14
  let v106 := v105 + v100
  let v107 := v101 + v95
  let v108 := v102 + v96
  let v109 := v103 + v97
  let v110 := v104 + v98
  let v111 := call3 0
  let v112 := v111 - v72
  let v113 := v112 + v10
  let v115 := call3 1
  let v116 := v115 - v75
  let v117 := v116 + v11
  let v119 := call3 2
  let v120 := v119 - v78
  let v121 := v120 + v11
  let v123 := call3 3
  let v124 := v123 - v81
  let v125 := v124 + v11
  let v127 := call3 4
  let v128 := v127 - v84
  let v129 := v128 + v11
  let v130 := v113 >>> v12
  let v131 := v117 >>> v12
  let v132 := v121 >>> v12
  let v133 := v125 >>> v12
  let v134 := v129 >>> v12
  let v135 := v113 &&& v13
  let v136 := v117 &&& v13
  let v137 := v121 &&& v13
  let v138 := v125 &&& v13
  let v139 := v129 &&& v13
  let v140 := v134 * v14
  let v141 := v140 + v135
  let v142 := v136 + v130
  let v143 := v137 + v131
  let v144 := v138 + v132
  let v145 := v139 + v133
  let v146 := v34 + v10
  let v147 := v146 - v106
  let v148 := v37 + v11
  let v149 := v148 - v107
  let v150 := v40 + v11
  let v151 := v150 - v108
  let v152 := v43 + v11
  let v153 := v152 - v109
  let v154 := v46 + v11
  let v155 := v154 - v110
  let v156 := v147 >>> v12
  let v157 := v149 >>> v12
  let v158 := v151 >>> v12
  let v159 := v153 >>> v12
  let v160 := v155 >>> v12
  let v161 := v147 &&& v13
  let v162 := v149 &&& v13
  let v163 := v151 &&& v13
  let v164 := v153 &&& v13
  let v165 := v155 &&& v13
  let v166 := v160 * v14
  let v167 := v166 + v161
  let v168 := v156 + v162
  let v169 := v163 + v157
  let v170 := v164 + v158
  let v171 := v165 + v159
  ![v141, v142, v143, v144, v145, v72, v75, v78, v81, v84, v106, v107, v108, v109, v110, v167, v168, v169, v170, v171]

private theorem shl_one64 (x : BitVec 64) : x <<< (1 : Nat) = x+x := by
  rw [BitVec.shiftLeft_eq_mul_twoPow]
  change x*2 = x+x
  exact BitVec.mul_two

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

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1000000 in
theorem doubleWordTrace_eq (p : PointWords) :
    doubleWordTrace p = pointToWords (doubleWord (pointFromWords p)) := by
  simp [doubleWordTrace, doubleWord, pointToWords, pointFromWords,
    addWord_vector, subWord_vector, shl_one64, sub_add_eq_add_sub]
  exact add_comm _ _

theorem doubleWordTrace_unsigned (p : PointWords)
    (hp : PointTight (unsignedPoint (pointFromWords p))) :
    unsignedPoint (pointFromWords (doubleWordTrace p)) =
      doubleCompleted (unsignedPoint (pointFromWords p)) := by
  rw [doubleWordTrace_eq, pointFromWords_toWords]
  exact doubleWord_unsigned _ hp

theorem doubleWordTrace_projective_unsigned (p : PointWords)
    (hp : ProjectiveTight (unsignedPoint (pointFromWords p))) :
    unsignedPoint (pointFromWords (doubleWordTrace p)) =
      doubleCompleted (unsignedPoint (pointFromWords p)) := by
  rw [doubleWordTrace_eq, pointFromWords_toWords]
  exact doubleWord_projective_unsigned _ hp

end Agave.Ed25519.SerialPoint.Execution
