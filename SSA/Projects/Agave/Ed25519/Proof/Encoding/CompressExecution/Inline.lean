import SSA.Projects.Agave.Ed25519.Proof.Encoding.CompressExecution.NormalizationInputs
import SSA.Projects.Agave.Ed25519.Proof.Encoding.CompressExecution.Sign
import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.ToBytesMemory
import SSA.Projects.Agave.Ed25519.Proof.SerialFieldMul.Execution

/-! Instructions 81–239 of the exact compressor: affine loads and both inline
canonicalizers. `NormalizationSafety` isolates each flagged scalar operation;
it contains no execution or encoding conclusion. Most obligations are the
already proved field serializer promises; the x parity shortcut is separate. -/
namespace Agave.Ed25519.Encoding.Compress.Execution
open LeanMLIR.RIR
open Reduce64.Execution (SmallRange)
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

def inlineYBytes (y : Field.Serial) : Fin 32 → BitVec 8 :=
  let v63 : BitVec 64 := y 0
  let v65 : BitVec 64 := y 1
  let v67 : BitVec 64 := y 2
  let v69 : BitVec 64 := y 3
  let v71 : BitVec 64 := y 4
  let v72 : BitVec 64 := v63 >>> 51
  let v73 : BitVec 64 := v65 >>> 51
  let v74 : BitVec 64 := v67 >>> 51
  let v75 : BitVec 64 := v69 >>> 51
  let v76 : BitVec 64 := v71 >>> 51
  let v77 : BitVec 64 := v63 &&& 2251799813685247#64
  let v78 : BitVec 64 := v65 &&& 2251799813685247#64
  let v79 : BitVec 64 := v67 &&& 2251799813685247#64
  let v80 : BitVec 64 := v69 &&& 2251799813685247#64
  let v81 : BitVec 64 := v71 &&& 2251799813685247#64
  let v82 : BitVec 64 := v76 * 19#64
  let v83 : BitVec 64 := v82 + v77
  let v84 : BitVec 64 := v78 + v72
  let v85 : BitVec 64 := v79 + v73
  let v86 : BitVec 64 := v80 + v74
  let v87 : BitVec 64 := v81 + v75
  let v88 : BitVec 64 := v83 + 19#64
  let v89 : BitVec 64 := v88 >>> 51
  let v90 : BitVec 64 := v89 + v84
  let v91 : BitVec 64 := v90 >>> 51
  let v92 : BitVec 64 := v91 + v85
  let v93 : BitVec 64 := v92 >>> 51
  let v94 : BitVec 64 := v93 + v86
  let v95 : BitVec 64 := v94 >>> 51
  let v96 : BitVec 64 := v95 + v87
  let v97 : BitVec 64 := v96 >>> 51
  let v98 : BitVec 64 := v97 * 19#64
  let v99 : BitVec 64 := v98 + v83
  let v100 : BitVec 64 := v99 >>> 51
  let v101 : BitVec 64 := v100 + v84
  let v102 : BitVec 64 := v101 >>> 51
  let v103 : BitVec 64 := v102 + v85
  let v104 : BitVec 64 := v101 &&& 2251799813685247#64
  let v105 : BitVec 64 := v103 >>> 51
  let v106 : BitVec 64 := v105 + v86
  let v107 : BitVec 64 := v103 &&& 2251799813685247#64
  let v108 : BitVec 64 := v106 >>> 51
  let v109 : BitVec 64 := v108 + v87
  let v110 : BitVec 64 := v106 &&& 2251799813685247#64
  let v111 : BitVec 64 := v109 &&& 2251799813685247#64
  let v112 : BitVec 8 := (v99).setWidth 8
  let v113 : BitVec 64 := v99 >>> 8
  let v114 : BitVec 8 := (v113).setWidth 8
  let v115 : BitVec 64 := v99 >>> 16
  let v116 : BitVec 8 := (v115).setWidth 8
  let v117 : BitVec 64 := v99 >>> 24
  let v118 : BitVec 8 := (v117).setWidth 8
  let v119 : BitVec 64 := v99 >>> 32
  let v120 : BitVec 8 := (v119).setWidth 8
  let v121 : BitVec 64 := v99 >>> 40
  let v122 : BitVec 8 := (v121).setWidth 8
  let v123 : BitVec 64 := v99 >>> 48
  let v124 : BitVec 64 := v123 &&& 7#64
  let v125 : BitVec 64 := v104 <<< 3
  let v126 : BitVec 64 := v125 ||| v124
  let v127 : BitVec 8 := (v126).setWidth 8
  let v128 : BitVec 64 := v101 >>> 5
  let v129 : BitVec 8 := (v128).setWidth 8
  let v130 : BitVec 64 := v101 >>> 13
  let v131 : BitVec 8 := (v130).setWidth 8
  let v132 : BitVec 64 := v101 >>> 21
  let v133 : BitVec 8 := (v132).setWidth 8
  let v134 : BitVec 64 := v101 >>> 29
  let v135 : BitVec 8 := (v134).setWidth 8
  let v136 : BitVec 64 := v101 >>> 37
  let v137 : BitVec 8 := (v136).setWidth 8
  let v138 : BitVec 64 := v104 >>> 45
  let v139 : BitVec 64 := v107 <<< 6
  let v140 : BitVec 64 := v139 ||| v138
  let v141 : BitVec 8 := (v140).setWidth 8
  let v142 : BitVec 64 := v103 >>> 2
  let v143 : BitVec 8 := (v142).setWidth 8
  let v144 : BitVec 64 := v103 >>> 10
  let v145 : BitVec 8 := (v144).setWidth 8
  let v146 : BitVec 64 := v103 >>> 18
  let v147 : BitVec 8 := (v146).setWidth 8
  let v148 : BitVec 64 := v103 >>> 26
  let v149 : BitVec 8 := (v148).setWidth 8
  let v150 : BitVec 64 := v103 >>> 34
  let v151 : BitVec 8 := (v150).setWidth 8
  let v152 : BitVec 64 := v103 >>> 42
  let v153 : BitVec 8 := (v152).setWidth 8
  let v154 : BitVec 64 := v107 >>> 50
  let v155 : BitVec 64 := v110 <<< 1
  let v156 : BitVec 64 := v155 ||| v154
  let v157 : BitVec 8 := (v156).setWidth 8
  let v158 : BitVec 64 := v106 >>> 7
  let v159 : BitVec 8 := (v158).setWidth 8
  let v160 : BitVec 64 := v106 >>> 15
  let v161 : BitVec 8 := (v160).setWidth 8
  let v162 : BitVec 64 := v106 >>> 23
  let v163 : BitVec 8 := (v162).setWidth 8
  let v164 : BitVec 64 := v106 >>> 31
  let v165 : BitVec 8 := (v164).setWidth 8
  let v166 : BitVec 64 := v106 >>> 39
  let v167 : BitVec 8 := (v166).setWidth 8
  let v168 : BitVec 64 := v110 >>> 47
  let v169 : BitVec 64 := v111 <<< 4
  let v170 : BitVec 64 := v169 ||| v168
  let v171 : BitVec 8 := (v170).setWidth 8
  let v172 : BitVec 64 := v109 >>> 4
  let v173 : BitVec 8 := (v172).setWidth 8
  let v174 : BitVec 64 := v109 >>> 12
  let v175 : BitVec 8 := (v174).setWidth 8
  let v176 : BitVec 64 := v109 >>> 20
  let v177 : BitVec 8 := (v176).setWidth 8
  let v178 : BitVec 64 := v109 >>> 28
  let v179 : BitVec 8 := (v178).setWidth 8
  let v180 : BitVec 64 := v109 >>> 36
  let v181 : BitVec 8 := (v180).setWidth 8
  let v182 : BitVec 64 := v111 >>> 44
  let v183 : BitVec 8 := (v182).setWidth 8
  ![v112, v114, v116, v118, v120, v122, v127, v129, v131, v133, v135, v137, v141, v143, v145, v147, v149, v151, v153, v157, v159, v161, v163, v165, v167, v171, v173, v175, v177, v179, v181, v183]

def inlineParity (x : Field.Serial) : BitVec 8 :=
  let v184 : BitVec 64 := x 0
  let v186 : BitVec 64 := x 1
  let v188 : BitVec 64 := x 2
  let v190 : BitVec 64 := x 3
  let v192 : BitVec 64 := x 4
  let v193 : BitVec 64 := v184 >>> 51
  let v194 : BitVec 64 := v186 >>> 51
  let v195 : BitVec 64 := v188 >>> 51
  let v196 : BitVec 64 := v190 >>> 51
  let v197 : BitVec 64 := v192 >>> 51
  let v198 : BitVec 64 := v184 &&& 2251799813685247#64
  let v199 : BitVec 64 := v186 &&& 2251799813685247#64
  let v200 : BitVec 64 := v188 &&& 2251799813685247#64
  let v201 : BitVec 64 := v190 &&& 2251799813685247#64
  let v202 : BitVec 64 := v192 &&& 2251799813685247#64
  let v203 : BitVec 64 := v197 * 19#64
  let v204 : BitVec 64 := v203 + v198
  let v205 : BitVec 64 := v199 + v193
  let v206 : BitVec 64 := v200 + v194
  let v207 : BitVec 64 := v201 + v195
  let v208 : BitVec 64 := v202 + v196
  let v209 : BitVec 64 := v204 + 19#64
  let v210 : BitVec 64 := v209 >>> 51
  let v211 : BitVec 64 := v205 + v210
  let v212 : BitVec 64 := v211 >>> 51
  let v213 : BitVec 64 := v206 + v212
  let v214 : BitVec 64 := v213 >>> 51
  let v215 : BitVec 64 := v207 + v214
  let v216 : BitVec 64 := v215 >>> 51
  let v217 : BitVec 64 := v208 + v216
  let v218 : BitVec 64 := v217 >>> 51
  let v219 : BitVec 64 := v218 + v204
  let v220 : BitVec 8 := (v219).setWidth 8
  let v221 : BitVec 8 := v220 &&& 1#8
  v221

def normalizedEnv (E : Env program.Γ) (temp : Pointer) (x y : Field.Serial) : Env program.Γ :=
  let v63 : BitVec 64 := y 0
  let v64 : Pointer := temp.add 48
  let v65 : BitVec 64 := y 1
  let v66 : Pointer := temp.add 56
  let v67 : BitVec 64 := y 2
  let v68 : Pointer := temp.add 64
  let v69 : BitVec 64 := y 3
  let v70 : Pointer := temp.add 72
  let v71 : BitVec 64 := y 4
  let v72 : BitVec 64 := v63 >>> 51
  let v73 : BitVec 64 := v65 >>> 51
  let v74 : BitVec 64 := v67 >>> 51
  let v75 : BitVec 64 := v69 >>> 51
  let v76 : BitVec 64 := v71 >>> 51
  let v77 : BitVec 64 := v63 &&& 2251799813685247#64
  let v78 : BitVec 64 := v65 &&& 2251799813685247#64
  let v79 : BitVec 64 := v67 &&& 2251799813685247#64
  let v80 : BitVec 64 := v69 &&& 2251799813685247#64
  let v81 : BitVec 64 := v71 &&& 2251799813685247#64
  let v82 : BitVec 64 := v76 * 19#64
  let v83 : BitVec 64 := v82 + v77
  let v84 : BitVec 64 := v78 + v72
  let v85 : BitVec 64 := v79 + v73
  let v86 : BitVec 64 := v80 + v74
  let v87 : BitVec 64 := v81 + v75
  let v88 : BitVec 64 := v83 + 19#64
  let v89 : BitVec 64 := v88 >>> 51
  let v90 : BitVec 64 := v89 + v84
  let v91 : BitVec 64 := v90 >>> 51
  let v92 : BitVec 64 := v91 + v85
  let v93 : BitVec 64 := v92 >>> 51
  let v94 : BitVec 64 := v93 + v86
  let v95 : BitVec 64 := v94 >>> 51
  let v96 : BitVec 64 := v95 + v87
  let v97 : BitVec 64 := v96 >>> 51
  let v98 : BitVec 64 := v97 * 19#64
  let v99 : BitVec 64 := v98 + v83
  let v100 : BitVec 64 := v99 >>> 51
  let v101 : BitVec 64 := v100 + v84
  let v102 : BitVec 64 := v101 >>> 51
  let v103 : BitVec 64 := v102 + v85
  let v104 : BitVec 64 := v101 &&& 2251799813685247#64
  let v105 : BitVec 64 := v103 >>> 51
  let v106 : BitVec 64 := v105 + v86
  let v107 : BitVec 64 := v103 &&& 2251799813685247#64
  let v108 : BitVec 64 := v106 >>> 51
  let v109 : BitVec 64 := v108 + v87
  let v110 : BitVec 64 := v106 &&& 2251799813685247#64
  let v111 : BitVec 64 := v109 &&& 2251799813685247#64
  let v112 : BitVec 8 := (v99).setWidth 8
  let v113 : BitVec 64 := v99 >>> 8
  let v114 : BitVec 8 := (v113).setWidth 8
  let v115 : BitVec 64 := v99 >>> 16
  let v116 : BitVec 8 := (v115).setWidth 8
  let v117 : BitVec 64 := v99 >>> 24
  let v118 : BitVec 8 := (v117).setWidth 8
  let v119 : BitVec 64 := v99 >>> 32
  let v120 : BitVec 8 := (v119).setWidth 8
  let v121 : BitVec 64 := v99 >>> 40
  let v122 : BitVec 8 := (v121).setWidth 8
  let v123 : BitVec 64 := v99 >>> 48
  let v124 : BitVec 64 := v123 &&& 7#64
  let v125 : BitVec 64 := v104 <<< 3
  let v126 : BitVec 64 := v125 ||| v124
  let v127 : BitVec 8 := (v126).setWidth 8
  let v128 : BitVec 64 := v101 >>> 5
  let v129 : BitVec 8 := (v128).setWidth 8
  let v130 : BitVec 64 := v101 >>> 13
  let v131 : BitVec 8 := (v130).setWidth 8
  let v132 : BitVec 64 := v101 >>> 21
  let v133 : BitVec 8 := (v132).setWidth 8
  let v134 : BitVec 64 := v101 >>> 29
  let v135 : BitVec 8 := (v134).setWidth 8
  let v136 : BitVec 64 := v101 >>> 37
  let v137 : BitVec 8 := (v136).setWidth 8
  let v138 : BitVec 64 := v104 >>> 45
  let v139 : BitVec 64 := v107 <<< 6
  let v140 : BitVec 64 := v139 ||| v138
  let v141 : BitVec 8 := (v140).setWidth 8
  let v142 : BitVec 64 := v103 >>> 2
  let v143 : BitVec 8 := (v142).setWidth 8
  let v144 : BitVec 64 := v103 >>> 10
  let v145 : BitVec 8 := (v144).setWidth 8
  let v146 : BitVec 64 := v103 >>> 18
  let v147 : BitVec 8 := (v146).setWidth 8
  let v148 : BitVec 64 := v103 >>> 26
  let v149 : BitVec 8 := (v148).setWidth 8
  let v150 : BitVec 64 := v103 >>> 34
  let v151 : BitVec 8 := (v150).setWidth 8
  let v152 : BitVec 64 := v103 >>> 42
  let v153 : BitVec 8 := (v152).setWidth 8
  let v154 : BitVec 64 := v107 >>> 50
  let v155 : BitVec 64 := v110 <<< 1
  let v156 : BitVec 64 := v155 ||| v154
  let v157 : BitVec 8 := (v156).setWidth 8
  let v158 : BitVec 64 := v106 >>> 7
  let v159 : BitVec 8 := (v158).setWidth 8
  let v160 : BitVec 64 := v106 >>> 15
  let v161 : BitVec 8 := (v160).setWidth 8
  let v162 : BitVec 64 := v106 >>> 23
  let v163 : BitVec 8 := (v162).setWidth 8
  let v164 : BitVec 64 := v106 >>> 31
  let v165 : BitVec 8 := (v164).setWidth 8
  let v166 : BitVec 64 := v106 >>> 39
  let v167 : BitVec 8 := (v166).setWidth 8
  let v168 : BitVec 64 := v110 >>> 47
  let v169 : BitVec 64 := v111 <<< 4
  let v170 : BitVec 64 := v169 ||| v168
  let v171 : BitVec 8 := (v170).setWidth 8
  let v172 : BitVec 64 := v109 >>> 4
  let v173 : BitVec 8 := (v172).setWidth 8
  let v174 : BitVec 64 := v109 >>> 12
  let v175 : BitVec 8 := (v174).setWidth 8
  let v176 : BitVec 64 := v109 >>> 20
  let v177 : BitVec 8 := (v176).setWidth 8
  let v178 : BitVec 64 := v109 >>> 28
  let v179 : BitVec 8 := (v178).setWidth 8
  let v180 : BitVec 64 := v109 >>> 36
  let v181 : BitVec 8 := (v180).setWidth 8
  let v182 : BitVec 64 := v111 >>> 44
  let v183 : BitVec 8 := (v182).setWidth 8
  let v184 : BitVec 64 := x 0
  let v185 : Pointer := temp.add 8
  let v186 : BitVec 64 := x 1
  let v187 : Pointer := temp.add 16
  let v188 : BitVec 64 := x 2
  let v189 : Pointer := temp.add 24
  let v190 : BitVec 64 := x 3
  let v191 : Pointer := temp.add 32
  let v192 : BitVec 64 := x 4
  let v193 : BitVec 64 := v184 >>> 51
  let v194 : BitVec 64 := v186 >>> 51
  let v195 : BitVec 64 := v188 >>> 51
  let v196 : BitVec 64 := v190 >>> 51
  let v197 : BitVec 64 := v192 >>> 51
  let v198 : BitVec 64 := v184 &&& 2251799813685247#64
  let v199 : BitVec 64 := v186 &&& 2251799813685247#64
  let v200 : BitVec 64 := v188 &&& 2251799813685247#64
  let v201 : BitVec 64 := v190 &&& 2251799813685247#64
  let v202 : BitVec 64 := v192 &&& 2251799813685247#64
  let v203 : BitVec 64 := v197 * 19#64
  let v204 : BitVec 64 := v203 + v198
  let v205 : BitVec 64 := v199 + v193
  let v206 : BitVec 64 := v200 + v194
  let v207 : BitVec 64 := v201 + v195
  let v208 : BitVec 64 := v202 + v196
  let v209 : BitVec 64 := v204 + 19#64
  let v210 : BitVec 64 := v209 >>> 51
  let v211 : BitVec 64 := v205 + v210
  let v212 : BitVec 64 := v211 >>> 51
  let v213 : BitVec 64 := v206 + v212
  let v214 : BitVec 64 := v213 >>> 51
  let v215 : BitVec 64 := v207 + v214
  let v216 : BitVec 64 := v215 >>> 51
  let v217 : BitVec 64 := v208 + v216
  let v218 : BitVec 64 := v217 >>> 51
  let v219 : BitVec 64 := v218 + v204
  let v220 : BitVec 8 := (v219).setWidth 8
  let v221 : BitVec 8 := v220 &&& 1#8
  E[%63 := .value v63,
    %64 := .value v64,
    %65 := .value v65,
    %66 := .value v66,
    %67 := .value v67,
    %68 := .value v68,
    %69 := .value v69,
    %70 := .value v70,
    %71 := .value v71,
    %72 := .value v72,
    %73 := .value v73,
    %74 := .value v74,
    %75 := .value v75,
    %76 := .value v76,
    %77 := .value v77,
    %78 := .value v78,
    %79 := .value v79,
    %80 := .value v80,
    %81 := .value v81,
    %82 := .value v82,
    %83 := .value v83,
    %84 := .value v84,
    %85 := .value v85,
    %86 := .value v86,
    %87 := .value v87,
    %88 := .value v88,
    %89 := .value v89,
    %90 := .value v90,
    %91 := .value v91,
    %92 := .value v92,
    %93 := .value v93,
    %94 := .value v94,
    %95 := .value v95,
    %96 := .value v96,
    %97 := .value v97,
    %98 := .value v98,
    %99 := .value v99,
    %100 := .value v100,
    %101 := .value v101,
    %102 := .value v102,
    %103 := .value v103,
    %104 := .value v104,
    %105 := .value v105,
    %106 := .value v106,
    %107 := .value v107,
    %108 := .value v108,
    %109 := .value v109,
    %110 := .value v110,
    %111 := .value v111,
    %112 := .value v112,
    %113 := .value v113,
    %114 := .value v114,
    %115 := .value v115,
    %116 := .value v116,
    %117 := .value v117,
    %118 := .value v118,
    %119 := .value v119,
    %120 := .value v120,
    %121 := .value v121,
    %122 := .value v122,
    %123 := .value v123,
    %124 := .value v124,
    %125 := .value v125,
    %126 := .value v126,
    %127 := .value v127,
    %128 := .value v128,
    %129 := .value v129,
    %130 := .value v130,
    %131 := .value v131,
    %132 := .value v132,
    %133 := .value v133,
    %134 := .value v134,
    %135 := .value v135,
    %136 := .value v136,
    %137 := .value v137,
    %138 := .value v138,
    %139 := .value v139,
    %140 := .value v140,
    %141 := .value v141,
    %142 := .value v142,
    %143 := .value v143,
    %144 := .value v144,
    %145 := .value v145,
    %146 := .value v146,
    %147 := .value v147,
    %148 := .value v148,
    %149 := .value v149,
    %150 := .value v150,
    %151 := .value v151,
    %152 := .value v152,
    %153 := .value v153,
    %154 := .value v154,
    %155 := .value v155,
    %156 := .value v156,
    %157 := .value v157,
    %158 := .value v158,
    %159 := .value v159,
    %160 := .value v160,
    %161 := .value v161,
    %162 := .value v162,
    %163 := .value v163,
    %164 := .value v164,
    %165 := .value v165,
    %166 := .value v166,
    %167 := .value v167,
    %168 := .value v168,
    %169 := .value v169,
    %170 := .value v170,
    %171 := .value v171,
    %172 := .value v172,
    %173 := .value v173,
    %174 := .value v174,
    %175 := .value v175,
    %176 := .value v176,
    %177 := .value v177,
    %178 := .value v178,
    %179 := .value v179,
    %180 := .value v180,
    %181 := .value v181,
    %182 := .value v182,
    %183 := .value v183,
    %184 := .value v184,
    %185 := .value v185,
    %186 := .value v186,
    %187 := .value v187,
    %188 := .value v188,
    %189 := .value v189,
    %190 := .value v190,
    %191 := .value v191,
    %192 := .value v192,
    %193 := .value v193,
    %194 := .value v194,
    %195 := .value v195,
    %196 := .value v196,
    %197 := .value v197,
    %198 := .value v198,
    %199 := .value v199,
    %200 := .value v200,
    %201 := .value v201,
    %202 := .value v202,
    %203 := .value v203,
    %204 := .value v204,
    %205 := .value v205,
    %206 := .value v206,
    %207 := .value v207,
    %208 := .value v208,
    %209 := .value v209,
    %210 := .value v210,
    %211 := .value v211,
    %212 := .value v212,
    %213 := .value v213,
    %214 := .value v214,
    %215 := .value v215,
    %216 := .value v216,
    %217 := .value v217,
    %218 := .value v218,
    %219 := .value v219,
    %220 := .value v220,
    %221 := .value v221]

/-- Local poison-freedom contracts for the flagged additions,
multiplications, shifts, truncation and disjoint ORs actually emitted here.
The residual list is deliberately explicit until the matching serializer lemmas
are replayed for this inline instruction order. -/
def NormalizationSafety (x y : Field.Serial) : Prop :=
  let v63 : BitVec 64 := y 0
  let v65 : BitVec 64 := y 1
  let v67 : BitVec 64 := y 2
  let v69 : BitVec 64 := y 3
  let v71 : BitVec 64 := y 4
  let v72 : BitVec 64 := v63 >>> 51
  let v73 : BitVec 64 := v65 >>> 51
  let v74 : BitVec 64 := v67 >>> 51
  let v75 : BitVec 64 := v69 >>> 51
  let v76 : BitVec 64 := v71 >>> 51
  let v77 : BitVec 64 := v63 &&& 2251799813685247#64
  let v78 : BitVec 64 := v65 &&& 2251799813685247#64
  let v79 : BitVec 64 := v67 &&& 2251799813685247#64
  let v80 : BitVec 64 := v69 &&& 2251799813685247#64
  let v81 : BitVec 64 := v71 &&& 2251799813685247#64
  let v82 : BitVec 64 := v76 * 19#64
  let v83 : BitVec 64 := v82 + v77
  let v84 : BitVec 64 := v78 + v72
  let v85 : BitVec 64 := v79 + v73
  let v86 : BitVec 64 := v80 + v74
  let v87 : BitVec 64 := v81 + v75
  let v88 : BitVec 64 := v83 + 19#64
  let v89 : BitVec 64 := v88 >>> 51
  let v90 : BitVec 64 := v89 + v84
  let v91 : BitVec 64 := v90 >>> 51
  let v92 : BitVec 64 := v91 + v85
  let v93 : BitVec 64 := v92 >>> 51
  let v94 : BitVec 64 := v93 + v86
  let v95 : BitVec 64 := v94 >>> 51
  let v96 : BitVec 64 := v95 + v87
  let v97 : BitVec 64 := v96 >>> 51
  let v98 : BitVec 64 := v97 * 19#64
  let v99 : BitVec 64 := v98 + v83
  let v100 : BitVec 64 := v99 >>> 51
  let v101 : BitVec 64 := v100 + v84
  let v102 : BitVec 64 := v101 >>> 51
  let v103 : BitVec 64 := v102 + v85
  let v104 : BitVec 64 := v101 &&& 2251799813685247#64
  let v105 : BitVec 64 := v103 >>> 51
  let v106 : BitVec 64 := v105 + v86
  let v107 : BitVec 64 := v103 &&& 2251799813685247#64
  let v108 : BitVec 64 := v106 >>> 51
  let v109 : BitVec 64 := v108 + v87
  let v110 : BitVec 64 := v106 &&& 2251799813685247#64
  let v111 : BitVec 64 := v109 &&& 2251799813685247#64
  let v112 : BitVec 8 := (v99).setWidth 8
  let v113 : BitVec 64 := v99 >>> 8
  let v114 : BitVec 8 := (v113).setWidth 8
  let v115 : BitVec 64 := v99 >>> 16
  let v116 : BitVec 8 := (v115).setWidth 8
  let v117 : BitVec 64 := v99 >>> 24
  let v118 : BitVec 8 := (v117).setWidth 8
  let v119 : BitVec 64 := v99 >>> 32
  let v120 : BitVec 8 := (v119).setWidth 8
  let v121 : BitVec 64 := v99 >>> 40
  let v122 : BitVec 8 := (v121).setWidth 8
  let v123 : BitVec 64 := v99 >>> 48
  let v124 : BitVec 64 := v123 &&& 7#64
  let v125 : BitVec 64 := v104 <<< 3
  let v126 : BitVec 64 := v125 ||| v124
  let v127 : BitVec 8 := (v126).setWidth 8
  let v128 : BitVec 64 := v101 >>> 5
  let v129 : BitVec 8 := (v128).setWidth 8
  let v130 : BitVec 64 := v101 >>> 13
  let v131 : BitVec 8 := (v130).setWidth 8
  let v132 : BitVec 64 := v101 >>> 21
  let v133 : BitVec 8 := (v132).setWidth 8
  let v134 : BitVec 64 := v101 >>> 29
  let v135 : BitVec 8 := (v134).setWidth 8
  let v136 : BitVec 64 := v101 >>> 37
  let v137 : BitVec 8 := (v136).setWidth 8
  let v138 : BitVec 64 := v104 >>> 45
  let v139 : BitVec 64 := v107 <<< 6
  let v140 : BitVec 64 := v139 ||| v138
  let v141 : BitVec 8 := (v140).setWidth 8
  let v142 : BitVec 64 := v103 >>> 2
  let v143 : BitVec 8 := (v142).setWidth 8
  let v144 : BitVec 64 := v103 >>> 10
  let v145 : BitVec 8 := (v144).setWidth 8
  let v146 : BitVec 64 := v103 >>> 18
  let v147 : BitVec 8 := (v146).setWidth 8
  let v148 : BitVec 64 := v103 >>> 26
  let v149 : BitVec 8 := (v148).setWidth 8
  let v150 : BitVec 64 := v103 >>> 34
  let v151 : BitVec 8 := (v150).setWidth 8
  let v152 : BitVec 64 := v103 >>> 42
  let v153 : BitVec 8 := (v152).setWidth 8
  let v154 : BitVec 64 := v107 >>> 50
  let v155 : BitVec 64 := v110 <<< 1
  let v156 : BitVec 64 := v155 ||| v154
  let v157 : BitVec 8 := (v156).setWidth 8
  let v158 : BitVec 64 := v106 >>> 7
  let v159 : BitVec 8 := (v158).setWidth 8
  let v160 : BitVec 64 := v106 >>> 15
  let v161 : BitVec 8 := (v160).setWidth 8
  let v162 : BitVec 64 := v106 >>> 23
  let v163 : BitVec 8 := (v162).setWidth 8
  let v164 : BitVec 64 := v106 >>> 31
  let v165 : BitVec 8 := (v164).setWidth 8
  let v166 : BitVec 64 := v106 >>> 39
  let v167 : BitVec 8 := (v166).setWidth 8
  let v168 : BitVec 64 := v110 >>> 47
  let v169 : BitVec 64 := v111 <<< 4
  let v170 : BitVec 64 := v169 ||| v168
  let v171 : BitVec 8 := (v170).setWidth 8
  let v172 : BitVec 64 := v109 >>> 4
  let v173 : BitVec 8 := (v172).setWidth 8
  let v174 : BitVec 64 := v109 >>> 12
  let v175 : BitVec 8 := (v174).setWidth 8
  let v176 : BitVec 64 := v109 >>> 20
  let v177 : BitVec 8 := (v176).setWidth 8
  let v178 : BitVec 64 := v109 >>> 28
  let v179 : BitVec 8 := (v178).setWidth 8
  let v180 : BitVec 64 := v109 >>> 36
  let v181 : BitVec 8 := (v180).setWidth 8
  let v182 : BitVec 64 := v111 >>> 44
  let v183 : BitVec 8 := (v182).setWidth 8
  let v184 : BitVec 64 := x 0
  let v186 : BitVec 64 := x 1
  let v188 : BitVec 64 := x 2
  let v190 : BitVec 64 := x 3
  let v192 : BitVec 64 := x 4
  let v193 : BitVec 64 := v184 >>> 51
  let v194 : BitVec 64 := v186 >>> 51
  let v195 : BitVec 64 := v188 >>> 51
  let v196 : BitVec 64 := v190 >>> 51
  let v197 : BitVec 64 := v192 >>> 51
  let v198 : BitVec 64 := v184 &&& 2251799813685247#64
  let v199 : BitVec 64 := v186 &&& 2251799813685247#64
  let v200 : BitVec 64 := v188 &&& 2251799813685247#64
  let v201 : BitVec 64 := v190 &&& 2251799813685247#64
  let v202 : BitVec 64 := v192 &&& 2251799813685247#64
  let v203 : BitVec 64 := v197 * 19#64
  let v204 : BitVec 64 := v203 + v198
  let v205 : BitVec 64 := v199 + v193
  let v206 : BitVec 64 := v200 + v194
  let v207 : BitVec 64 := v201 + v195
  let v208 : BitVec 64 := v202 + v196
  let v209 : BitVec 64 := v204 + 19#64
  let v210 : BitVec 64 := v209 >>> 51
  let v211 : BitVec 64 := v205 + v210
  let v212 : BitVec 64 := v211 >>> 51
  let v213 : BitVec 64 := v206 + v212
  let v214 : BitVec 64 := v213 >>> 51
  let v215 : BitVec 64 := v207 + v214
  let v216 : BitVec 64 := v215 >>> 51
  let v217 : BitVec 64 := v208 + v216
  let v218 : BitVec 64 := v217 >>> 51
  let v219 : BitVec 64 := v218 + v204
  let v220 : BitVec 8 := (v219).setWidth 8
  let v221 : BitVec 8 := v220 &&& 1#8
  Operation.mul {nsw := true, nuw := true} (.value v76) (.value 19#64) = (.value (v76 * 19#64)) ∧
  Operation.add {nsw := true, nuw := true} (.value v82) (.value v77) = (.value (v82 + v77)) ∧
  Operation.add {nsw := true, nuw := true} (.value v78) (.value v72) = (.value (v78 + v72)) ∧
  Operation.add {nsw := true, nuw := true} (.value v79) (.value v73) = (.value (v79 + v73)) ∧
  Operation.add {nsw := true, nuw := true} (.value v80) (.value v74) = (.value (v80 + v74)) ∧
  Operation.add {nsw := true, nuw := true} (.value v81) (.value v75) = (.value (v81 + v75)) ∧
  Operation.add {nsw := true, nuw := true} (.value v83) (.value 19#64) = (.value (v83 + 19#64)) ∧
  Operation.add {nsw := true, nuw := true} (.value v89) (.value v84) = (.value (v89 + v84)) ∧
  Operation.add {nsw := true, nuw := true} (.value v91) (.value v85) = (.value (v91 + v85)) ∧
  Operation.add {nsw := true, nuw := true} (.value v93) (.value v86) = (.value (v93 + v86)) ∧
  Operation.add {nsw := true, nuw := true} (.value v95) (.value v87) = (.value (v95 + v87)) ∧
  Operation.mul {nsw := true, nuw := true} (.value v97) (.value 19#64) = (.value (v97 * 19#64)) ∧
  Operation.add {nsw := true, nuw := true} (.value v98) (.value v83) = (.value (v98 + v83)) ∧
  Operation.add {nsw := true, nuw := true} (.value v100) (.value v84) = (.value (v100 + v84)) ∧
  Operation.add {nsw := true, nuw := true} (.value v102) (.value v85) = (.value (v102 + v85)) ∧
  Operation.add {nsw := true, nuw := true} (.value v105) (.value v86) = (.value (v105 + v86)) ∧
  Operation.add {nsw := true, nuw := true} (.value v108) (.value v87) = (.value (v108 + v87)) ∧
  Operation.shl {nsw := true, nuw := true} (.value v104) (.value 3#64) = (.value (v104 <<< 3)) ∧
  Operation.or true (.value v125) (.value v124) = .value (v125 ||| v124) ∧
  Operation.shl {nsw := true, nuw := true} (.value v107) (.value 6#64) = (.value (v107 <<< 6)) ∧
  Operation.or true (.value v139) (.value v138) = .value (v139 ||| v138) ∧
  Operation.shl {nsw := true, nuw := true} (.value v110) (.value 1#64) = (.value (v110 <<< 1)) ∧
  Operation.or true (.value v155) (.value v154) = .value (v155 ||| v154) ∧
  Operation.shl {nsw := true, nuw := true} (.value v111) (.value 4#64) = (.value (v111 <<< 4)) ∧
  Operation.or true (.value v169) (.value v168) = .value (v169 ||| v168) ∧
  Operation.trunc {nsw := true, nuw := true} (.value v182) = (.value ((v182).setWidth 8)) ∧
  Operation.mul {nsw := true, nuw := true} (.value v197) (.value 19#64) = (.value (v197 * 19#64)) ∧
  Operation.add {nsw := true, nuw := true} (.value v203) (.value v198) = (.value (v203 + v198)) ∧
  Operation.add {nsw := true, nuw := true} (.value v199) (.value v193) = (.value (v199 + v193)) ∧
  Operation.add {nsw := true, nuw := true} (.value v200) (.value v194) = (.value (v200 + v194)) ∧
  Operation.add {nsw := true, nuw := true} (.value v201) (.value v195) = (.value (v201 + v195)) ∧
  Operation.add {nsw := true, nuw := true} (.value v202) (.value v196) = (.value (v202 + v196)) ∧
  Operation.add {nsw := true, nuw := true} (.value v204) (.value 19#64) = (.value (v204 + 19#64)) ∧
  Operation.add {nsw := true, nuw := true} (.value v205) (.value v210) = (.value (v205 + v210)) ∧
  Operation.add {nsw := true, nuw := true} (.value v206) (.value v212) = (.value (v206 + v212)) ∧
  Operation.add {nsw := true, nuw := true} (.value v207) (.value v214) = (.value (v207 + v214)) ∧
  Operation.add {nsw := true, nuw := true} (.value v208) (.value v216) = (.value (v208 + v216)) ∧
  Operation.add {nsw := true, nuw := true} (.value v218) (.value v204) = (.value (v218 + v204))

def affineXWords (s : GlobalState) (temp : Pointer) : Field.Serial :=
  fun i => s.mem.readAt (temp.add (BitVec.ofNat 64 (8 * i.val))) 64

def affineYWords (s : GlobalState) (temp : Pointer) : Field.Serial :=
  fun i => s.mem.readAt (temp.add (BitVec.ofNat 64 (40 + 8 * i.val))) 64

private theorem trunc_unflagged (v : BitVec 64) :
    Operation.trunc {} (.value v) = .value (v.setWidth 8) := by
  simp [Operation.trunc]

set_option maxHeartbeats 16000000 in
/-- Exact load and arithmetic execution. All loads are justified by the one
80-byte affine scratch object; memory is unchanged throughout this segment. -/
theorem normalize_run (p : Primitives) (E : Env program.Γ) (initial s : GlobalState)
    (input : Pointer) (htemp : SmallRange s.mem (scratch initial 5) 80)
    (hsafe : NormalizationSafety (affineXWords s (scratch initial 5))
      (affineYWords s (scratch initial 5))) :
    runSlice p 81 159 (affineEnv E initial input) s =
      .value (normalizedEnv (affineEnv E initial input) (scratch initial 5)
        (affineXWords s (scratch initial 5)) (affineYWords s (scratch initial 5)), s) := by
  have hf0 := htemp.fits_add (k := 0) (count := 8) (by decide)
  have hf8 := htemp.fits_add (k := 8) (count := 8) (by decide)
  have hf16 := htemp.fits_add (k := 16) (count := 8) (by decide)
  have hf24 := htemp.fits_add (k := 24) (count := 8) (by decide)
  have hf32 := htemp.fits_add (k := 32) (count := 8) (by decide)
  have hf40 := htemp.fits_add (k := 40) (count := 8) (by decide)
  have hf48 := htemp.fits_add (k := 48) (count := 8) (by decide)
  have hf56 := htemp.fits_add (k := 56) (count := 8) (by decide)
  have hf64 := htemp.fits_add (k := 64) (count := 8) (by decide)
  have hf72 := htemp.fits_add (k := 72) (count := 8) (by decide)
  have hg8 := htemp.gep (k := 8) (by decide)
  have hg16 := htemp.gep (k := 16) (by decide)
  have hg24 := htemp.gep (k := 24) (by decide)
  have hg32 := htemp.gep (k := 32) (by decide)
  have hg48 := htemp.gep (k := 48) (by decide)
  have hg56 := htemp.gep (k := 56) (by decide)
  have hg64 := htemp.gep (k := 64) (by decide)
  have hg72 := htemp.gep (k := 72) (by decide)
  simp only [Pointer.add_zero] at hf0
  norm_num only [Nat.cast_ofNat] at hg8 hg16 hg24 hg32 hg48 hg56 hg64 hg72
  have hreads := affineEnv_normalizationInputs E initial input
  generalize he : affineEnv E initial input = Ea at hreads ⊢
  clear he
  generalize hx : affineXWords s (scratch initial 5) = x at hsafe ⊢
  generalize hy : affineYWords s (scratch initial 5) = y at hsafe ⊢
  have hx0 := congrFun hx (0 : Fin 5)
  have hx1 := congrFun hx (1 : Fin 5)
  have hx2 := congrFun hx (2 : Fin 5)
  have hx3 := congrFun hx (3 : Fin 5)
  have hx4 := congrFun hx (4 : Fin 5)
  have hy0 := congrFun hy (0 : Fin 5)
  have hy1 := congrFun hy (1 : Fin 5)
  have hy2 := congrFun hy (2 : Fin 5)
  have hy3 := congrFun hy (3 : Fin 5)
  have hy4 := congrFun hy (4 : Fin 5)
  simp [affineXWords, affineYWords] at hx0 hx1 hx2 hx3 hx4 hy0 hy1 hy2 hy3 hy4
  clear hx hy
  dsimp only [NormalizationSafety] at hsafe
  rcases hsafe with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36, h37⟩
  simp (config := { maxSteps := 1000000 }) [runSlice, program.entry, normalizedEnv, List.drop, List.take, List.foldlM_cons, List.foldlM_nil,
    Nat.reduceMul, Nat.reduceAdd, Nat.reducePow, Nat.reduceMod, BitVec.ofNat_eq_ofNat,
    Instr.run, Operation.load, UnOp.compute, BinOp.compute, Ty.wrap, Ty.unflatten,
    EffectM.bind_eq, EffectM.pure_eq, mlir_effect, mlir_env,
    Operation.and, Operation.lshr, trunc_unflagged,
    PoisonOr.value_bind, PoisonOr.poison_bind, PoisonOr.bind_poison, PoisonOr.pure_def,
    -BitVec.shiftLeft_add_distrib,
    GepIndex.inboundsOffset, Operation.gepInboundsIndex, Operation.GepSignedRange,
    throwUBIf, hx0, hx1, hx2, hx3, hx4, hy0, hy1, hy2, hy3, hy4,
    hreads.read2, hreads.read4, hreads.read5, hreads.read6, hreads.read7, hreads.read8, hreads.read9, hreads.read10, hreads.read11, hreads.read12, hreads.read13, hreads.read14, hreads.read15, hreads.read16, hreads.read17, hreads.read18, hreads.read19, hreads.read20, hreads.read21, hreads.read22, hreads.read23, hreads.read24, hreads.read25, hreads.read26, hreads.read27, hreads.read28, hreads.read29, hreads.read30, hreads.read31, hreads.read32, hreads.read33, hreads.read34, hreads.read35, hreads.read36, hreads.read37, hreads.read38, hreads.read39, hreads.read40, hreads.read41, hreads.read42, hreads.read43, hreads.read58, hreads.read62,
    hf0, hf8, hf16, hf24, hf32, hf40, hf48, hf56, hf64, hf72,
    hg8, hg16, hg24, hg32, hg48, hg56, hg64, hg72,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36, h37]

/-- y's exact inline byte schedule is the already checked standalone
field serializer schedule; only commutativity changes operand spelling. -/
theorem inlineYBytes_eq_machine (y : Field.Serial) :
    inlineYBytes y = Decompress.Execution.ToBytes.machine y := by
  funext i
  simp only [inlineYBytes, Decompress.Execution.ToBytes.machine,
    Decompress.Execution.ToBytes.rawBytes, Decompress.Execution.ToBytes.carryMachine,
    Decompress.Execution.ToBytes.reverseCarry, Decompress.Execution.ToBytes.quotientCarry,
    weakWord, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val, Matrix.head_cons, Matrix.tail_cons,
    Matrix.cons_val_zero', Matrix.cons_val_succ', BitVec.ofNat_eq_ofNat, Nat.cast_ofNat, BitVec.add_comm,
    BitVec.mul_comm]

theorem parity_add_mul19 (q w : BitVec 64) :
    (q + w).setWidth 8 &&& 1#8 = (19#64 * q + w).setWidth 8 &&& 1#8 := by
  apply BitVec.eq_of_toNat_eq
  have hand (n : Nat) : n &&& 1 = n % 2 := by
    simpa using Nat.and_two_pow_sub_one_eq_mod n 1
  simp only [BitVec.toNat_and, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
    BitVec.toNat_add, BitVec.toNat_mul, hand]
  omega

/-- `%219` adds q rather than 19q, which preserves exactly the low parity bit. -/
theorem inlineParity_eq_machine (x : Field.Serial) :
    inlineParity x = Decompress.Execution.ToBytes.machine x 0 &&& 1#8 := by
  simp only [inlineParity, Decompress.Execution.ToBytes.machine,
    Decompress.Execution.ToBytes.rawBytes, Decompress.Execution.ToBytes.carryMachine,
    Decompress.Execution.ToBytes.reverseCarry, Decompress.Execution.ToBytes.quotientCarry,
    weakWord, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val, Matrix.head_cons, Matrix.tail_cons,
    Matrix.cons_val_zero', Matrix.cons_val_succ', BitVec.ofNat_eq_ofNat, Nat.cast_ofNat]
  simp only [BitVec.add_comm, BitVec.mul_comm] at ⊢
  simpa only [quotientWord, carriedWord, weakWord, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val,
    Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val_zero', Matrix.cons_val_succ',
    BitVec.ofNat_eq_ofNat, Nat.cast_ofNat, BitVec.add_comm, BitVec.mul_comm]
    using parity_add_mul19 (quotientWord x) (weakWord x 0)

/-- The checked serializer's packed value is the canonical 256-bit field word. -/
theorem packed_tight_eq_toBytes (a : Field.Serial) :
    packedBytes (tightWords a) = toBytes (fun i => (a i).toNat) := by
  apply BitVec.eq_of_toNat_eq
  rw [tightWords_canonical, toBytes_toNat _ (fun i => (a i).isLt), value_eq_decode51]
  rfl

theorem inlineYBytes_canonical (y : Field.Serial) (i : Fin 32) :
    inlineYBytes y i = (toBytes (fun j => (y j).toNat)).extractLsb' (8 * i.val) 8 := by
  rw [inlineYBytes_eq_machine, Decompress.Execution.ToBytes.machine_canonical,
    packed_tight_eq_toBytes]

theorem inlineParity_canonical (x : Field.Serial) :
    inlineParity x = (toBytes (fun j => (x j).toNat)).extractLsb' 0 8 &&& 1#8 := by
  rw [inlineParity_eq_machine, Decompress.Execution.ToBytes.machine_canonical,
    packed_tight_eq_toBytes]
  rfl

def inlineCompressedBytes (x y : Field.Serial) (i : Fin 32) : BitVec 8 :=
  if i.val = 31 then (inlineParity x <<< 7) ||| inlineYBytes y 31 else inlineYBytes y i

theorem inlineCompressedBytes_eq (x y : Field.Serial) :
    inlineCompressedBytes x y = encodedBytes x y := by
  funext i
  simp only [inlineCompressedBytes, inlineParity_canonical, inlineYBytes_canonical,
    encodedBytes, insertSign]
  rfl

end Agave.Ed25519.Encoding.Compress.Execution
