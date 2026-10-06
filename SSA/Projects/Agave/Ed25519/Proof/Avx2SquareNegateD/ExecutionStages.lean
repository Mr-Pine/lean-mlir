import SSA.Projects.Agave.Ed25519.Proof.Avx2SquareNegateD.ExecutionMachine

namespace Agave.Ed25519.Avx2SquareNegateD.Execution

abbrev WordColumns := Fin 10 → V64

set_option maxHeartbeats 800000 in
/-- The ten convolution columns before the common carry schedule, sliced from
`wordTrace` by retaining exactly their register dependencies. -/
def columnTrace (a : Blocks) : WordColumns :=
  let v0 : BitVec 32 := 0
  let v1 : BitVec 32 := 0
  let v2 : Vector (BitVec 32) 8 := Vector.replicate 8 0
  let v4 : Vector (BitVec 32) 8 := v2.set 0 v1 (by decide)
  let v6 : Vector (BitVec 32) 8 := v4.set 1 v1 (by decide)
  let v8 : Vector (BitVec 32) 8 := v6.set 2 v0 (by decide)
  let v10 : Vector (BitVec 32) 8 := v8.set 3 v0 (by decide)
  let v12 : Vector (BitVec 32) 8 := v10.set 4 v1 (by decide)
  let v14 : Vector (BitVec 32) 8 := v12.set 5 v1 (by decide)
  let v16 : Vector (BitVec 32) 8 := v14.set 6 v0 (by decide)
  let v18 : Vector (BitVec 32) 8 := v16.set 7 v0 (by decide)
  let v19 : Vector (BitVec 32) 8 := Vector.replicate 8 0
  let v21 : Vector (BitVec 32) 8 := v19.set 0 v0 (by decide)
  let v23 : Vector (BitVec 32) 8 := v21.set 1 v0 (by decide)
  let v25 : Vector (BitVec 32) 8 := v23.set 2 v1 (by decide)
  let v27 : Vector (BitVec 32) 8 := v25.set 3 v1 (by decide)
  let v29 : Vector (BitVec 32) 8 := v27.set 4 v0 (by decide)
  let v31 : Vector (BitVec 32) 8 := v29.set 5 v0 (by decide)
  let v33 : Vector (BitVec 32) 8 := v31.set 6 v1 (by decide)
  let v35 : Vector (BitVec 32) 8 := v33.set 7 v1 (by decide)
  let v40 : Vector (BitVec 32) 8 := Vector.replicate 8 1
  let v41 : Vector (BitVec 64) 4 := Vector.replicate 4 19
  let v42 : Vector (BitVec 64) 4 := Vector.replicate 4 4294967295
  let v43 : Vector (BitVec 64) 4 := Vector.replicate 4 1
  let v44 : BitVec 64 := 9223369425514659840
  let v45 : BitVec 64 := 0
  let v46 : Vector (BitVec 64) 4 := Vector.replicate 4 0
  let v48 : Vector (BitVec 64) 4 := v46.set 0 v45 (by decide)
  let v50 : Vector (BitVec 64) 4 := v48.set 1 v45 (by decide)
  let v52 : Vector (BitVec 64) 4 := v50.set 2 v45 (by decide)
  let v54 : Vector (BitVec 64) 4 := v52.set 3 v44 (by decide)
  let v55 : BitVec 64 := 4611685880988434432
  let v56 : Vector (BitVec 64) 4 := Vector.replicate 4 0
  let v58 : Vector (BitVec 64) 4 := v56.set 0 v45 (by decide)
  let v60 : Vector (BitVec 64) 4 := v58.set 1 v45 (by decide)
  let v62 : Vector (BitVec 64) 4 := v60.set 2 v45 (by decide)
  let v64 : Vector (BitVec 64) 4 := v62.set 3 v55 (by decide)
  let v65 : BitVec 64 := 9223371899415822336
  let v66 : Vector (BitVec 64) 4 := Vector.replicate 4 0
  let v68 : Vector (BitVec 64) 4 := v66.set 0 v45 (by decide)
  let v70 : Vector (BitVec 64) 4 := v68.set 1 v45 (by decide)
  let v72 : Vector (BitVec 64) 4 := v70.set 2 v45 (by decide)
  let v74 : Vector (BitVec 64) 4 := v72.set 3 v65 (by decide)
  let v116 : Vector (BitVec 32) 8 := a 0
  let v117 : Vector (BitVec 32) 8 := #v[v116[0]'(by decide), v18[0]'(by decide), v116[1]'(by decide), v18[1]'(by decide), v116[4]'(by decide), v18[4]'(by decide), v116[5]'(by decide), v18[5]'(by decide)]
  let v118 : Vector (BitVec 32) 8 := #v[v116[2]'(by decide), v35[2]'(by decide), v116[3]'(by decide), v35[3]'(by decide), v116[6]'(by decide), v35[6]'(by decide), v116[7]'(by decide), v35[7]'(by decide)]
  let v119 : Vector (BitVec 64) 4 := join64 v117
  let v120 : Vector (BitVec 64) 4 := join64 v118
  let v122 : Vector (BitVec 32) 8 := a 1
  let v123 : Vector (BitVec 32) 8 := #v[v122[0]'(by decide), v18[0]'(by decide), v122[1]'(by decide), v18[1]'(by decide), v122[4]'(by decide), v18[4]'(by decide), v122[5]'(by decide), v18[5]'(by decide)]
  let v124 : Vector (BitVec 32) 8 := #v[v122[2]'(by decide), v35[2]'(by decide), v122[3]'(by decide), v35[3]'(by decide), v122[6]'(by decide), v35[6]'(by decide), v122[7]'(by decide), v35[7]'(by decide)]
  let v125 : Vector (BitVec 64) 4 := join64 v123
  let v126 : Vector (BitVec 64) 4 := join64 v124
  let v128 : Vector (BitVec 32) 8 := a 2
  let v129 : Vector (BitVec 32) 8 := #v[v128[0]'(by decide), v18[0]'(by decide), v128[1]'(by decide), v18[1]'(by decide), v128[4]'(by decide), v18[4]'(by decide), v128[5]'(by decide), v18[5]'(by decide)]
  let v130 : Vector (BitVec 32) 8 := #v[v128[2]'(by decide), v35[2]'(by decide), v128[3]'(by decide), v35[3]'(by decide), v128[6]'(by decide), v35[6]'(by decide), v128[7]'(by decide), v35[7]'(by decide)]
  let v131 : Vector (BitVec 64) 4 := join64 v129
  let v132 : Vector (BitVec 64) 4 := join64 v130
  let v134 : Vector (BitVec 32) 8 := a 3
  let v135 : Vector (BitVec 32) 8 := #v[v134[0]'(by decide), v18[0]'(by decide), v134[1]'(by decide), v18[1]'(by decide), v134[4]'(by decide), v18[4]'(by decide), v134[5]'(by decide), v18[5]'(by decide)]
  let v136 : Vector (BitVec 32) 8 := #v[v134[2]'(by decide), v35[2]'(by decide), v134[3]'(by decide), v35[3]'(by decide), v134[6]'(by decide), v35[6]'(by decide), v134[7]'(by decide), v35[7]'(by decide)]
  let v137 : Vector (BitVec 64) 4 := join64 v135
  let v138 : Vector (BitVec 64) 4 := join64 v136
  let v140 : Vector (BitVec 32) 8 := a 4
  let v141 : Vector (BitVec 32) 8 := #v[v140[0]'(by decide), v18[0]'(by decide), v140[1]'(by decide), v18[1]'(by decide), v140[4]'(by decide), v18[4]'(by decide), v140[5]'(by decide), v18[5]'(by decide)]
  let v142 : Vector (BitVec 32) 8 := #v[v140[2]'(by decide), v35[2]'(by decide), v140[3]'(by decide), v35[3]'(by decide), v140[6]'(by decide), v35[6]'(by decide), v140[7]'(by decide), v35[7]'(by decide)]
  let v143 : Vector (BitVec 64) 4 := join64 v141
  let v144 : Vector (BitVec 64) 4 := join64 v142
  let v145 : Vector (BitVec 32) 8 := Vector.zipWith (fun (x y : BitVec 32) => x <<< y.toNat) v117 v40
  let v146 : Vector (BitVec 64) 4 := join64 v145
  let v147 : Vector (BitVec 32) 8 := Vector.zipWith (fun (x y : BitVec 32) => x <<< y.toNat) v118 v40
  let v148 : Vector (BitVec 64) 4 := join64 v147
  let v149 : Vector (BitVec 32) 8 := Vector.zipWith (fun (x y : BitVec 32) => x <<< y.toNat) v123 v40
  let v150 : Vector (BitVec 64) 4 := join64 v149
  let v151 : Vector (BitVec 32) 8 := Vector.zipWith (fun (x y : BitVec 32) => x <<< y.toNat) v124 v40
  let v152 : Vector (BitVec 64) 4 := join64 v151
  let v153 : Vector (BitVec 32) 8 := Vector.zipWith (fun (x y : BitVec 32) => x <<< y.toNat) v129 v40
  let v154 : Vector (BitVec 64) 4 := join64 v153
  let v155 : Vector (BitVec 32) 8 := Vector.zipWith (fun (x y : BitVec 32) => x <<< y.toNat) v130 v40
  let v156 : Vector (BitVec 64) 4 := join64 v155
  let v157 : Vector (BitVec 32) 8 := Vector.zipWith (fun (x y : BitVec 32) => x <<< y.toNat) v135 v40
  let v158 : Vector (BitVec 64) 4 := join64 v157
  let v159 : Vector (BitVec 32) 8 := Vector.zipWith (fun (x y : BitVec 32) => x <<< y.toNat) v136 v40
  let v160 : Vector (BitVec 64) 4 := join64 v159
  let v161 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v132 v41
  let v162 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v137 v41
  let v163 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v138 v41
  let v164 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v143 v41
  let v165 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v144 v41
  let v166 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v119 v119
  let v167 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x &&& y) v164 v42
  let v168 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v167 v150
  let v169 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x &&& y) v162 v42
  let v170 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v169 v154
  let v171 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x &&& y) v165 v42
  let v172 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v171 v148
  let v173 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x &&& y) v163 v42
  let v174 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v173 v152
  let v175 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x &&& y) v161 v42
  let v176 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v175 v132
  let v177 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v174 v176
  let v178 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v177 v172
  let v179 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x <<< y.toNat) v178 v43
  let v180 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v170 v166
  let v181 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v180 v168
  let v182 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v181 v179
  let v183 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v146 v120
  let v184 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v167 v152
  let v185 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v169 v156
  let v186 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v171 v125
  let v187 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v173 v131
  let v188 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v186 v187
  let v189 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x <<< y.toNat) v188 v43
  let v190 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v185 v183
  let v191 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v190 v184
  let v192 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v191 v189
  let v193 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v125 v146
  let v194 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v148 v120
  let v195 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v194 v193
  let v196 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v167 v154
  let v197 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v169 v137
  let v198 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v171 v152
  let v199 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v173 v156
  let v200 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v198 v199
  let v201 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x <<< y.toNat) v200 v43
  let v202 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v195 v197
  let v203 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v202 v196
  let v204 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v203 v201
  let v205 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v126 v146
  let v206 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v125 v148
  let v207 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v206 v205
  let v208 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v167 v156
  let v209 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v207 v208
  let v210 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v171 v131
  let v211 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v173 v137
  let v212 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v210 v211
  let v213 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x <<< y.toNat) v212 v43
  let v214 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v209 v213
  let v215 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v131 v146
  let v216 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v152 v148
  let v217 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v125 v125
  let v218 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v167 v158
  let v219 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v171 v156
  let v220 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v173 v138
  let v221 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v219 v220
  let v222 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x <<< y.toNat) v221 v43
  let v223 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v215 v217
  let v224 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v223 v216
  let v225 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v224 v218
  let v226 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v225 v222
  let v227 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v132 v146
  let v228 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v131 v148
  let v229 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v228 v227
  let v230 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v150 v126
  let v231 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v229 v230
  let v232 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v167 v160
  let v233 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v231 v232
  let v234 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v171 v137
  let v235 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x <<< y.toNat) v234 v43
  let v236 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v233 v235
  let v237 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v137 v146
  let v238 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v156 v148
  let v239 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v131 v150
  let v240 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v152 v126
  let v241 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v167 v143
  let v242 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v171 v160
  let v243 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x <<< y.toNat) v242 v43
  let v244 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v240 v239
  let v245 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v244 v237
  let v246 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v245 v238
  let v247 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v246 v241
  let v248 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v247 v243
  let v249 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v138 v146
  let v250 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v137 v148
  let v251 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v132 v150
  let v252 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v131 v152
  let v253 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v171 v143
  let v254 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x <<< y.toNat) v253 v43
  let v255 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v252 v251
  let v256 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v255 v249
  let v257 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v256 v250
  let v258 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v257 v254
  let v259 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v143 v146
  let v260 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v160 v148
  let v261 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v137 v150
  let v262 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v156 v152
  let v263 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v131 v131
  let v264 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v171 v144
  let v265 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x <<< y.toNat) v264 v43
  let v266 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v261 v263
  let v267 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v266 v262
  let v268 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v267 v259
  let v269 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v268 v260
  let v270 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v269 v265
  let v271 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v144 v146
  let v272 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v143 v148
  let v273 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v138 v150
  let v274 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v137 v152
  let v275 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v154 v132
  let v276 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v274 v273
  let v277 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v276 v275
  let v278 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v277 v271
  let v279 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v278 v272
  let v280 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x - y) v54 v182
  let v281 : Vector (BitVec 64) 4 := #v[v182[0]'(by decide), v182[1]'(by decide), v182[2]'(by decide), v280[3]'(by decide)]
  let v282 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x - y) v64 v192
  let v283 : Vector (BitVec 64) 4 := #v[v192[0]'(by decide), v192[1]'(by decide), v192[2]'(by decide), v282[3]'(by decide)]
  let v284 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x - y) v74 v204
  let v285 : Vector (BitVec 64) 4 := #v[v204[0]'(by decide), v204[1]'(by decide), v204[2]'(by decide), v284[3]'(by decide)]
  let v286 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x - y) v64 v214
  let v287 : Vector (BitVec 64) 4 := #v[v214[0]'(by decide), v214[1]'(by decide), v214[2]'(by decide), v286[3]'(by decide)]
  let v288 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x - y) v74 v226
  let v289 : Vector (BitVec 64) 4 := #v[v226[0]'(by decide), v226[1]'(by decide), v226[2]'(by decide), v288[3]'(by decide)]
  let v290 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x - y) v64 v236
  let v291 : Vector (BitVec 64) 4 := #v[v236[0]'(by decide), v236[1]'(by decide), v236[2]'(by decide), v290[3]'(by decide)]
  let v292 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x - y) v74 v248
  let v293 : Vector (BitVec 64) 4 := #v[v248[0]'(by decide), v248[1]'(by decide), v248[2]'(by decide), v292[3]'(by decide)]
  let v294 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x - y) v64 v258
  let v295 : Vector (BitVec 64) 4 := #v[v258[0]'(by decide), v258[1]'(by decide), v258[2]'(by decide), v294[3]'(by decide)]
  let v296 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x - y) v74 v270
  let v297 : Vector (BitVec 64) 4 := #v[v270[0]'(by decide), v270[1]'(by decide), v270[2]'(by decide), v296[3]'(by decide)]
  let v298 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x - y) v64 v279
  let v299 : Vector (BitVec 64) 4 := #v[v279[0]'(by decide), v279[1]'(by decide), v279[2]'(by decide), v298[3]'(by decide)]
  ![v281, v283, v285, v287, v289, v291, v293, v295, v297, v299]

/-- The carry, mask, narrowing and output shuffle instructions, with the ten
input columns held abstract. -/
def reductionTrace (z : WordColumns) : Blocks :=
  let v0 : BitVec 32 := 0
  let v41 : Vector (BitVec 64) 4 := Vector.replicate 4 19
  let v75 : Vector (BitVec 64) 4 := Vector.replicate 4 26
  let v76 : Vector (BitVec 64) 4 := Vector.replicate 4 67108863
  let v77 : Vector (BitVec 64) 4 := Vector.replicate 4 25
  let v78 : Vector (BitVec 64) 4 := Vector.replicate 4 33554431
  let v79 : Vector (BitVec 64) 4 := Vector.replicate 4 51
  let v80 : BitVec 32 := 67108863
  let v81 : Vector (BitVec 32) 8 := Vector.replicate 8 0
  let v83 : Vector (BitVec 32) 8 := v81.set 0 v80 (by decide)
  let v85 : Vector (BitVec 32) 8 := v83.set 1 v0 (by decide)
  let v87 : Vector (BitVec 32) 8 := v85.set 2 v80 (by decide)
  let v89 : Vector (BitVec 32) 8 := v87.set 3 v0 (by decide)
  let v91 : Vector (BitVec 32) 8 := v89.set 4 v80 (by decide)
  let v93 : Vector (BitVec 32) 8 := v91.set 5 v0 (by decide)
  let v95 : Vector (BitVec 32) 8 := v93.set 6 v80 (by decide)
  let v97 : Vector (BitVec 32) 8 := v95.set 7 v0 (by decide)
  let v98 : BitVec 32 := 33554431
  let v99 : Vector (BitVec 32) 8 := Vector.replicate 8 0
  let v101 : Vector (BitVec 32) 8 := v99.set 0 v98 (by decide)
  let v103 : Vector (BitVec 32) 8 := v101.set 1 v0 (by decide)
  let v105 : Vector (BitVec 32) 8 := v103.set 2 v98 (by decide)
  let v107 : Vector (BitVec 32) 8 := v105.set 3 v0 (by decide)
  let v109 : Vector (BitVec 32) 8 := v107.set 4 v98 (by decide)
  let v111 : Vector (BitVec 32) 8 := v109.set 5 v0 (by decide)
  let v113 : Vector (BitVec 32) 8 := v111.set 6 v98 (by decide)
  let v115 : Vector (BitVec 32) 8 := v113.set 7 v0 (by decide)
  let v281 : Vector (BitVec 64) 4 := z 0
  let v283 : Vector (BitVec 64) 4 := z 1
  let v285 : Vector (BitVec 64) 4 := z 2
  let v287 : Vector (BitVec 64) 4 := z 3
  let v289 : Vector (BitVec 64) 4 := z 4
  let v291 : Vector (BitVec 64) 4 := z 5
  let v293 : Vector (BitVec 64) 4 := z 6
  let v295 : Vector (BitVec 64) 4 := z 7
  let v297 : Vector (BitVec 64) 4 := z 8
  let v299 : Vector (BitVec 64) 4 := z 9
  let v300 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x >>> y.toNat) v281 v75
  let v301 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v300 v283
  let v302 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x &&& y) v281 v76
  let v303 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x >>> y.toNat) v289 v75
  let v304 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v303 v291
  let v305 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x &&& y) v289 v76
  let v306 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x >>> y.toNat) v301 v77
  let v307 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v306 v285
  let v308 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x &&& y) v301 v78
  let v309 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x >>> y.toNat) v304 v77
  let v310 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v309 v293
  let v311 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x &&& y) v304 v78
  let v312 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x >>> y.toNat) v307 v75
  let v313 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v312 v287
  let v314 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x >>> y.toNat) v310 v75
  let v315 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v314 v295
  let v316 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x >>> y.toNat) v313 v77
  let v317 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v316 v305
  let v318 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x >>> y.toNat) v315 v77
  let v319 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v318 v297
  let v320 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x >>> y.toNat) v317 v75
  let v321 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v320 v311
  let v322 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x >>> y.toNat) v319 v75
  let v323 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v322 v299
  let v324 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x >>> y.toNat) v323 v77
  let v325 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x &&& y) v324 v76
  let v326 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x >>> y.toNat) v323 v79
  let v327 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v325 v41
  let v328 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x * y) v326 v41
  let v329 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v327 v302
  let v330 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v328 v308
  let v331 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x >>> y.toNat) v329 v75
  let v332 : Vector (BitVec 64) 4 := Vector.zipWith (fun (x y : BitVec 64) => x + y) v330 v331
  let v333 : Vector (BitVec 32) 8 := split32 v329
  let v334 : Vector (BitVec 32) 8 := Vector.zipWith (fun (x y : BitVec 32) => x &&& y) v333 v97
  let v335 : Vector (BitVec 32) 8 := split32 v332
  let v336 : Vector (BitVec 32) 8 := #v[v334[0]'(by decide), v334[2]'(by decide), v335[0]'(by decide), v335[2]'(by decide), v334[4]'(by decide), v334[6]'(by decide), v335[4]'(by decide), v335[6]'(by decide)]
  let v337 : Vector (BitVec 32) 8 := split32 v307
  let v338 : Vector (BitVec 32) 8 := Vector.zipWith (fun (x y : BitVec 32) => x &&& y) v337 v97
  let v339 : Vector (BitVec 32) 8 := split32 v313
  let v340 : Vector (BitVec 32) 8 := Vector.zipWith (fun (x y : BitVec 32) => x &&& y) v339 v115
  let v341 : Vector (BitVec 32) 8 := #v[v338[0]'(by decide), v338[2]'(by decide), v340[0]'(by decide), v340[2]'(by decide), v338[4]'(by decide), v338[6]'(by decide), v340[4]'(by decide), v340[6]'(by decide)]
  let v342 : Vector (BitVec 32) 8 := split32 v321
  let v343 : Vector (BitVec 32) 8 := split32 v317
  let v344 : Vector (BitVec 32) 8 := Vector.zipWith (fun (x y : BitVec 32) => x &&& y) v343 v97
  let v345 : Vector (BitVec 32) 8 := #v[v344[0]'(by decide), v344[2]'(by decide), v342[0]'(by decide), v342[2]'(by decide), v344[4]'(by decide), v344[6]'(by decide), v342[4]'(by decide), v342[6]'(by decide)]
  let v346 : Vector (BitVec 32) 8 := split32 v310
  let v347 : Vector (BitVec 32) 8 := Vector.zipWith (fun (x y : BitVec 32) => x &&& y) v346 v97
  let v348 : Vector (BitVec 32) 8 := split32 v315
  let v349 : Vector (BitVec 32) 8 := Vector.zipWith (fun (x y : BitVec 32) => x &&& y) v348 v115
  let v350 : Vector (BitVec 32) 8 := #v[v347[0]'(by decide), v347[2]'(by decide), v349[0]'(by decide), v349[2]'(by decide), v347[4]'(by decide), v347[6]'(by decide), v349[4]'(by decide), v349[6]'(by decide)]
  let v351 : Vector (BitVec 32) 8 := split32 v319
  let v352 : Vector (BitVec 32) 8 := Vector.zipWith (fun (x y : BitVec 32) => x &&& y) v351 v97
  let v353 : Vector (BitVec 32) 8 := split32 v323
  let v354 : Vector (BitVec 32) 8 := Vector.zipWith (fun (x y : BitVec 32) => x &&& y) v353 v115
  let v355 : Vector (BitVec 32) 8 := #v[v352[0]'(by decide), v352[2]'(by decide), v354[0]'(by decide), v354[2]'(by decide), v352[4]'(by decide), v352[6]'(by decide), v354[4]'(by decide), v354[6]'(by decide)]
  ![v336, v341, v345, v350, v355]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- Slicing the straight-line register graph changes only let sharing. -/
theorem wordTrace_eq_stages (a : Blocks) :
    wordTrace a = reductionTrace (columnTrace a) := by
  rfl

end Agave.Ed25519.Avx2SquareNegateD.Execution
