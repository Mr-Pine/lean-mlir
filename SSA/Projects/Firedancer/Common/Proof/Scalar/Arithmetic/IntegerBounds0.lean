import SSA.Projects.Firedancer.Common.Proof.Scalar.Arithmetic.IntegerRegisters

/-! Checked linear identities and interval certificates for the corresponding
numbered source arithmetic registers. Generated equations are verified by
`ring` and `omega`; no external arithmetic result is trusted. -/

namespace Firedancer.Common.ScalarArithmetic.IntegerRegisters

set_option maxHeartbeats 2000000

attribute [local irreducible] z61 z63 z65 z67 z69 z71 z73 z75 z77 z79 z81 z83 z85 z87 z89 z91 z93 z95 z97 z99 z101 z103 z105 z106 z107 z108 z109 z110 z111 z112 z113 z114 z115 z116 z117 z118 z119 z120 z121 z122 z123 z124 z125 z126 z127 z128 z129 z130 z131 z132 z133 z134 z135 z136 z137 z138 z139 z140 z141 z142 z143 z144 z145 z146 z147 z148 z149 z150 z151 z152 z153 z154 z155 z156 z157 z158 z159 z160 z161 z162 z163 z164 z165 z166 z167 z168 z169 z170 z171 z172 z173 z174 z175 z176 z177 z178 z179 z180 z181 z182 z183 z184 z185 z186 z187 z188 z189 z190 z191 z192 z193 z194 z195 z196 z197 z198 z199 z200 z201 z202 z203 z204 z205 z206 z207 z208 z209 z210 z211 z212 z213 z214 z215 z216 z217 z218 z219 z220 z221 z222 z223 z224 z225 z226 z227 z228 z229 z230 z231 z232 z233 z234 z235 z236 z237 z238 z239 z240 z241 z242 z243 z244 z245 z246 z247 z248 z249 z250 z251 z252 z253 z254 z255 z256 z257 z258 z259 z260 z261 z262 z263 z264 z265 z266 z267 z268 z269 z270 z271 z272 z273 z274 z275 z276 z277 z278 z279 z280 z281 z282 z283 z284 z285 z286 z287 z288 z289 z290 z291 z292 z293 z294 z295 z296 z297 z298 z299 z300 z301 z302 z303 z304 z305 z306 z307 z308 z309 z310 z311 z312 z313 z314 z315 z316 z317 z318 z319 z320 z321 z322 z323 z324 z325 z326 z327 z328 z329 z330 z331 z332 z333 z334 z335 z336 z337 z338 z339 z340 z341 z342 z343 z344 z345 z346 z347 z348 z349 z350 z351 z352 z353 z354 z355 z356 z357 z358 z359 z360 z361 z362 z363 z364 z365 z366 z367 z368 z369 z370 z371 z372 z373 z374 z375 z376 z377 z378 z379 z380 z381 z382 z383 z384 z385 z386 z387 z388 z389 z390 z391 z392 z393 z394 z395 z396 z397 z398 z399 z400 z401 z402 z403 z404 z405 z406 z407 z408 z409 z410 z411 z412 z413 z414 z415 z416 z417 z418 z419 z420 z421 z422 z423 z424 z425 z426 z427 z428 z429 z430 z431 z432 z433 z434 z435 z436 z437 z438 z439 z440 z441 z442 z443 z444 z445 z446 m170 m179 m189 m196 m201 m206 m210 m213 m217 m222 m227 m301 m306 m311 m321 m329 m334 m338 m341 m345 m349 m354 m358

theorem z61_linear (d : Digits) : z61 d = (d 0) := by
  simp only [z61] <;> ring

theorem z61_bounds (d : Digits) (hd : Bounded d) :
    (0 : Int) ≤ z61 d ∧ z61 d ≤ 2097151 := by
  have h := hd 0
  norm_num at h
  rw [z61]
  omega

theorem z63_linear (d : Digits) : z63 d = (d 1) := by
  simp only [z63] <;> ring

theorem z63_bounds (d : Digits) (hd : Bounded d) :
    (0 : Int) ≤ z63 d ∧ z63 d ≤ 2097151 := by
  have h := hd 1
  norm_num at h
  rw [z63]
  omega

theorem z65_linear (d : Digits) : z65 d = (d 2) := by
  simp only [z65] <;> ring

theorem z65_bounds (d : Digits) (hd : Bounded d) :
    (0 : Int) ≤ z65 d ∧ z65 d ≤ 2097151 := by
  have h := hd 2
  norm_num at h
  rw [z65]
  omega

theorem z67_linear (d : Digits) : z67 d = (d 3) := by
  simp only [z67] <;> ring

theorem z67_bounds (d : Digits) (hd : Bounded d) :
    (0 : Int) ≤ z67 d ∧ z67 d ≤ 2097151 := by
  have h := hd 3
  norm_num at h
  rw [z67]
  omega

theorem z69_linear (d : Digits) : z69 d = (d 4) := by
  simp only [z69] <;> ring

theorem z69_bounds (d : Digits) (hd : Bounded d) :
    (0 : Int) ≤ z69 d ∧ z69 d ≤ 2097151 := by
  have h := hd 4
  norm_num at h
  rw [z69]
  omega

theorem z71_linear (d : Digits) : z71 d = (d 5) := by
  simp only [z71] <;> ring

theorem z71_bounds (d : Digits) (hd : Bounded d) :
    (0 : Int) ≤ z71 d ∧ z71 d ≤ 2097151 := by
  have h := hd 5
  norm_num at h
  rw [z71]
  omega

theorem z73_linear (d : Digits) : z73 d = (d 6) := by
  simp only [z73] <;> ring

theorem z73_bounds (d : Digits) (hd : Bounded d) :
    (0 : Int) ≤ z73 d ∧ z73 d ≤ 2097151 := by
  have h := hd 6
  norm_num at h
  rw [z73]
  omega

theorem z75_linear (d : Digits) : z75 d = (d 7) := by
  simp only [z75] <;> ring

theorem z75_bounds (d : Digits) (hd : Bounded d) :
    (0 : Int) ≤ z75 d ∧ z75 d ≤ 2097151 := by
  have h := hd 7
  norm_num at h
  rw [z75]
  omega

theorem z77_linear (d : Digits) : z77 d = (d 8) := by
  simp only [z77] <;> ring

theorem z77_bounds (d : Digits) (hd : Bounded d) :
    (0 : Int) ≤ z77 d ∧ z77 d ≤ 2097151 := by
  have h := hd 8
  norm_num at h
  rw [z77]
  omega

theorem z79_linear (d : Digits) : z79 d = (d 9) := by
  simp only [z79] <;> ring

theorem z79_bounds (d : Digits) (hd : Bounded d) :
    (0 : Int) ≤ z79 d ∧ z79 d ≤ 2097151 := by
  have h := hd 9
  norm_num at h
  rw [z79]
  omega

theorem z81_linear (d : Digits) : z81 d = (d 10) := by
  simp only [z81] <;> ring

theorem z81_bounds (d : Digits) (hd : Bounded d) :
    (0 : Int) ≤ z81 d ∧ z81 d ≤ 2097151 := by
  have h := hd 10
  norm_num at h
  rw [z81]
  omega

theorem z83_linear (d : Digits) : z83 d = (d 11) := by
  simp only [z83] <;> ring

theorem z83_bounds (d : Digits) (hd : Bounded d) :
    (0 : Int) ≤ z83 d ∧ z83 d ≤ 2097151 := by
  have h := hd 11
  norm_num at h
  rw [z83]
  omega

theorem z85_linear (d : Digits) : z85 d = (d 12) := by
  simp only [z85] <;> ring

theorem z85_bounds (d : Digits) (hd : Bounded d) :
    (0 : Int) ≤ z85 d ∧ z85 d ≤ 2097151 := by
  have h := hd 12
  norm_num at h
  rw [z85]
  omega

theorem z87_linear (d : Digits) : z87 d = (d 13) := by
  simp only [z87] <;> ring

theorem z87_bounds (d : Digits) (hd : Bounded d) :
    (0 : Int) ≤ z87 d ∧ z87 d ≤ 2097151 := by
  have h := hd 13
  norm_num at h
  rw [z87]
  omega

theorem z89_linear (d : Digits) : z89 d = (d 14) := by
  simp only [z89] <;> ring

theorem z89_bounds (d : Digits) (hd : Bounded d) :
    (0 : Int) ≤ z89 d ∧ z89 d ≤ 2097151 := by
  have h := hd 14
  norm_num at h
  rw [z89]
  omega

theorem z91_linear (d : Digits) : z91 d = (d 15) := by
  simp only [z91] <;> ring

theorem z91_bounds (d : Digits) (hd : Bounded d) :
    (0 : Int) ≤ z91 d ∧ z91 d ≤ 2097151 := by
  have h := hd 15
  norm_num at h
  rw [z91]
  omega

theorem z93_linear (d : Digits) : z93 d = (d 16) := by
  simp only [z93] <;> ring

theorem z93_bounds (d : Digits) (hd : Bounded d) :
    (0 : Int) ≤ z93 d ∧ z93 d ≤ 2097151 := by
  have h := hd 16
  norm_num at h
  rw [z93]
  omega

theorem z95_linear (d : Digits) : z95 d = (d 17) := by
  simp only [z95] <;> ring

theorem z95_bounds (d : Digits) (hd : Bounded d) :
    (0 : Int) ≤ z95 d ∧ z95 d ≤ 2097151 := by
  have h := hd 17
  norm_num at h
  rw [z95]
  omega

theorem z97_linear (d : Digits) : z97 d = (d 18) := by
  simp only [z97] <;> ring

theorem z97_bounds (d : Digits) (hd : Bounded d) :
    (0 : Int) ≤ z97 d ∧ z97 d ≤ 2097151 := by
  have h := hd 18
  norm_num at h
  rw [z97]
  omega

theorem z99_linear (d : Digits) : z99 d = (d 19) := by
  simp only [z99] <;> ring

theorem z99_bounds (d : Digits) (hd : Bounded d) :
    (0 : Int) ≤ z99 d ∧ z99 d ≤ 2097151 := by
  have h := hd 19
  norm_num at h
  rw [z99]
  omega

theorem z101_linear (d : Digits) : z101 d = (d 20) := by
  simp only [z101] <;> ring

theorem z101_bounds (d : Digits) (hd : Bounded d) :
    (0 : Int) ≤ z101 d ∧ z101 d ≤ 2097151 := by
  have h := hd 20
  norm_num at h
  rw [z101]
  omega

theorem z103_linear (d : Digits) : z103 d = (d 21) := by
  simp only [z103] <;> ring

theorem z103_bounds (d : Digits) (hd : Bounded d) :
    (0 : Int) ≤ z103 d ∧ z103 d ≤ 2097151 := by
  have h := hd 21
  norm_num at h
  rw [z103]
  omega

theorem z105_linear (d : Digits) : z105 d = (d 22) := by
  simp only [z105] <;> ring

theorem z105_bounds (d : Digits) (hd : Bounded d) :
    (0 : Int) ≤ z105 d ∧ z105 d ≤ 2097151 := by
  have h := hd 22
  norm_num at h
  rw [z105]
  omega

theorem z106_linear (d : Digits) : z106 d = (d 23) := by
  simp only [z106] <;> ring

theorem z106_bounds (d : Digits) (hd : Bounded d) :
    (0 : Int) ≤ z106 d ∧ z106 d ≤ 536870911 := by
  have h := hd 23
  norm_num at h
  rw [z106]
  omega

theorem z107_linear (d : Digits) : z107 d = (666643) * (d 23) := by
  simp only [z107, z106_linear] <;> ring

theorem z107_bounds (d : Digits) (hd : Bounded d) :
    (0 : Int) ≤ z107 d ∧ z107 d ≤ 357901234721773 := by
  have h0 := hd 23
  norm_num at h0
  rw [z107_linear]
  omega

theorem z108_linear (d : Digits) : z108 d = (d 11) + (666643) * (d 23) := by
  simp only [z108, z107_linear, z83_linear] <;> ring

theorem z108_bounds (d : Digits) (hd : Bounded d) :
    (0 : Int) ≤ z108 d ∧ z108 d ≤ 357901236818924 := by
  have h0 := hd 11
  norm_num at h0
  have h1 := hd 23
  norm_num at h1
  rw [z108_linear]
  omega

theorem z109_linear (d : Digits) : z109 d = (470296) * (d 23) := by
  simp only [z109, z106_linear] <;> ring

theorem z109_bounds (d : Digits) (hd : Bounded d) :
    (0 : Int) ≤ z109 d ∧ z109 d ≤ 252488241959656 := by
  have h0 := hd 23
  norm_num at h0
  rw [z109_linear]
  omega

theorem z110_linear (d : Digits) : z110 d = (d 12) + (470296) * (d 23) := by
  simp only [z110, z109_linear, z85_linear] <;> ring

theorem z110_bounds (d : Digits) (hd : Bounded d) :
    (0 : Int) ≤ z110 d ∧ z110 d ≤ 252488244056807 := by
  have h0 := hd 12
  norm_num at h0
  have h1 := hd 23
  norm_num at h1
  rw [z110_linear]
  omega

theorem z111_linear (d : Digits) : z111 d = (654183) * (d 23) := by
  simp only [z111, z106_linear] <;> ring

theorem z111_bounds (d : Digits) (hd : Bounded d) :
    (0 : Int) ≤ z111 d ∧ z111 d ≤ 351211823170713 := by
  have h0 := hd 23
  norm_num at h0
  rw [z111_linear]
  omega

theorem z112_linear (d : Digits) : z112 d = (d 13) + (654183) * (d 23) := by
  simp only [z112, z111_linear, z87_linear] <;> ring

theorem z112_bounds (d : Digits) (hd : Bounded d) :
    (0 : Int) ≤ z112 d ∧ z112 d ≤ 351211825267864 := by
  have h0 := hd 13
  norm_num at h0
  have h1 := hd 23
  norm_num at h1
  rw [z112_linear]
  omega

theorem z113_linear (d : Digits) : z113 d = (-997805) * (d 23) := by
  simp only [z113, z106_linear] <;> ring

theorem z113_bounds (d : Digits) (hd : Bounded d) :
    (-535692479350355 : Int) ≤ z113 d ∧ z113 d ≤ 0 := by
  have h0 := hd 23
  norm_num at h0
  rw [z113_linear]
  omega

theorem z114_linear (d : Digits) : z114 d = (d 14) + (-997805) * (d 23) := by
  simp only [z114, z113_linear, z89_linear] <;> ring

theorem z114_bounds (d : Digits) (hd : Bounded d) :
    (-535692479350355 : Int) ≤ z114 d ∧ z114 d ≤ 2097151 := by
  have h0 := hd 14
  norm_num at h0
  have h1 := hd 23
  norm_num at h1
  rw [z114_linear]
  omega

theorem z115_linear (d : Digits) : z115 d = (136657) * (d 23) := by
  simp only [z115, z106_linear] <;> ring

theorem z115_bounds (d : Digits) (hd : Bounded d) :
    (0 : Int) ≤ z115 d ∧ z115 d ≤ 73367168084527 := by
  have h0 := hd 23
  norm_num at h0
  rw [z115_linear]
  omega

theorem z116_linear (d : Digits) : z116 d = (d 15) + (136657) * (d 23) := by
  simp only [z116, z115_linear, z91_linear] <;> ring

theorem z116_bounds (d : Digits) (hd : Bounded d) :
    (0 : Int) ≤ z116 d ∧ z116 d ≤ 73367170181678 := by
  have h0 := hd 15
  norm_num at h0
  have h1 := hd 23
  norm_num at h1
  rw [z116_linear]
  omega

theorem z117_linear (d : Digits) : z117 d = (-683901) * (d 23) := by
  simp only [z117, z106_linear] <;> ring

theorem z117_bounds (d : Digits) (hd : Bounded d) :
    (-367166552903811 : Int) ≤ z117 d ∧ z117 d ≤ 0 := by
  have h0 := hd 23
  norm_num at h0
  rw [z117_linear]
  omega

theorem z118_linear (d : Digits) : z118 d = (d 16) + (-683901) * (d 23) := by
  simp only [z118, z117_linear, z93_linear] <;> ring

theorem z118_bounds (d : Digits) (hd : Bounded d) :
    (-367166552903811 : Int) ≤ z118 d ∧ z118 d ≤ 2097151 := by
  have h0 := hd 16
  norm_num at h0
  have h1 := hd 23
  norm_num at h1
  rw [z118_linear]
  omega

theorem z119_linear (d : Digits) : z119 d = (666643) * (d 22) := by
  simp only [z119, z105_linear] <;> ring

theorem z119_bounds (d : Digits) (hd : Bounded d) :
    (0 : Int) ≤ z119 d ∧ z119 d ≤ 1398051034093 := by
  have h0 := hd 22
  norm_num at h0
  rw [z119_linear]
  omega

theorem z120_linear (d : Digits) : z120 d = (470296) * (d 22) := by
  simp only [z120, z105_linear] <;> ring

theorem z120_bounds (d : Digits) (hd : Bounded d) :
    (0 : Int) ≤ z120 d ∧ z120 d ≤ 986281726696 := by
  have h0 := hd 22
  norm_num at h0
  rw [z120_linear]
  omega

theorem z121_linear (d : Digits) : z121 d = (654183) * (d 22) := by
  simp only [z121, z105_linear] <;> ring

theorem z121_bounds (d : Digits) (hd : Bounded d) :
    (0 : Int) ≤ z121 d ∧ z121 d ≤ 1371920532633 := by
  have h0 := hd 22
  norm_num at h0
  rw [z121_linear]
  omega

theorem z122_linear (d : Digits) : z122 d = (-997805) * (d 22) := by
  simp only [z122, z105_linear] <;> ring

theorem z122_bounds (d : Digits) (hd : Bounded d) :
    (-2092547753555 : Int) ≤ z122 d ∧ z122 d ≤ 0 := by
  have h0 := hd 22
  norm_num at h0
  rw [z122_linear]
  omega

theorem z123_linear (d : Digits) : z123 d = (136657) * (d 22) := by
  simp only [z123, z105_linear] <;> ring

theorem z123_bounds (d : Digits) (hd : Bounded d) :
    (0 : Int) ≤ z123 d ∧ z123 d ≤ 286590364207 := by
  have h0 := hd 22
  norm_num at h0
  rw [z123_linear]
  omega

theorem z124_linear (d : Digits) : z124 d = (d 14) + (136657) * (d 22) + (-997805) * (d 23) := by
  simp only [z124, z114_linear, z123_linear] <;> ring

theorem z124_bounds (d : Digits) (hd : Bounded d) :
    (-535692479350355 : Int) ≤ z124 d ∧ z124 d ≤ 286592461358 := by
  have h0 := hd 14
  norm_num at h0
  have h1 := hd 22
  norm_num at h1
  have h2 := hd 23
  norm_num at h2
  rw [z124_linear]
  omega

theorem z125_linear (d : Digits) : z125 d = (-683901) * (d 22) := by
  simp only [z125, z105_linear] <;> ring

theorem z125_bounds (d : Digits) (hd : Bounded d) :
    (-1434243666051 : Int) ≤ z125 d ∧ z125 d ≤ 0 := by
  have h0 := hd 22
  norm_num at h0
  rw [z125_linear]
  omega

theorem z126_linear (d : Digits) : z126 d = (d 15) + (-683901) * (d 22) + (136657) * (d 23) := by
  simp only [z126, z116_linear, z125_linear] <;> ring

theorem z126_bounds (d : Digits) (hd : Bounded d) :
    (-1434243666051 : Int) ≤ z126 d ∧ z126 d ≤ 73367170181678 := by
  have h0 := hd 15
  norm_num at h0
  have h1 := hd 22
  norm_num at h1
  have h2 := hd 23
  norm_num at h2
  rw [z126_linear]
  omega

theorem z127_linear (d : Digits) : z127 d = (666643) * (d 21) := by
  simp only [z127, z103_linear] <;> ring

theorem z127_bounds (d : Digits) (hd : Bounded d) :
    (0 : Int) ≤ z127 d ∧ z127 d ≤ 1398051034093 := by
  have h0 := hd 21
  norm_num at h0
  rw [z127_linear]
  omega

theorem z128_linear (d : Digits) : z128 d = (470296) * (d 21) := by
  simp only [z128, z103_linear] <;> ring

theorem z128_bounds (d : Digits) (hd : Bounded d) :
    (0 : Int) ≤ z128 d ∧ z128 d ≤ 986281726696 := by
  have h0 := hd 21
  norm_num at h0
  rw [z128_linear]
  omega

theorem z129_linear (d : Digits) : z129 d = (654183) * (d 21) := by
  simp only [z129, z103_linear] <;> ring

theorem z129_bounds (d : Digits) (hd : Bounded d) :
    (0 : Int) ≤ z129 d ∧ z129 d ≤ 1371920532633 := by
  have h0 := hd 21
  norm_num at h0
  rw [z129_linear]
  omega

theorem z130_linear (d : Digits) : z130 d = (-997805) * (d 21) := by
  simp only [z130, z103_linear] <;> ring

theorem z130_bounds (d : Digits) (hd : Bounded d) :
    (-2092547753555 : Int) ≤ z130 d ∧ z130 d ≤ 0 := by
  have h0 := hd 21
  norm_num at h0
  rw [z130_linear]
  omega

theorem z131_linear (d : Digits) : z131 d = (136657) * (d 21) := by
  simp only [z131, z103_linear] <;> ring

theorem z131_bounds (d : Digits) (hd : Bounded d) :
    (0 : Int) ≤ z131 d ∧ z131 d ≤ 286590364207 := by
  have h0 := hd 21
  norm_num at h0
  rw [z131_linear]
  omega

theorem z132_linear (d : Digits) : z132 d = (-683901) * (d 21) := by
  simp only [z132, z103_linear] <;> ring

theorem z132_bounds (d : Digits) (hd : Bounded d) :
    (-1434243666051 : Int) ≤ z132 d ∧ z132 d ≤ 0 := by
  have h0 := hd 21
  norm_num at h0
  rw [z132_linear]
  omega

theorem z133_linear (d : Digits) : z133 d = (d 14) + (-683901) * (d 21) + (136657) * (d 22) + (-997805) * (d 23) := by
  simp only [z133, z124_linear, z132_linear] <;> ring

theorem z133_bounds (d : Digits) (hd : Bounded d) :
    (-537126723016406 : Int) ≤ z133 d ∧ z133 d ≤ 286592461358 := by
  have h0 := hd 14
  norm_num at h0
  have h1 := hd 21
  norm_num at h1
  have h2 := hd 22
  norm_num at h2
  have h3 := hd 23
  norm_num at h3
  rw [z133_linear]
  omega

theorem z134_linear (d : Digits) : z134 d = (666643) * (d 20) := by
  simp only [z134, z101_linear] <;> ring

theorem z134_bounds (d : Digits) (hd : Bounded d) :
    (0 : Int) ≤ z134 d ∧ z134 d ≤ 1398051034093 := by
  have h0 := hd 20
  norm_num at h0
  rw [z134_linear]
  omega

theorem z135_linear (d : Digits) : z135 d = (666643) * (d 20) + (d 8) := by
  simp only [z135, z134_linear, z77_linear] <;> ring

theorem z135_bounds (d : Digits) (hd : Bounded d) :
    (0 : Int) ≤ z135 d ∧ z135 d ≤ 1398053131244 := by
  have h0 := hd 20
  norm_num at h0
  have h1 := hd 8
  norm_num at h1
  rw [z135_linear]
  omega

theorem z136_linear (d : Digits) : z136 d = (470296) * (d 20) := by
  simp only [z136, z101_linear] <;> ring

theorem z136_bounds (d : Digits) (hd : Bounded d) :
    (0 : Int) ≤ z136 d ∧ z136 d ≤ 986281726696 := by
  have h0 := hd 20
  norm_num at h0
  rw [z136_linear]
  omega

theorem z137_linear (d : Digits) : z137 d = (654183) * (d 20) := by
  simp only [z137, z101_linear] <;> ring

theorem z137_bounds (d : Digits) (hd : Bounded d) :
    (0 : Int) ≤ z137 d ∧ z137 d ≤ 1371920532633 := by
  have h0 := hd 20
  norm_num at h0
  rw [z137_linear]
  omega

theorem z138_linear (d : Digits) : z138 d = (-997805) * (d 20) := by
  simp only [z138, z101_linear] <;> ring

theorem z138_bounds (d : Digits) (hd : Bounded d) :
    (-2092547753555 : Int) ≤ z138 d ∧ z138 d ≤ 0 := by
  have h0 := hd 20
  norm_num at h0
  rw [z138_linear]
  omega

theorem z139_linear (d : Digits) : z139 d = (136657) * (d 20) := by
  simp only [z139, z101_linear] <;> ring

theorem z139_bounds (d : Digits) (hd : Bounded d) :
    (0 : Int) ≤ z139 d ∧ z139 d ≤ 286590364207 := by
  have h0 := hd 20
  norm_num at h0
  rw [z139_linear]
  omega

theorem z140_linear (d : Digits) : z140 d = (-683901) * (d 20) := by
  simp only [z140, z101_linear] <;> ring

theorem z140_bounds (d : Digits) (hd : Bounded d) :
    (-1434243666051 : Int) ≤ z140 d ∧ z140 d ≤ 0 := by
  have h0 := hd 20
  norm_num at h0
  rw [z140_linear]
  omega

theorem z141_linear (d : Digits) : z141 d = (666643) * (d 19) := by
  simp only [z141, z99_linear] <;> ring

theorem z141_bounds (d : Digits) (hd : Bounded d) :
    (0 : Int) ≤ z141 d ∧ z141 d ≤ 1398051034093 := by
  have h0 := hd 19
  norm_num at h0
  rw [z141_linear]
  omega

theorem z142_linear (d : Digits) : z142 d = (666643) * (d 19) + (d 7) := by
  simp only [z142, z141_linear, z75_linear] <;> ring

theorem z142_bounds (d : Digits) (hd : Bounded d) :
    (0 : Int) ≤ z142 d ∧ z142 d ≤ 1398053131244 := by
  have h0 := hd 19
  norm_num at h0
  have h1 := hd 7
  norm_num at h1
  rw [z142_linear]
  omega

theorem z143_linear (d : Digits) : z143 d = (470296) * (d 19) := by
  simp only [z143, z99_linear] <;> ring

theorem z143_bounds (d : Digits) (hd : Bounded d) :
    (0 : Int) ≤ z143 d ∧ z143 d ≤ 986281726696 := by
  have h0 := hd 19
  norm_num at h0
  rw [z143_linear]
  omega

theorem z144_linear (d : Digits) : z144 d = (470296) * (d 19) + (666643) * (d 20) + (d 8) := by
  simp only [z144, z135_linear, z143_linear] <;> ring

theorem z144_bounds (d : Digits) (hd : Bounded d) :
    (0 : Int) ≤ z144 d ∧ z144 d ≤ 2384334857940 := by
  have h0 := hd 19
  norm_num at h0
  have h1 := hd 20
  norm_num at h1
  have h2 := hd 8
  norm_num at h2
  rw [z144_linear]
  omega

theorem z145_linear (d : Digits) : z145 d = (654183) * (d 19) := by
  simp only [z145, z99_linear] <;> ring

theorem z145_bounds (d : Digits) (hd : Bounded d) :
    (0 : Int) ≤ z145 d ∧ z145 d ≤ 1371920532633 := by
  have h0 := hd 19
  norm_num at h0
  rw [z145_linear]
  omega

theorem z146_linear (d : Digits) : z146 d = (-997805) * (d 19) := by
  simp only [z146, z99_linear] <;> ring

theorem z146_bounds (d : Digits) (hd : Bounded d) :
    (-2092547753555 : Int) ≤ z146 d ∧ z146 d ≤ 0 := by
  have h0 := hd 19
  norm_num at h0
  rw [z146_linear]
  omega

theorem z147_linear (d : Digits) : z147 d = (136657) * (d 19) := by
  simp only [z147, z99_linear] <;> ring

theorem z147_bounds (d : Digits) (hd : Bounded d) :
    (0 : Int) ≤ z147 d ∧ z147 d ≤ 286590364207 := by
  have h0 := hd 19
  norm_num at h0
  rw [z147_linear]
  omega

theorem z148_linear (d : Digits) : z148 d = (-683901) * (d 19) := by
  simp only [z148, z99_linear] <;> ring

theorem z148_bounds (d : Digits) (hd : Bounded d) :
    (-1434243666051 : Int) ≤ z148 d ∧ z148 d ≤ 0 := by
  have h0 := hd 19
  norm_num at h0
  rw [z148_linear]
  omega

theorem z149_linear (d : Digits) : z149 d = (d 12) + (136657) * (d 20) + (470296) * (d 23) := by
  simp only [z149, z110_linear, z139_linear] <;> ring

theorem z149_bounds (d : Digits) (hd : Bounded d) :
    (0 : Int) ≤ z149 d ∧ z149 d ≤ 252774834421014 := by
  have h0 := hd 12
  norm_num at h0
  have h1 := hd 20
  norm_num at h1
  have h2 := hd 23
  norm_num at h2
  rw [z149_linear]
  omega

theorem z150_linear (d : Digits) : z150 d = (d 12) + (-683901) * (d 19) + (136657) * (d 20) + (470296) * (d 23) := by
  simp only [z150, z149_linear, z148_linear] <;> ring

theorem z150_bounds (d : Digits) (hd : Bounded d) :
    (-1434243666051 : Int) ≤ z150 d ∧ z150 d ≤ 252774834421014 := by
  have h0 := hd 12
  norm_num at h0
  have h1 := hd 19
  norm_num at h1
  have h2 := hd 20
  norm_num at h2
  have h3 := hd 23
  norm_num at h3
  rw [z150_linear]
  omega

theorem z151_linear (d : Digits) : z151 d = (d 12) + (-683901) * (d 19) + (136657) * (d 20) + (654183) * (d 22) + (470296) * (d 23) := by
  simp only [z151, z150_linear, z121_linear] <;> ring

theorem z151_bounds (d : Digits) (hd : Bounded d) :
    (-1434243666051 : Int) ≤ z151 d ∧ z151 d ≤ 254146754953647 := by
  have h0 := hd 12
  norm_num at h0
  have h1 := hd 19
  norm_num at h1
  have h2 := hd 20
  norm_num at h2
  have h3 := hd 22
  norm_num at h3
  have h4 := hd 23
  norm_num at h4
  rw [z151_linear]
  omega

theorem z152_linear (d : Digits) : z152 d = (d 12) + (-683901) * (d 19) + (136657) * (d 20) + (-997805) * (d 21) + (654183) * (d 22) + (470296) * (d 23) := by
  simp only [z152, z151_linear, z130_linear] <;> ring

theorem z152_bounds (d : Digits) (hd : Bounded d) :
    (-3526791419606 : Int) ≤ z152 d ∧ z152 d ≤ 254146754953647 := by
  have h0 := hd 12
  norm_num at h0
  have h1 := hd 19
  norm_num at h1
  have h2 := hd 20
  norm_num at h2
  have h3 := hd 21
  norm_num at h3
  have h4 := hd 22
  norm_num at h4
  have h5 := hd 23
  norm_num at h5
  rw [z152_linear]
  omega

theorem z153_linear (d : Digits) : z153 d = (666643) * (d 18) := by
  simp only [z153, z97_linear] <;> ring

theorem z153_bounds (d : Digits) (hd : Bounded d) :
    (0 : Int) ≤ z153 d ∧ z153 d ≤ 1398051034093 := by
  have h0 := hd 18
  norm_num at h0
  rw [z153_linear]
  omega

theorem z154_linear (d : Digits) : z154 d = (666643) * (d 18) + (d 6) := by
  simp only [z154, z153_linear, z73_linear] <;> ring

theorem z154_bounds (d : Digits) (hd : Bounded d) :
    (0 : Int) ≤ z154 d ∧ z154 d ≤ 1398053131244 := by
  have h0 := hd 18
  norm_num at h0
  have h1 := hd 6
  norm_num at h1
  rw [z154_linear]
  omega

theorem z155_linear (d : Digits) : z155 d = (470296) * (d 18) := by
  simp only [z155, z97_linear] <;> ring

theorem z155_bounds (d : Digits) (hd : Bounded d) :
    (0 : Int) ≤ z155 d ∧ z155 d ≤ 986281726696 := by
  have h0 := hd 18
  norm_num at h0
  rw [z155_linear]
  omega

theorem z156_linear (d : Digits) : z156 d = (470296) * (d 18) + (666643) * (d 19) + (d 7) := by
  simp only [z156, z142_linear, z155_linear] <;> ring

theorem z156_bounds (d : Digits) (hd : Bounded d) :
    (0 : Int) ≤ z156 d ∧ z156 d ≤ 2384334857940 := by
  have h0 := hd 18
  norm_num at h0
  have h1 := hd 19
  norm_num at h1
  have h2 := hd 7
  norm_num at h2
  rw [z156_linear]
  omega

theorem z157_linear (d : Digits) : z157 d = (654183) * (d 18) := by
  simp only [z157, z97_linear] <;> ring

theorem z157_bounds (d : Digits) (hd : Bounded d) :
    (0 : Int) ≤ z157 d ∧ z157 d ≤ 1371920532633 := by
  have h0 := hd 18
  norm_num at h0
  rw [z157_linear]
  omega

theorem z158_linear (d : Digits) : z158 d = (654183) * (d 18) + (470296) * (d 19) + (666643) * (d 20) + (d 8) := by
  simp only [z158, z144_linear, z157_linear] <;> ring

theorem z158_bounds (d : Digits) (hd : Bounded d) :
    (0 : Int) ≤ z158 d ∧ z158 d ≤ 3756255390573 := by
  have h0 := hd 18
  norm_num at h0
  have h1 := hd 19
  norm_num at h1
  have h2 := hd 20
  norm_num at h2
  have h3 := hd 8
  norm_num at h3
  rw [z158_linear]
  omega

theorem z159_linear (d : Digits) : z159 d = (-997805) * (d 18) := by
  simp only [z159, z97_linear] <;> ring

theorem z159_bounds (d : Digits) (hd : Bounded d) :
    (-2092547753555 : Int) ≤ z159 d ∧ z159 d ≤ 0 := by
  have h0 := hd 18
  norm_num at h0
  rw [z159_linear]
  omega

theorem z160_linear (d : Digits) : z160 d = (136657) * (d 18) := by
  simp only [z160, z97_linear] <;> ring

theorem z160_bounds (d : Digits) (hd : Bounded d) :
    (0 : Int) ≤ z160 d ∧ z160 d ≤ 286590364207 := by
  have h0 := hd 18
  norm_num at h0
  rw [z160_linear]
  omega

theorem z161_linear (d : Digits) : z161 d = (d 10) + (654183) * (d 20) := by
  simp only [z161, z137_linear, z81_linear] <;> ring

theorem z161_bounds (d : Digits) (hd : Bounded d) :
    (0 : Int) ≤ z161 d ∧ z161 d ≤ 1371922629784 := by
  have h0 := hd 10
  norm_num at h0
  have h1 := hd 20
  norm_num at h1
  rw [z161_linear]
  omega

theorem z162_linear (d : Digits) : z162 d = (d 10) + (-997805) * (d 19) + (654183) * (d 20) := by
  simp only [z162, z161_linear, z146_linear] <;> ring

theorem z162_bounds (d : Digits) (hd : Bounded d) :
    (-2092547753555 : Int) ≤ z162 d ∧ z162 d ≤ 1371922629784 := by
  have h0 := hd 10
  norm_num at h0
  have h1 := hd 19
  norm_num at h1
  have h2 := hd 20
  norm_num at h2
  rw [z162_linear]
  omega

theorem z163_linear (d : Digits) : z163 d = (d 10) + (136657) * (d 18) + (-997805) * (d 19) + (654183) * (d 20) := by
  simp only [z163, z162_linear, z160_linear] <;> ring

theorem z163_bounds (d : Digits) (hd : Bounded d) :
    (-2092547753555 : Int) ≤ z163 d ∧ z163 d ≤ 1658512993991 := by
  have h0 := hd 10
  norm_num at h0
  have h1 := hd 18
  norm_num at h1
  have h2 := hd 19
  norm_num at h2
  have h3 := hd 20
  norm_num at h3
  rw [z163_linear]
  omega

theorem z164_linear (d : Digits) : z164 d = (d 10) + (136657) * (d 18) + (-997805) * (d 19) + (654183) * (d 20) + (666643) * (d 22) := by
  simp only [z164, z163_linear, z119_linear] <;> ring

theorem z164_bounds (d : Digits) (hd : Bounded d) :
    (-2092547753555 : Int) ≤ z164 d ∧ z164 d ≤ 3056564028084 := by
  have h0 := hd 10
  norm_num at h0
  have h1 := hd 18
  norm_num at h1
  have h2 := hd 19
  norm_num at h2
  have h3 := hd 20
  norm_num at h3
  have h4 := hd 22
  norm_num at h4
  rw [z164_linear]
  omega

theorem z165_linear (d : Digits) : z165 d = (d 10) + (136657) * (d 18) + (-997805) * (d 19) + (654183) * (d 20) + (470296) * (d 21) + (666643) * (d 22) := by
  simp only [z165, z164_linear, z128_linear] <;> ring

theorem z165_bounds (d : Digits) (hd : Bounded d) :
    (-2092547753555 : Int) ≤ z165 d ∧ z165 d ≤ 4042845754780 := by
  have h0 := hd 10
  norm_num at h0
  have h1 := hd 18
  norm_num at h1
  have h2 := hd 19
  norm_num at h2
  have h3 := hd 20
  norm_num at h3
  have h4 := hd 21
  norm_num at h4
  have h5 := hd 22
  norm_num at h5
  rw [z165_linear]
  omega

theorem z166_linear (d : Digits) : z166 d = (-683901) * (d 18) := by
  simp only [z166, z97_linear] <;> ring

theorem z166_bounds (d : Digits) (hd : Bounded d) :
    (-1434243666051 : Int) ≤ z166 d ∧ z166 d ≤ 0 := by
  have h0 := hd 18
  norm_num at h0
  rw [z166_linear]
  omega

end Firedancer.Common.ScalarArithmetic.IntegerRegisters
