import SSA.Projects.Firedancer.Common.Proof.Scalar.Arithmetic.IntegerBounds0

/-! Checked linear identities and interval certificates for the corresponding
numbered source arithmetic registers. Generated equations are verified by
`ring` and `omega`; no external arithmetic result is trusted. -/

namespace Firedancer.Common.ScalarArithmetic.IntegerRegisters

set_option maxHeartbeats 2000000

attribute [local irreducible] z61 z63 z65 z67 z69 z71 z73 z75 z77 z79 z81 z83 z85 z87 z89 z91 z93 z95 z97 z99 z101 z103 z105 z106 z107 z108 z109 z110 z111 z112 z113 z114 z115 z116 z117 z118 z119 z120 z121 z122 z123 z124 z125 z126 z127 z128 z129 z130 z131 z132 z133 z134 z135 z136 z137 z138 z139 z140 z141 z142 z143 z144 z145 z146 z147 z148 z149 z150 z151 z152 z153 z154 z155 z156 z157 z158 z159 z160 z161 z162 z163 z164 z165 z166 z167 z168 z169 z170 z171 z172 z173 z174 z175 z176 z177 z178 z179 z180 z181 z182 z183 z184 z185 z186 z187 z188 z189 z190 z191 z192 z193 z194 z195 z196 z197 z198 z199 z200 z201 z202 z203 z204 z205 z206 z207 z208 z209 z210 z211 z212 z213 z214 z215 z216 z217 z218 z219 z220 z221 z222 z223 z224 z225 z226 z227 z228 z229 z230 z231 z232 z233 z234 z235 z236 z237 z238 z239 z240 z241 z242 z243 z244 z245 z246 z247 z248 z249 z250 z251 z252 z253 z254 z255 z256 z257 z258 z259 z260 z261 z262 z263 z264 z265 z266 z267 z268 z269 z270 z271 z272 z273 z274 z275 z276 z277 z278 z279 z280 z281 z282 z283 z284 z285 z286 z287 z288 z289 z290 z291 z292 z293 z294 z295 z296 z297 z298 z299 z300 z301 z302 z303 z304 z305 z306 z307 z308 z309 z310 z311 z312 z313 z314 z315 z316 z317 z318 z319 z320 z321 z322 z323 z324 z325 z326 z327 z328 z329 z330 z331 z332 z333 z334 z335 z336 z337 z338 z339 z340 z341 z342 z343 z344 z345 z346 z347 z348 z349 z350 z351 z352 z353 z354 z355 z356 z357 z358 z359 z360 z361 z362 z363 z364 z365 z366 z367 z368 z369 z370 z371 z372 z373 z374 z375 z376 z377 z378 z379 z380 z381 z382 z383 z384 z385 z386 z387 z388 z389 z390 z391 z392 z393 z394 z395 z396 z397 z398 z399 z400 z401 z402 z403 z404 z405 z406 z407 z408 z409 z410 z411 z412 z413 z414 z415 z416 z417 z418 z419 z420 z421 z422 z423 z424 z425 z426 z427 z428 z429 z430 z431 z432 z433 z434 z435 z436 z437 z438 z439 z440 z441 z442 z443 z444 z445 z446 m170 m179 m189 m196 m201 m206 m210 m213 m217 m222 m227 m301 m306 m311 m321 m329 m334 m338 m341 m345 m349 m354 m358

theorem z167_linear (d : Digits) : z167 d = (666643) * (d 18) + (d 6) + 1048576 := by
  simp only [z167, z154_linear] <;> ring

theorem z167_bounds (d : Digits) (hd : Bounded d) :
    (1048576 : Int) ≤ z167 d ∧ z167 d ≤ 1398054179820 := by
  have h0 := hd 18
  norm_num at h0
  have h1 := hd 6
  norm_num at h1
  rw [z167_linear]
  omega

theorem z168_bounds (d : Digits) (hd : Bounded d) :
    (0 : Int) ≤ z168 d ∧ z168 d ≤ 666644 := by
  have h := z167_bounds d hd
  rw [z168]
  omega

theorem z169_linear (d : Digits) : z169 d = (470296) * (d 18) + (666643) * (d 19) + (d 7) + (z168 d) := by
  simp only [z169, z156_linear] <;> ring

theorem z169_bounds (d : Digits) (hd : Bounded d) :
    (0 : Int) ≤ z169 d ∧ z169 d ≤ 2384335524584 := by
  have h0 := hd 18
  norm_num at h0
  have h1 := hd 19
  norm_num at h1
  have h2 := hd 7
  norm_num at h2
  have h3 := z168_bounds d hd
  rw [z169_linear]
  omega

theorem m170_bounds (d : Digits) : 0 ≤ m170 d ∧ m170 d ≤ 2097151 := by
  rw [m170]
  omega

theorem z170_linear (d : Digits) : z170 d = (666643) * (d 18) + (d 6) + (-1) * (m170 d) + 1048576 := by
  simp only [z170, z167_linear] <;> ring

theorem z170_bounds (d : Digits) (hd : Bounded d) :
    (-1048575 : Int) ≤ z170 d ∧ z170 d ≤ 1398054179820 := by
  have h0 := hd 18
  norm_num at h0
  have h1 := hd 6
  norm_num at h1
  have h2 := m170_bounds d
  rw [z170_linear]
  omega

theorem z171_linear (d : Digits) : z171 d = (m170 d) + -1048576 := by
  simp only [z171, z154_linear, z170_linear] <;> ring

theorem z171_bounds (d : Digits) (hd : Bounded d) :
    (-1048576 : Int) ≤ z171 d ∧ z171 d ≤ 1048575 := by
  have h0 := m170_bounds d
  rw [z171_linear]
  omega

theorem z172_linear (d : Digits) : z172 d = (654183) * (d 18) + (470296) * (d 19) + (666643) * (d 20) + (d 8) + 1048576 := by
  simp only [z172, z158_linear] <;> ring

theorem z172_bounds (d : Digits) (hd : Bounded d) :
    (1048576 : Int) ≤ z172 d ∧ z172 d ≤ 3756256439149 := by
  have h0 := hd 18
  norm_num at h0
  have h1 := hd 19
  norm_num at h1
  have h2 := hd 20
  norm_num at h2
  have h3 := hd 8
  norm_num at h3
  rw [z172_linear]
  omega

theorem z173_bounds (d : Digits) (hd : Bounded d) :
    (0 : Int) ≤ z173 d ∧ z173 d ≤ 1791122 := by
  have h := z172_bounds d hd
  rw [z173]
  omega

theorem z174_linear (d : Digits) : z174 d = (470296) * (d 20) + (d 9) := by
  simp only [z174, z136_linear, z79_linear] <;> ring

theorem z174_bounds (d : Digits) (hd : Bounded d) :
    (0 : Int) ≤ z174 d ∧ z174 d ≤ 986283823847 := by
  have h0 := hd 20
  norm_num at h0
  have h1 := hd 9
  norm_num at h1
  rw [z174_linear]
  omega

theorem z175_linear (d : Digits) : z175 d = (654183) * (d 19) + (470296) * (d 20) + (d 9) := by
  simp only [z175, z174_linear, z145_linear] <;> ring

theorem z175_bounds (d : Digits) (hd : Bounded d) :
    (0 : Int) ≤ z175 d ∧ z175 d ≤ 2358204356480 := by
  have h0 := hd 19
  norm_num at h0
  have h1 := hd 20
  norm_num at h1
  have h2 := hd 9
  norm_num at h2
  rw [z175_linear]
  omega

theorem z176_linear (d : Digits) : z176 d = (-997805) * (d 18) + (654183) * (d 19) + (470296) * (d 20) + (d 9) := by
  simp only [z176, z175_linear, z159_linear] <;> ring

theorem z176_bounds (d : Digits) (hd : Bounded d) :
    (-2092547753555 : Int) ≤ z176 d ∧ z176 d ≤ 2358204356480 := by
  have h0 := hd 18
  norm_num at h0
  have h1 := hd 19
  norm_num at h1
  have h2 := hd 20
  norm_num at h2
  have h3 := hd 9
  norm_num at h3
  rw [z176_linear]
  omega

theorem z177_linear (d : Digits) : z177 d = (-997805) * (d 18) + (654183) * (d 19) + (470296) * (d 20) + (666643) * (d 21) + (d 9) := by
  simp only [z177, z176_linear, z127_linear] <;> ring

theorem z177_bounds (d : Digits) (hd : Bounded d) :
    (-2092547753555 : Int) ≤ z177 d ∧ z177 d ≤ 3756255390573 := by
  have h0 := hd 18
  norm_num at h0
  have h1 := hd 19
  norm_num at h1
  have h2 := hd 20
  norm_num at h2
  have h3 := hd 21
  norm_num at h3
  have h4 := hd 9
  norm_num at h4
  rw [z177_linear]
  omega

theorem z178_linear (d : Digits) : z178 d = (-997805) * (d 18) + (654183) * (d 19) + (470296) * (d 20) + (666643) * (d 21) + (d 9) + (z173 d) := by
  simp only [z178, z177_linear] <;> ring

theorem z178_bounds (d : Digits) (hd : Bounded d) :
    (-2092547753555 : Int) ≤ z178 d ∧ z178 d ≤ 3756257181695 := by
  have h0 := hd 18
  norm_num at h0
  have h1 := hd 19
  norm_num at h1
  have h2 := hd 20
  norm_num at h2
  have h3 := hd 21
  norm_num at h3
  have h4 := hd 9
  norm_num at h4
  have h5 := z173_bounds d hd
  rw [z178_linear]
  omega

theorem m179_bounds (d : Digits) : 0 ≤ m179 d ∧ m179 d ≤ 2097151 := by
  rw [m179]
  omega

theorem z179_linear (d : Digits) : z179 d = (654183) * (d 18) + (470296) * (d 19) + (666643) * (d 20) + (d 8) + (-1) * (m179 d) + 1048576 := by
  simp only [z179, z172_linear] <;> ring

theorem z179_bounds (d : Digits) (hd : Bounded d) :
    (-1048575 : Int) ≤ z179 d ∧ z179 d ≤ 3756256439149 := by
  have h0 := hd 18
  norm_num at h0
  have h1 := hd 19
  norm_num at h1
  have h2 := hd 20
  norm_num at h2
  have h3 := hd 8
  norm_num at h3
  have h4 := m179_bounds d
  rw [z179_linear]
  omega

theorem z180_linear (d : Digits) : z180 d = (m179 d) + -1048576 := by
  simp only [z180, z158_linear, z179_linear] <;> ring

theorem z180_bounds (d : Digits) (hd : Bounded d) :
    (-1048576 : Int) ≤ z180 d ∧ z180 d ≤ 1048575 := by
  have h0 := m179_bounds d
  rw [z180_linear]
  omega

theorem z181_linear (d : Digits) : z181 d = (d 10) + (136657) * (d 18) + (-997805) * (d 19) + (654183) * (d 20) + (470296) * (d 21) + (666643) * (d 22) + 1048576 := by
  simp only [z181, z165_linear] <;> ring

theorem z181_bounds (d : Digits) (hd : Bounded d) :
    (-2092546704979 : Int) ≤ z181 d ∧ z181 d ≤ 4042846803356 := by
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
  rw [z181_linear]
  omega

theorem z182_bounds (d : Digits) (hd : Bounded d) :
    (-997805 : Int) ≤ z182 d ∧ z182 d ≤ 1927779 := by
  have h := z181_bounds d hd
  rw [z182]
  omega

theorem z183_linear (d : Digits) : z183 d = (d 11) + (-997805) * (d 20) + (666643) * (d 23) := by
  simp only [z183, z108_linear, z138_linear] <;> ring

theorem z183_bounds (d : Digits) (hd : Bounded d) :
    (-2092547753555 : Int) ≤ z183 d ∧ z183 d ≤ 357901236818924 := by
  have h0 := hd 11
  norm_num at h0
  have h1 := hd 20
  norm_num at h1
  have h2 := hd 23
  norm_num at h2
  rw [z183_linear]
  omega

theorem z184_linear (d : Digits) : z184 d = (d 11) + (136657) * (d 19) + (-997805) * (d 20) + (666643) * (d 23) := by
  simp only [z184, z183_linear, z147_linear] <;> ring

theorem z184_bounds (d : Digits) (hd : Bounded d) :
    (-2092547753555 : Int) ≤ z184 d ∧ z184 d ≤ 358187827183131 := by
  have h0 := hd 11
  norm_num at h0
  have h1 := hd 19
  norm_num at h1
  have h2 := hd 20
  norm_num at h2
  have h3 := hd 23
  norm_num at h3
  rw [z184_linear]
  omega

theorem z185_linear (d : Digits) : z185 d = (d 11) + (-683901) * (d 18) + (136657) * (d 19) + (-997805) * (d 20) + (666643) * (d 23) := by
  simp only [z185, z184_linear, z166_linear] <;> ring

theorem z185_bounds (d : Digits) (hd : Bounded d) :
    (-3526791419606 : Int) ≤ z185 d ∧ z185 d ≤ 358187827183131 := by
  have h0 := hd 11
  norm_num at h0
  have h1 := hd 18
  norm_num at h1
  have h2 := hd 19
  norm_num at h2
  have h3 := hd 20
  norm_num at h3
  have h4 := hd 23
  norm_num at h4
  rw [z185_linear]
  omega

theorem z186_linear (d : Digits) : z186 d = (d 11) + (-683901) * (d 18) + (136657) * (d 19) + (-997805) * (d 20) + (470296) * (d 22) + (666643) * (d 23) := by
  simp only [z186, z185_linear, z120_linear] <;> ring

theorem z186_bounds (d : Digits) (hd : Bounded d) :
    (-3526791419606 : Int) ≤ z186 d ∧ z186 d ≤ 359174108909827 := by
  have h0 := hd 11
  norm_num at h0
  have h1 := hd 18
  norm_num at h1
  have h2 := hd 19
  norm_num at h2
  have h3 := hd 20
  norm_num at h3
  have h4 := hd 22
  norm_num at h4
  have h5 := hd 23
  norm_num at h5
  rw [z186_linear]
  omega

theorem z187_linear (d : Digits) : z187 d = (d 11) + (-683901) * (d 18) + (136657) * (d 19) + (-997805) * (d 20) + (654183) * (d 21) + (470296) * (d 22) + (666643) * (d 23) := by
  simp only [z187, z186_linear, z129_linear] <;> ring

theorem z187_bounds (d : Digits) (hd : Bounded d) :
    (-3526791419606 : Int) ≤ z187 d ∧ z187 d ≤ 360546029442460 := by
  have h0 := hd 11
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
  have h6 := hd 23
  norm_num at h6
  rw [z187_linear]
  omega

theorem z188_linear (d : Digits) : z188 d = (d 11) + (-683901) * (d 18) + (136657) * (d 19) + (-997805) * (d 20) + (654183) * (d 21) + (470296) * (d 22) + (666643) * (d 23) + (z182 d) := by
  simp only [z188, z187_linear] <;> ring

theorem z188_bounds (d : Digits) (hd : Bounded d) :
    (-3526792417411 : Int) ≤ z188 d ∧ z188 d ≤ 360546031370239 := by
  have h0 := hd 11
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
  have h6 := hd 23
  norm_num at h6
  have h7 := z182_bounds d hd
  rw [z188_linear]
  omega

theorem m189_bounds (d : Digits) : 0 ≤ m189 d ∧ m189 d ≤ 2097151 := by
  rw [m189]
  omega

theorem z189_linear (d : Digits) : z189 d = (d 10) + (136657) * (d 18) + (-997805) * (d 19) + (654183) * (d 20) + (470296) * (d 21) + (666643) * (d 22) + (-1) * (m189 d) + 1048576 := by
  simp only [z189, z181_linear] <;> ring

theorem z189_bounds (d : Digits) (hd : Bounded d) :
    (-2092548802130 : Int) ≤ z189 d ∧ z189 d ≤ 4042846803356 := by
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
  have h6 := m189_bounds d
  rw [z189_linear]
  omega

theorem z190_linear (d : Digits) : z190 d = (d 12) + (-683901) * (d 19) + (136657) * (d 20) + (-997805) * (d 21) + (654183) * (d 22) + (470296) * (d 23) + 1048576 := by
  simp only [z190, z152_linear] <;> ring

theorem z190_bounds (d : Digits) (hd : Bounded d) :
    (-3526790371030 : Int) ≤ z190 d ∧ z190 d ≤ 254146756002223 := by
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
  rw [z190_linear]
  omega

theorem z191_bounds (d : Digits) (hd : Bounded d) :
    (-1681705 : Int) ≤ z191 d ∧ z191 d ≤ 121186616 := by
  have h := z190_bounds d hd
  rw [z191]
  omega

theorem z192_linear (d : Digits) : z192 d = (d 13) + (-683901) * (d 20) + (654183) * (d 23) := by
  simp only [z192, z112_linear, z140_linear] <;> ring

theorem z192_bounds (d : Digits) (hd : Bounded d) :
    (-1434243666051 : Int) ≤ z192 d ∧ z192 d ≤ 351211825267864 := by
  have h0 := hd 13
  norm_num at h0
  have h1 := hd 20
  norm_num at h1
  have h2 := hd 23
  norm_num at h2
  rw [z192_linear]
  omega

theorem z193_linear (d : Digits) : z193 d = (d 13) + (-683901) * (d 20) + (-997805) * (d 22) + (654183) * (d 23) := by
  simp only [z193, z192_linear, z122_linear] <;> ring

theorem z193_bounds (d : Digits) (hd : Bounded d) :
    (-3526791419606 : Int) ≤ z193 d ∧ z193 d ≤ 351211825267864 := by
  have h0 := hd 13
  norm_num at h0
  have h1 := hd 20
  norm_num at h1
  have h2 := hd 22
  norm_num at h2
  have h3 := hd 23
  norm_num at h3
  rw [z193_linear]
  omega

theorem z194_linear (d : Digits) : z194 d = (d 13) + (-683901) * (d 20) + (136657) * (d 21) + (-997805) * (d 22) + (654183) * (d 23) := by
  simp only [z194, z193_linear, z131_linear] <;> ring

theorem z194_bounds (d : Digits) (hd : Bounded d) :
    (-3526791419606 : Int) ≤ z194 d ∧ z194 d ≤ 351498415632071 := by
  have h0 := hd 13
  norm_num at h0
  have h1 := hd 20
  norm_num at h1
  have h2 := hd 21
  norm_num at h2
  have h3 := hd 22
  norm_num at h3
  have h4 := hd 23
  norm_num at h4
  rw [z194_linear]
  omega

theorem z195_linear (d : Digits) : z195 d = (d 13) + (-683901) * (d 20) + (136657) * (d 21) + (-997805) * (d 22) + (654183) * (d 23) + (z191 d) := by
  simp only [z195, z194_linear] <;> ring

theorem z195_bounds (d : Digits) (hd : Bounded d) :
    (-3526793101311 : Int) ≤ z195 d ∧ z195 d ≤ 351498536818687 := by
  have h0 := hd 13
  norm_num at h0
  have h1 := hd 20
  norm_num at h1
  have h2 := hd 21
  norm_num at h2
  have h3 := hd 22
  norm_num at h3
  have h4 := hd 23
  norm_num at h4
  have h5 := z191_bounds d hd
  rw [z195_linear]
  omega

theorem m196_bounds (d : Digits) : 0 ≤ m196 d ∧ m196 d ≤ 2097151 := by
  rw [m196]
  omega

theorem z196_linear (d : Digits) : z196 d = (d 12) + (-683901) * (d 19) + (136657) * (d 20) + (-997805) * (d 21) + (654183) * (d 22) + (470296) * (d 23) + (-1) * (m196 d) + 1048576 := by
  simp only [z196, z190_linear] <;> ring

theorem z196_bounds (d : Digits) (hd : Bounded d) :
    (-3526792468181 : Int) ≤ z196 d ∧ z196 d ≤ 254146756002223 := by
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
  have h6 := m196_bounds d
  rw [z196_linear]
  omega

theorem z197_linear (d : Digits) : z197 d = (m196 d) + -1048576 := by
  simp only [z197, z152_linear, z196_linear] <;> ring

theorem z197_bounds (d : Digits) (hd : Bounded d) :
    (-1048576 : Int) ≤ z197 d ∧ z197 d ≤ 1048575 := by
  have h0 := m196_bounds d
  rw [z197_linear]
  omega

theorem z198_linear (d : Digits) : z198 d = (d 14) + (-683901) * (d 21) + (136657) * (d 22) + (-997805) * (d 23) + 1048576 := by
  simp only [z198, z133_linear] <;> ring

theorem z198_bounds (d : Digits) (hd : Bounded d) :
    (-537126721967830 : Int) ≤ z198 d ∧ z198 d ≤ 286593509934 := by
  have h0 := hd 14
  norm_num at h0
  have h1 := hd 21
  norm_num at h1
  have h2 := hd 22
  norm_num at h2
  have h3 := hd 23
  norm_num at h3
  rw [z198_linear]
  omega

theorem z199_bounds (d : Digits) (hd : Bounded d) :
    (-256121980 : Int) ≤ z199 d ∧ z199 d ≤ 136658 := by
  have h := z198_bounds d hd
  rw [z199]
  omega

theorem z200_linear (d : Digits) : z200 d = (d 15) + (-683901) * (d 22) + (136657) * (d 23) + (z199 d) := by
  simp only [z200, z126_linear] <;> ring

theorem z200_bounds (d : Digits) (hd : Bounded d) :
    (-1434499788031 : Int) ≤ z200 d ∧ z200 d ≤ 73367170318336 := by
  have h0 := hd 15
  norm_num at h0
  have h1 := hd 22
  norm_num at h1
  have h2 := hd 23
  norm_num at h2
  have h3 := z199_bounds d hd
  rw [z200_linear]
  omega

theorem m201_bounds (d : Digits) : 0 ≤ m201 d ∧ m201 d ≤ 2097151 := by
  rw [m201]
  omega

theorem z201_linear (d : Digits) : z201 d = (d 14) + (-683901) * (d 21) + (136657) * (d 22) + (-997805) * (d 23) + (-1) * (m201 d) + 1048576 := by
  simp only [z201, z198_linear] <;> ring

theorem z201_bounds (d : Digits) (hd : Bounded d) :
    (-537126724064981 : Int) ≤ z201 d ∧ z201 d ≤ 286593509934 := by
  have h0 := hd 14
  norm_num at h0
  have h1 := hd 21
  norm_num at h1
  have h2 := hd 22
  norm_num at h2
  have h3 := hd 23
  norm_num at h3
  have h4 := m201_bounds d
  rw [z201_linear]
  omega

theorem z202_linear (d : Digits) : z202 d = (m201 d) + -1048576 := by
  simp only [z202, z133_linear, z201_linear] <;> ring

theorem z202_bounds (d : Digits) (hd : Bounded d) :
    (-1048576 : Int) ≤ z202 d ∧ z202 d ≤ 1048575 := by
  have h0 := m201_bounds d
  rw [z202_linear]
  omega

theorem z203_linear (d : Digits) : z203 d = (d 16) + (-683901) * (d 23) + 1048576 := by
  simp only [z203, z118_linear] <;> ring

theorem z203_bounds (d : Digits) (hd : Bounded d) :
    (-367166551855235 : Int) ≤ z203 d ∧ z203 d ≤ 3145727 := by
  have h0 := hd 16
  norm_num at h0
  have h1 := hd 23
  norm_num at h1
  rw [z203_linear]
  omega

theorem z204_bounds (d : Digits) (hd : Bounded d) :
    (-175078656 : Int) ≤ z204 d ∧ z204 d ≤ 1 := by
  have h := z203_bounds d hd
  rw [z204]
  omega

theorem z205_linear (d : Digits) : z205 d = (d 17) + (z204 d) := by
  simp only [z205, z95_linear] <;> ring

theorem z205_bounds (d : Digits) (hd : Bounded d) :
    (-175078656 : Int) ≤ z205 d ∧ z205 d ≤ 2097152 := by
  have h0 := hd 17
  norm_num at h0
  have h1 := z204_bounds d hd
  rw [z205_linear]
  omega

theorem m206_bounds (d : Digits) : 0 ≤ m206 d ∧ m206 d ≤ 2097151 := by
  rw [m206]
  omega

theorem z206_linear (d : Digits) : z206 d = (d 16) + (-683901) * (d 23) + (-1) * (m206 d) + 1048576 := by
  simp only [z206, z203_linear] <;> ring

theorem z206_bounds (d : Digits) (hd : Bounded d) :
    (-367166553952386 : Int) ≤ z206 d ∧ z206 d ≤ 3145727 := by
  have h0 := hd 16
  norm_num at h0
  have h1 := hd 23
  norm_num at h1
  have h2 := m206_bounds d
  rw [z206_linear]
  omega

theorem z207_linear (d : Digits) : z207 d = (m206 d) + -1048576 := by
  simp only [z207, z118_linear, z206_linear] <;> ring

theorem z207_bounds (d : Digits) (hd : Bounded d) :
    (-1048576 : Int) ≤ z207 d ∧ z207 d ≤ 1048575 := by
  have h0 := m206_bounds d
  rw [z207_linear]
  omega

theorem z208_linear (d : Digits) : z208 d = (470296) * (d 18) + (666643) * (d 19) + (d 7) + 1048576 + (z168 d) := by
  simp only [z208, z169_linear] <;> ring

theorem z208_bounds (d : Digits) (hd : Bounded d) :
    (1048576 : Int) ≤ z208 d ∧ z208 d ≤ 2384336573160 := by
  have h0 := hd 18
  norm_num at h0
  have h1 := hd 19
  norm_num at h1
  have h2 := hd 7
  norm_num at h2
  have h4 := z168_bounds d hd
  rw [z208_linear]
  omega

theorem z209_bounds (d : Digits) (hd : Bounded d) :
    (0 : Int) ≤ z209 d ∧ z209 d ≤ 1136940 := by
  have h := z208_bounds d hd
  rw [z209]
  omega

theorem m210_bounds (d : Digits) : 0 ≤ m210 d ∧ m210 d ≤ 2097151 := by
  rw [m210]
  omega

theorem z210_linear (d : Digits) : z210 d = (470296) * (d 18) + (666643) * (d 19) + (d 7) + (-1) * (m210 d) + 1048576 + (z168 d) := by
  simp only [z210, z208_linear] <;> ring

theorem z210_bounds (d : Digits) (hd : Bounded d) :
    (-1048575 : Int) ≤ z210 d ∧ z210 d ≤ 2384336573160 := by
  have h0 := hd 18
  norm_num at h0
  have h1 := hd 19
  norm_num at h1
  have h2 := hd 7
  norm_num at h2
  have h3 := m210_bounds d
  have h5 := z168_bounds d hd
  rw [z210_linear]
  omega

theorem z211_linear (d : Digits) : z211 d = (-997805) * (d 18) + (654183) * (d 19) + (470296) * (d 20) + (666643) * (d 21) + (d 9) + 1048576 + (z173 d) := by
  simp only [z211, z178_linear] <;> ring

theorem z211_bounds (d : Digits) (hd : Bounded d) :
    (-2092546704979 : Int) ≤ z211 d ∧ z211 d ≤ 3756258230271 := by
  have h0 := hd 18
  norm_num at h0
  have h1 := hd 19
  norm_num at h1
  have h2 := hd 20
  norm_num at h2
  have h3 := hd 21
  norm_num at h3
  have h4 := hd 9
  norm_num at h4
  have h6 := z173_bounds d hd
  rw [z211_linear]
  omega

theorem z212_bounds (d : Digits) (hd : Bounded d) :
    (-997805 : Int) ≤ z212 d ∧ z212 d ≤ 1791123 := by
  have h := z211_bounds d hd
  rw [z212]
  omega

theorem m213_bounds (d : Digits) : 0 ≤ m213 d ∧ m213 d ≤ 2097151 := by
  rw [m213]
  omega

theorem z213_linear (d : Digits) : z213 d = (-997805) * (d 18) + (654183) * (d 19) + (470296) * (d 20) + (666643) * (d 21) + (d 9) + (-1) * (m213 d) + 1048576 + (z173 d) := by
  simp only [z213, z211_linear] <;> ring

theorem z213_bounds (d : Digits) (hd : Bounded d) :
    (-2092548802130 : Int) ≤ z213 d ∧ z213 d ≤ 3756258230271 := by
  have h0 := hd 18
  norm_num at h0
  have h1 := hd 19
  norm_num at h1
  have h2 := hd 20
  norm_num at h2
  have h3 := hd 21
  norm_num at h3
  have h4 := hd 9
  norm_num at h4
  have h5 := m213_bounds d
  have h7 := z173_bounds d hd
  rw [z213_linear]
  omega

theorem z214_linear (d : Digits) : z214 d = (d 11) + (-683901) * (d 18) + (136657) * (d 19) + (-997805) * (d 20) + (654183) * (d 21) + (470296) * (d 22) + (666643) * (d 23) + 1048576 + (z182 d) := by
  simp only [z214, z188_linear] <;> ring

theorem z214_bounds (d : Digits) (hd : Bounded d) :
    (-3526791368835 : Int) ≤ z214 d ∧ z214 d ≤ 360546032418815 := by
  have h0 := hd 11
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
  have h6 := hd 23
  norm_num at h6
  have h8 := z182_bounds d hd
  rw [z214_linear]
  omega

theorem z215_bounds (d : Digits) (hd : Bounded d) :
    (-1681706 : Int) ≤ z215 d ∧ z215 d ≤ 171921745 := by
  have h := z214_bounds d hd
  rw [z215]
  omega

theorem z216_linear (d : Digits) : z216 d = (m196 d) + -1048576 + (z215 d) := by
  simp only [z216, z197_linear] <;> ring

theorem z216_bounds (d : Digits) (hd : Bounded d) :
    (-2730282 : Int) ≤ z216 d ∧ z216 d ≤ 172970320 := by
  have h0 := m196_bounds d
  have h2 := z215_bounds d hd
  rw [z216_linear]
  omega

theorem m217_bounds (d : Digits) : 0 ≤ m217 d ∧ m217 d ≤ 2097151 := by
  rw [m217]
  omega

theorem z217_linear (d : Digits) : z217 d = (d 11) + (-683901) * (d 18) + (136657) * (d 19) + (-997805) * (d 20) + (654183) * (d 21) + (470296) * (d 22) + (666643) * (d 23) + (-1) * (m217 d) + 1048576 + (z182 d) := by
  simp only [z217, z214_linear] <;> ring

theorem z217_bounds (d : Digits) (hd : Bounded d) :
    (-3526793465986 : Int) ≤ z217 d ∧ z217 d ≤ 360546032418815 := by
  have h0 := hd 11
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
  have h6 := hd 23
  norm_num at h6
  have h7 := m217_bounds d
  have h9 := z182_bounds d hd
  rw [z217_linear]
  omega

theorem z218_linear (d : Digits) : z218 d = (m217 d) + -1048576 := by
  simp only [z218, z188_linear, z217_linear] <;> ring

theorem z218_bounds (d : Digits) (hd : Bounded d) :
    (-1048576 : Int) ≤ z218 d ∧ z218 d ≤ 1048575 := by
  have h0 := m217_bounds d
  rw [z218_linear]
  omega

theorem z219_linear (d : Digits) : z219 d = (d 13) + (-683901) * (d 20) + (136657) * (d 21) + (-997805) * (d 22) + (654183) * (d 23) + 1048576 + (z191 d) := by
  simp only [z219, z195_linear] <;> ring

theorem z219_bounds (d : Digits) (hd : Bounded d) :
    (-3526792052735 : Int) ≤ z219 d ∧ z219 d ≤ 351498537867263 := by
  have h0 := hd 13
  norm_num at h0
  have h1 := hd 20
  norm_num at h1
  have h2 := hd 21
  norm_num at h2
  have h3 := hd 22
  norm_num at h3
  have h4 := hd 23
  norm_num at h4
  have h6 := z191_bounds d hd
  rw [z219_linear]
  omega

theorem z220_bounds (d : Digits) (hd : Bounded d) :
    (-1681706 : Int) ≤ z220 d ∧ z220 d ≤ 167607563 := by
  have h := z219_bounds d hd
  rw [z220]
  omega

theorem z221_linear (d : Digits) : z221 d = (m201 d) + -1048576 + (z220 d) := by
  simp only [z221, z202_linear] <;> ring

theorem z221_bounds (d : Digits) (hd : Bounded d) :
    (-2730282 : Int) ≤ z221 d ∧ z221 d ≤ 168656138 := by
  have h0 := m201_bounds d
  have h2 := z220_bounds d hd
  rw [z221_linear]
  omega

theorem m222_bounds (d : Digits) : 0 ≤ m222 d ∧ m222 d ≤ 2097151 := by
  rw [m222]
  omega

theorem z222_linear (d : Digits) : z222 d = (d 13) + (-683901) * (d 20) + (136657) * (d 21) + (-997805) * (d 22) + (654183) * (d 23) + (-1) * (m222 d) + 1048576 + (z191 d) := by
  simp only [z222, z219_linear] <;> ring

theorem z222_bounds (d : Digits) (hd : Bounded d) :
    (-3526794149886 : Int) ≤ z222 d ∧ z222 d ≤ 351498537867263 := by
  have h0 := hd 13
  norm_num at h0
  have h1 := hd 20
  norm_num at h1
  have h2 := hd 21
  norm_num at h2
  have h3 := hd 22
  norm_num at h3
  have h4 := hd 23
  norm_num at h4
  have h5 := m222_bounds d
  have h7 := z191_bounds d hd
  rw [z222_linear]
  omega

theorem z223_linear (d : Digits) : z223 d = (m222 d) + -1048576 := by
  simp only [z223, z195_linear, z222_linear] <;> ring

theorem z223_bounds (d : Digits) (hd : Bounded d) :
    (-1048576 : Int) ≤ z223 d ∧ z223 d ≤ 1048575 := by
  have h0 := m222_bounds d
  rw [z223_linear]
  omega

theorem z224_linear (d : Digits) : z224 d = (d 15) + (-683901) * (d 22) + (136657) * (d 23) + 1048576 + (z199 d) := by
  simp only [z224, z200_linear] <;> ring

theorem z224_bounds (d : Digits) (hd : Bounded d) :
    (-1434498739455 : Int) ≤ z224 d ∧ z224 d ≤ 73367171366912 := by
  have h0 := hd 15
  norm_num at h0
  have h1 := hd 22
  norm_num at h1
  have h2 := hd 23
  norm_num at h2
  have h4 := z199_bounds d hd
  rw [z224_linear]
  omega

theorem z225_bounds (d : Digits) (hd : Bounded d) :
    (-684023 : Int) ≤ z225 d ∧ z225 d ≤ 34984193 := by
  have h := z224_bounds d hd
  rw [z225]
  omega

theorem z226_linear (d : Digits) : z226 d = (m206 d) + -1048576 + (z225 d) := by
  simp only [z226, z207_linear] <;> ring

theorem z226_bounds (d : Digits) (hd : Bounded d) :
    (-1732599 : Int) ≤ z226 d ∧ z226 d ≤ 36032768 := by
  have h0 := m206_bounds d
  have h2 := z225_bounds d hd
  rw [z226_linear]
  omega

theorem m227_bounds (d : Digits) : 0 ≤ m227 d ∧ m227 d ≤ 2097151 := by
  rw [m227]
  omega

theorem z227_linear (d : Digits) : z227 d = (d 15) + (-683901) * (d 22) + (136657) * (d 23) + (-1) * (m227 d) + 1048576 + (z199 d) := by
  simp only [z227, z224_linear] <;> ring

theorem z227_bounds (d : Digits) (hd : Bounded d) :
    (-1434500836606 : Int) ≤ z227 d ∧ z227 d ≤ 73367171366912 := by
  have h0 := hd 15
  norm_num at h0
  have h1 := hd 22
  norm_num at h1
  have h2 := hd 23
  norm_num at h2
  have h3 := m227_bounds d
  have h5 := z199_bounds d hd
  rw [z227_linear]
  omega

theorem z228_linear (d : Digits) : z228 d = (m227 d) + -1048576 := by
  simp only [z228, z200_linear, z227_linear] <;> ring

theorem z228_bounds (d : Digits) (hd : Bounded d) :
    (-1048576 : Int) ≤ z228 d ∧ z228 d ≤ 1048575 := by
  have h0 := m227_bounds d
  rw [z228_linear]
  omega

end Firedancer.Common.ScalarArithmetic.IntegerRegisters
