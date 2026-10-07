import SSA.Projects.Firedancer.Common.Proof.Scalar.Arithmetic.IntegerBounds1

/-! Checked linear identities and interval certificates for the corresponding
numbered source arithmetic registers. Generated equations are verified by
`ring` and `omega`; no external arithmetic result is trusted. -/

namespace Firedancer.Common.ScalarArithmetic.IntegerRegisters

set_option maxHeartbeats 2000000

attribute [local irreducible] z61 z63 z65 z67 z69 z71 z73 z75 z77 z79 z81 z83 z85 z87 z89 z91 z93 z95 z97 z99 z101 z103 z105 z106 z107 z108 z109 z110 z111 z112 z113 z114 z115 z116 z117 z118 z119 z120 z121 z122 z123 z124 z125 z126 z127 z128 z129 z130 z131 z132 z133 z134 z135 z136 z137 z138 z139 z140 z141 z142 z143 z144 z145 z146 z147 z148 z149 z150 z151 z152 z153 z154 z155 z156 z157 z158 z159 z160 z161 z162 z163 z164 z165 z166 z167 z168 z169 z170 z171 z172 z173 z174 z175 z176 z177 z178 z179 z180 z181 z182 z183 z184 z185 z186 z187 z188 z189 z190 z191 z192 z193 z194 z195 z196 z197 z198 z199 z200 z201 z202 z203 z204 z205 z206 z207 z208 z209 z210 z211 z212 z213 z214 z215 z216 z217 z218 z219 z220 z221 z222 z223 z224 z225 z226 z227 z228 z229 z230 z231 z232 z233 z234 z235 z236 z237 z238 z239 z240 z241 z242 z243 z244 z245 z246 z247 z248 z249 z250 z251 z252 z253 z254 z255 z256 z257 z258 z259 z260 z261 z262 z263 z264 z265 z266 z267 z268 z269 z270 z271 z272 z273 z274 z275 z276 z277 z278 z279 z280 z281 z282 z283 z284 z285 z286 z287 z288 z289 z290 z291 z292 z293 z294 z295 z296 z297 z298 z299 z300 z301 z302 z303 z304 z305 z306 z307 z308 z309 z310 z311 z312 z313 z314 z315 z316 z317 z318 z319 z320 z321 z322 z323 z324 z325 z326 z327 z328 z329 z330 z331 z332 z333 z334 z335 z336 z337 z338 z339 z340 z341 z342 z343 z344 z345 z346 z347 z348 z349 z350 z351 z352 z353 z354 z355 z356 z357 z358 z359 z360 z361 z362 z363 z364 z365 z366 z367 z368 z369 z370 z371 z372 z373 z374 z375 z376 z377 z378 z379 z380 z381 z382 z383 z384 z385 z386 z387 z388 z389 z390 z391 z392 z393 z394 z395 z396 z397 z398 z399 z400 z401 z402 z403 z404 z405 z406 z407 z408 z409 z410 z411 z412 z413 z414 z415 z416 z417 z418 z419 z420 z421 z422 z423 z424 z425 z426 z427 z428 z429 z430 z431 z432 z433 z434 z435 z436 z437 z438 z439 z440 z441 z442 z443 z444 z445 z446 m170 m179 m189 m196 m201 m206 m210 m213 m217 m222 m227 m301 m306 m311 m321 m329 m334 m338 m341 m345 m349 m354 m358

theorem z229_linear (d : Digits) : z229 d = (666643) * (d 17) + (666643) * (z204 d) := by
  simp only [z229, z205_linear] <;> ring

theorem z229_bounds (d : Digits) (hd : Bounded d) :
    (-116714960471808 : Int) ≤ z229 d ∧ z229 d ≤ 1398051700736 := by
  have h0 := hd 17
  norm_num at h0
  have h1 := z204_bounds d hd
  rw [z229_linear]
  omega

theorem z230_linear (d : Digits) : z230 d = (666643) * (d 17) + (d 5) + (666643) * (z204 d) := by
  simp only [z230, z229_linear, z71_linear] <;> ring

theorem z230_bounds (d : Digits) (hd : Bounded d) :
    (-116714960471808 : Int) ≤ z230 d ∧ z230 d ≤ 1398053797887 := by
  have h0 := hd 17
  norm_num at h0
  have h1 := hd 5
  norm_num at h1
  have h2 := z204_bounds d hd
  rw [z230_linear]
  omega

theorem z231_linear (d : Digits) : z231 d = (470296) * (d 17) + (470296) * (z204 d) := by
  simp only [z231, z205_linear] <;> ring

theorem z231_bounds (d : Digits) (hd : Bounded d) :
    (-82338791602176 : Int) ≤ z231 d ∧ z231 d ≤ 986282196992 := by
  have h0 := hd 17
  norm_num at h0
  have h1 := z204_bounds d hd
  rw [z231_linear]
  omega

theorem z232_linear (d : Digits) : z232 d = (470296) * (d 17) + (m170 d) + -1048576 + (470296) * (z204 d) := by
  simp only [z232, z171_linear, z231_linear] <;> ring

theorem z232_bounds (d : Digits) (hd : Bounded d) :
    (-82338792650752 : Int) ≤ z232 d ∧ z232 d ≤ 986283245567 := by
  have h0 := hd 17
  norm_num at h0
  have h1 := m170_bounds d
  have h3 := z204_bounds d hd
  rw [z232_linear]
  omega

theorem z233_linear (d : Digits) : z233 d = (654183) * (d 17) + (654183) * (z204 d) := by
  simp only [z233, z205_linear] <;> ring

theorem z233_bounds (d : Digits) (hd : Bounded d) :
    (-114533480418048 : Int) ≤ z233 d ∧ z233 d ≤ 1371921186816 := by
  have h0 := hd 17
  norm_num at h0
  have h1 := z204_bounds d hd
  rw [z233_linear]
  omega

theorem z234_linear (d : Digits) : z234 d = (-997805) * (d 17) + (-997805) * (z204 d) := by
  simp only [z234, z205_linear] <;> ring

theorem z234_bounds (d : Digits) (hd : Bounded d) :
    (-2092548751360 : Int) ≤ z234 d ∧ z234 d ≤ 174694358350080 := by
  have h0 := hd 17
  norm_num at h0
  have h1 := z204_bounds d hd
  rw [z234_linear]
  omega

theorem z235_linear (d : Digits) : z235 d = (136657) * (d 17) + (136657) * (z204 d) := by
  simp only [z235, z205_linear] <;> ring

theorem z235_bounds (d : Digits) (hd : Bounded d) :
    (-23925723892992 : Int) ≤ z235 d ∧ z235 d ≤ 286590500864 := by
  have h0 := hd 17
  norm_num at h0
  have h1 := z204_bounds d hd
  rw [z235_linear]
  omega

theorem z236_linear (d : Digits) : z236 d = (-683901) * (d 17) + (-683901) * (z204 d) := by
  simp only [z236, z205_linear] <;> ring

theorem z236_bounds (d : Digits) (hd : Bounded d) :
    (-1434244349952 : Int) ≤ z236 d ∧ z236 d ≤ 119736467917056 := by
  have h0 := hd 17
  norm_num at h0
  have h1 := z204_bounds d hd
  rw [z236_linear]
  omega

theorem z237_linear (d : Digits) : z237 d = (d 10) + (-683901) * (d 17) + (136657) * (d 18) + (-997805) * (d 19) + (654183) * (d 20) + (470296) * (d 21) + (666643) * (d 22) + (-683901) * (z204 d) := by
  simp only [z237, z165_linear, z236_linear] <;> ring

theorem z237_bounds (d : Digits) (hd : Bounded d) :
    (-3526792103507 : Int) ≤ z237 d ∧ z237 d ≤ 123779313671836 := by
  have h0 := hd 10
  norm_num at h0
  have h1 := hd 17
  norm_num at h1
  have h2 := hd 18
  norm_num at h2
  have h3 := hd 19
  norm_num at h3
  have h4 := hd 20
  norm_num at h4
  have h5 := hd 21
  norm_num at h5
  have h6 := hd 22
  norm_num at h6
  have h7 := z204_bounds d hd
  rw [z237_linear]
  omega

theorem z238_linear (d : Digits) : z238 d = (-683901) * (d 17) + (m189 d) + -1048576 + (-683901) * (z204 d) := by
  simp only [z238, z237_linear, z189_linear] <;> ring

theorem z238_bounds (d : Digits) (hd : Bounded d) :
    (-1434245398528 : Int) ≤ z238 d ∧ z238 d ≤ 119736468965631 := by
  have h0 := hd 17
  norm_num at h0
  have h1 := m189_bounds d
  have h3 := z204_bounds d hd
  rw [z238_linear]
  omega

theorem z239_linear (d : Digits) : z239 d = (-683901) * (d 17) + (m189 d) + -1048576 + (-683901) * (z204 d) + (z212 d) := by
  simp only [z239, z238_linear] <;> ring

theorem z239_bounds (d : Digits) (hd : Bounded d) :
    (-1434246396333 : Int) ≤ z239 d ∧ z239 d ≤ 119736470756754 := by
  have h0 := hd 17
  norm_num at h0
  have h1 := m189_bounds d
  have h3 := z204_bounds d hd
  have h4 := z212_bounds d hd
  rw [z239_linear]
  omega

theorem z240_linear (d : Digits) : z240 d = (666643) * (m206 d) + -699025850368 + (666643) * (z225 d) := by
  simp only [z240, z226_linear] <;> ring

theorem z240_bounds (d : Digits) (hd : Bounded d) :
    (-1155024995157 : Int) ≤ z240 d ∧ z240 d ≤ 24020992557824 := by
  have h0 := m206_bounds d
  have h2 := z225_bounds d hd
  rw [z240_linear]
  omega

theorem z241_linear (d : Digits) : z241 d = (d 4) + (666643) * (m206 d) + -699025850368 + (666643) * (z225 d) := by
  simp only [z241, z240_linear, z69_linear] <;> ring

theorem z241_bounds (d : Digits) (hd : Bounded d) :
    (-1155024995157 : Int) ≤ z241 d ∧ z241 d ≤ 24020994654975 := by
  have h0 := hd 4
  norm_num at h0
  have h1 := m206_bounds d
  have h3 := z225_bounds d hd
  rw [z241_linear]
  omega

theorem z242_linear (d : Digits) : z242 d = (470296) * (m206 d) + -493141098496 + (470296) * (z225 d) := by
  simp only [z242, z226_linear] <;> ring

theorem z242_bounds (d : Digits) (hd : Bounded d) :
    (-814834379304 : Int) ≤ z242 d ∧ z242 d ≤ 16946066659328 := by
  have h0 := m206_bounds d
  have h2 := z225_bounds d hd
  rw [z242_linear]
  omega

theorem z243_linear (d : Digits) : z243 d = (666643) * (d 17) + (d 5) + (470296) * (m206 d) + -493141098496 + (666643) * (z204 d) + (470296) * (z225 d) := by
  simp only [z243, z230_linear, z242_linear] <;> ring

theorem z243_bounds (d : Digits) (hd : Bounded d) :
    (-117529794851112 : Int) ≤ z243 d ∧ z243 d ≤ 18344120457215 := by
  have h0 := hd 17
  norm_num at h0
  have h1 := hd 5
  norm_num at h1
  have h2 := m206_bounds d
  have h4 := z204_bounds d hd
  have h5 := z225_bounds d hd
  rw [z243_linear]
  omega

theorem z244_linear (d : Digits) : z244 d = (654183) * (m206 d) + -685960593408 + (654183) * (z225 d) := by
  simp only [z244, z226_linear] <;> ring

theorem z244_bounds (d : Digits) (hd : Bounded d) :
    (-1133436811617 : Int) ≤ z244 d ∧ z244 d ≤ 23572024268544 := by
  have h0 := m206_bounds d
  have h2 := z225_bounds d hd
  rw [z244_linear]
  omega

theorem z245_linear (d : Digits) : z245 d = (470296) * (d 17) + (m170 d) + (654183) * (m206 d) + -685961641984 + (470296) * (z204 d) + (654183) * (z225 d) := by
  simp only [z245, z232_linear, z244_linear] <;> ring

theorem z245_bounds (d : Digits) (hd : Bounded d) :
    (-83472229462369 : Int) ≤ z245 d ∧ z245 d ≤ 24558307514111 := by
  have h0 := hd 17
  norm_num at h0
  have h1 := m170_bounds d
  have h2 := m206_bounds d
  have h4 := z204_bounds d hd
  have h5 := z225_bounds d hd
  rw [z245_linear]
  omega

theorem z246_linear (d : Digits) : z246 d = (-997805) * (m206 d) + 1046274375680 + (-997805) * (z225 d) := by
  simp only [z246, z226_linear] <;> ring

theorem z246_bounds (d : Digits) (hd : Bounded d) :
    (-35953676074240 : Int) ≤ z246 d ∧ z246 d ≤ 1728795945195 := by
  have h0 := m206_bounds d
  have h2 := z225_bounds d hd
  rw [z246_linear]
  omega

theorem z247_linear (d : Digits) : z247 d = (136657) * (m206 d) + -143295250432 + (136657) * (z225 d) := by
  simp only [z247, z226_linear] <;> ring

theorem z247_bounds (d : Digits) (hd : Bounded d) :
    (-236771781543 : Int) ≤ z247 d ∧ z247 d ≤ 4924129976576 := by
  have h0 := m206_bounds d
  have h2 := z225_bounds d hd
  rw [z247_linear]
  omega

theorem z248_linear (d : Digits) : z248 d = (-683901) * (m206 d) + 717122174976 + (-683901) * (z225 d) := by
  simp only [z248, z226_linear] <;> ring

theorem z248_bounds (d : Digits) (hd : Bounded d) :
    (-24642846067968 : Int) ≤ z248 d ∧ z248 d ≤ 1184926188699 := by
  have h0 := m206_bounds d
  have h2 := z225_bounds d hd
  rw [z248_linear]
  omega

theorem z249_linear (d : Digits) : z249 d = (666643) * (m227 d) + -699025850368 := by
  simp only [z249, z228_linear] <;> ring

theorem z249_bounds (d : Digits) (hd : Bounded d) :
    (-699025850368 : Int) ≤ z249 d ∧ z249 d ≤ 699025183725 := by
  have h0 := m227_bounds d
  rw [z249_linear]
  omega

theorem z250_linear (d : Digits) : z250 d = (d 3) + (666643) * (m227 d) + -699025850368 := by
  simp only [z250, z249_linear, z67_linear] <;> ring

theorem z250_bounds (d : Digits) (hd : Bounded d) :
    (-699025850368 : Int) ≤ z250 d ∧ z250 d ≤ 699027280876 := by
  have h0 := hd 3
  norm_num at h0
  have h1 := m227_bounds d
  rw [z250_linear]
  omega

theorem z251_linear (d : Digits) : z251 d = (470296) * (m227 d) + -493141098496 := by
  simp only [z251, z228_linear] <;> ring

theorem z251_bounds (d : Digits) (hd : Bounded d) :
    (-493141098496 : Int) ≤ z251 d ∧ z251 d ≤ 493140628200 := by
  have h0 := m227_bounds d
  rw [z251_linear]
  omega

theorem z252_linear (d : Digits) : z252 d = (d 4) + (666643) * (m206 d) + (470296) * (m227 d) + -1192166948864 + (666643) * (z225 d) := by
  simp only [z252, z241_linear, z251_linear] <;> ring

theorem z252_bounds (d : Digits) (hd : Bounded d) :
    (-1648166093653 : Int) ≤ z252 d ∧ z252 d ≤ 24514135283175 := by
  have h0 := hd 4
  norm_num at h0
  have h1 := m206_bounds d
  have h2 := m227_bounds d
  have h4 := z225_bounds d hd
  rw [z252_linear]
  omega

theorem z253_linear (d : Digits) : z253 d = (654183) * (m227 d) + -685960593408 := by
  simp only [z253, z228_linear] <;> ring

theorem z253_bounds (d : Digits) (hd : Bounded d) :
    (-685960593408 : Int) ≤ z253 d ∧ z253 d ≤ 685959939225 := by
  have h0 := m227_bounds d
  rw [z253_linear]
  omega

theorem z254_linear (d : Digits) : z254 d = (666643) * (d 17) + (d 5) + (470296) * (m206 d) + (654183) * (m227 d) + -1179101691904 + (666643) * (z204 d) + (470296) * (z225 d) := by
  simp only [z254, z243_linear, z253_linear] <;> ring

theorem z254_bounds (d : Digits) (hd : Bounded d) :
    (-118215755444520 : Int) ≤ z254 d ∧ z254 d ≤ 19030080396440 := by
  have h0 := hd 17
  norm_num at h0
  have h1 := hd 5
  norm_num at h1
  have h2 := m206_bounds d
  have h3 := m227_bounds d
  have h5 := z204_bounds d hd
  have h6 := z225_bounds d hd
  rw [z254_linear]
  omega

theorem z255_linear (d : Digits) : z255 d = (-997805) * (m227 d) + 1046274375680 := by
  simp only [z255, z228_linear] <;> ring

theorem z255_bounds (d : Digits) (hd : Bounded d) :
    (-1046273377875 : Int) ≤ z255 d ∧ z255 d ≤ 1046274375680 := by
  have h0 := m227_bounds d
  rw [z255_linear]
  omega

theorem z256_linear (d : Digits) : z256 d = (470296) * (d 17) + (m170 d) + (654183) * (m206 d) + (-997805) * (m227 d) + 360312733696 + (470296) * (z204 d) + (654183) * (z225 d) := by
  simp only [z256, z245_linear, z255_linear] <;> ring

theorem z256_bounds (d : Digits) (hd : Bounded d) :
    (-84518502840244 : Int) ≤ z256 d ∧ z256 d ≤ 25604581889791 := by
  have h0 := hd 17
  norm_num at h0
  have h1 := m170_bounds d
  have h2 := m206_bounds d
  have h3 := m227_bounds d
  have h5 := z204_bounds d hd
  have h6 := z225_bounds d hd
  rw [z256_linear]
  omega

theorem z257_linear (d : Digits) : z257 d = (136657) * (m227 d) + -143295250432 := by
  simp only [z257, z228_linear] <;> ring

theorem z257_bounds (d : Digits) (hd : Bounded d) :
    (-143295250432 : Int) ≤ z257 d ∧ z257 d ≤ 143295113775 := by
  have h0 := m227_bounds d
  rw [z257_linear]
  omega

theorem z258_linear (d : Digits) : z258 d = (-683901) * (m227 d) + 717122174976 := by
  simp only [z258, z228_linear] <;> ring

theorem z258_bounds (d : Digits) (hd : Bounded d) :
    (-717121491075 : Int) ≤ z258 d ∧ z258 d ≤ 717122174976 := by
  have h0 := m227_bounds d
  rw [z258_linear]
  omega

theorem z259_linear (d : Digits) : z259 d = (-997805) * (d 17) + (m179 d) + -1048576 + (-997805) * (z204 d) := by
  simp only [z259, z180_linear, z234_linear] <;> ring

theorem z259_bounds (d : Digits) (hd : Bounded d) :
    (-2092549799936 : Int) ≤ z259 d ∧ z259 d ≤ 174694359398655 := by
  have h0 := hd 17
  norm_num at h0
  have h1 := m179_bounds d
  have h3 := z204_bounds d hd
  rw [z259_linear]
  omega

theorem z260_linear (d : Digits) : z260 d = (-997805) * (d 17) + (m179 d) + -1048576 + (-997805) * (z204 d) + (z209 d) := by
  simp only [z260, z259_linear] <;> ring

theorem z260_bounds (d : Digits) (hd : Bounded d) :
    (-2092549799936 : Int) ≤ z260 d ∧ z260 d ≤ 174694360535595 := by
  have h0 := hd 17
  norm_num at h0
  have h1 := m179_bounds d
  have h3 := z204_bounds d hd
  have h4 := z209_bounds d hd
  rw [z260_linear]
  omega

theorem z261_linear (d : Digits) : z261 d = (-997805) * (d 17) + (m179 d) + (136657) * (m206 d) + -143296299008 + (-997805) * (z204 d) + (z209 d) + (136657) * (z225 d) := by
  simp only [z261, z260_linear, z247_linear] <;> ring

theorem z261_bounds (d : Digits) (hd : Bounded d) :
    (-2329321581479 : Int) ≤ z261 d ∧ z261 d ≤ 179618490512171 := by
  have h0 := hd 17
  norm_num at h0
  have h1 := m179_bounds d
  have h2 := m206_bounds d
  have h4 := z204_bounds d hd
  have h5 := z209_bounds d hd
  have h6 := z225_bounds d hd
  rw [z261_linear]
  omega

theorem z262_linear (d : Digits) : z262 d = (-997805) * (d 17) + (m179 d) + (136657) * (m206 d) + (-683901) * (m227 d) + 573825875968 + (-997805) * (z204 d) + (z209 d) + (136657) * (z225 d) := by
  simp only [z262, z261_linear, z258_linear] <;> ring

theorem z262_bounds (d : Digits) (hd : Bounded d) :
    (-3046443072554 : Int) ≤ z262 d ∧ z262 d ≤ 180335612687147 := by
  have h0 := hd 17
  norm_num at h0
  have h1 := m179_bounds d
  have h2 := m206_bounds d
  have h3 := m227_bounds d
  have h5 := z204_bounds d hd
  have h6 := z209_bounds d hd
  have h7 := z225_bounds d hd
  rw [z262_linear]
  omega

theorem z263_linear (d : Digits) : z263 d = (666643) * (m201 d) + -699025850368 + (666643) * (z220 d) := by
  simp only [z263, z221_linear] <;> ring

theorem z263_bounds (d : Digits) (hd : Bounded d) :
    (-1820123383326 : Int) ≤ z263 d ∧ z263 d ≤ 112433433804734 := by
  have h0 := m201_bounds d
  have h2 := z220_bounds d hd
  rw [z263_linear]
  omega

theorem z264_linear (d : Digits) : z264 d = (d 2) + (666643) * (m201 d) + -699025850368 + (666643) * (z220 d) := by
  simp only [z264, z263_linear, z65_linear] <;> ring

theorem z264_bounds (d : Digits) (hd : Bounded d) :
    (-1820123383326 : Int) ≤ z264 d ∧ z264 d ≤ 112433435901885 := by
  have h0 := hd 2
  norm_num at h0
  have h1 := m201_bounds d
  have h3 := z220_bounds d hd
  rw [z264_linear]
  omega

theorem z265_linear (d : Digits) : z265 d = (470296) * (m201 d) + -493141098496 + (470296) * (z220 d) := by
  simp only [z265, z221_linear] <;> ring

theorem z265_bounds (d : Digits) (hd : Bounded d) :
    (-1284040703472 : Int) ≤ z265 d ∧ z265 d ≤ 79318307076848 := by
  have h0 := m201_bounds d
  have h2 := z220_bounds d hd
  rw [z265_linear]
  omega

theorem z266_linear (d : Digits) : z266 d = (d 3) + (470296) * (m201 d) + (666643) * (m227 d) + -1192166948864 + (470296) * (z220 d) := by
  simp only [z266, z250_linear, z265_linear] <;> ring

theorem z266_bounds (d : Digits) (hd : Bounded d) :
    (-1983066553840 : Int) ≤ z266 d ∧ z266 d ≤ 80017334357724 := by
  have h0 := hd 3
  norm_num at h0
  have h1 := m201_bounds d
  have h2 := m227_bounds d
  have h4 := z220_bounds d hd
  rw [z266_linear]
  omega

theorem z267_linear (d : Digits) : z267 d = (654183) * (m201 d) + -685960593408 + (654183) * (z220 d) := by
  simp only [z267, z221_linear] <;> ring

theorem z267_bounds (d : Digits) (hd : Bounded d) :
    (-1786104069606 : Int) ≤ z267 d ∧ z267 d ≤ 110331978325254 := by
  have h0 := m201_bounds d
  have h2 := z220_bounds d hd
  rw [z267_linear]
  omega

theorem z268_linear (d : Digits) : z268 d = (d 4) + (654183) * (m201 d) + (666643) * (m206 d) + (470296) * (m227 d) + -1878127542272 + (654183) * (z220 d) + (666643) * (z225 d) := by
  simp only [z268, z252_linear, z267_linear] <;> ring

theorem z268_bounds (d : Digits) (hd : Bounded d) :
    (-3434270163259 : Int) ≤ z268 d ∧ z268 d ≤ 134846113608429 := by
  have h0 := hd 4
  norm_num at h0
  have h1 := m201_bounds d
  have h2 := m206_bounds d
  have h3 := m227_bounds d
  have h5 := z220_bounds d hd
  have h6 := z225_bounds d hd
  rw [z268_linear]
  omega

theorem z269_linear (d : Digits) : z269 d = (-997805) * (m201 d) + 1046274375680 + (-997805) * (z220 d) := by
  simp only [z269, z221_linear] <;> ring

theorem z269_bounds (d : Digits) (hd : Bounded d) :
    (-168285937777090 : Int) ≤ z269 d ∧ z269 d ≤ 2724289031010 := by
  have h0 := m201_bounds d
  have h2 := z220_bounds d hd
  rw [z269_linear]
  omega

theorem z270_linear (d : Digits) : z270 d = (666643) * (d 17) + (d 5) + (-997805) * (m201 d) + (470296) * (m206 d) + (654183) * (m227 d) + -132827316224 + (666643) * (z204 d) + (-997805) * (z220 d) + (470296) * (z225 d) := by
  simp only [z270, z254_linear, z269_linear] <;> ring

theorem z270_bounds (d : Digits) (hd : Bounded d) :
    (-286501693221610 : Int) ≤ z270 d ∧ z270 d ≤ 21754369427450 := by
  have h0 := hd 17
  norm_num at h0
  have h1 := hd 5
  norm_num at h1
  have h2 := m201_bounds d
  have h3 := m206_bounds d
  have h4 := m227_bounds d
  have h6 := z204_bounds d hd
  have h7 := z220_bounds d hd
  have h8 := z225_bounds d hd
  rw [z270_linear]
  omega

theorem z271_linear (d : Digits) : z271 d = (136657) * (m201 d) + -143295250432 + (136657) * (z220 d) := by
  simp only [z271, z221_linear] <;> ring

theorem z271_bounds (d : Digits) (hd : Bounded d) :
    (-373112147274 : Int) ≤ z271 d ∧ z271 d ≤ 23048041850666 := by
  have h0 := m201_bounds d
  have h2 := z220_bounds d hd
  rw [z271_linear]
  omega

theorem z272_linear (d : Digits) : z272 d = (470296) * (d 17) + (m170 d) + (136657) * (m201 d) + (654183) * (m206 d) + (-997805) * (m227 d) + 217017483264 + (470296) * (z204 d) + (136657) * (z220 d) + (654183) * (z225 d) := by
  simp only [z272, z256_linear, z271_linear] <;> ring

theorem z272_bounds (d : Digits) (hd : Bounded d) :
    (-84891614987518 : Int) ≤ z272 d ∧ z272 d ≤ 48652623740457 := by
  have h0 := hd 17
  norm_num at h0
  have h1 := m170_bounds d
  have h2 := m201_bounds d
  have h3 := m206_bounds d
  have h4 := m227_bounds d
  have h6 := z204_bounds d hd
  have h7 := z220_bounds d hd
  have h8 := z225_bounds d hd
  rw [z272_linear]
  omega

theorem z273_linear (d : Digits) : z273 d = (-683901) * (m201 d) + 717122174976 + (-683901) * (z220 d) := by
  simp only [z273, z221_linear] <;> ring

theorem z273_bounds (d : Digits) (hd : Bounded d) :
    (-115344101434338 : Int) ≤ z273 d ∧ z273 d ≤ 1867242590082 := by
  have h0 := m201_bounds d
  have h2 := z220_bounds d hd
  rw [z273_linear]
  omega

theorem z274_linear (d : Digits) : z274 d = (666643) * (m222 d) + -699025850368 := by
  simp only [z274, z223_linear] <;> ring

theorem z274_bounds (d : Digits) (hd : Bounded d) :
    (-699025850368 : Int) ≤ z274 d ∧ z274 d ≤ 699025183725 := by
  have h0 := m222_bounds d
  rw [z274_linear]
  omega

theorem z275_linear (d : Digits) : z275 d = (d 1) + (666643) * (m222 d) + -699025850368 := by
  simp only [z275, z274_linear, z63_linear] <;> ring

theorem z275_bounds (d : Digits) (hd : Bounded d) :
    (-699025850368 : Int) ≤ z275 d ∧ z275 d ≤ 699027280876 := by
  have h0 := hd 1
  norm_num at h0
  have h1 := m222_bounds d
  rw [z275_linear]
  omega

theorem z276_linear (d : Digits) : z276 d = (470296) * (m222 d) + -493141098496 := by
  simp only [z276, z223_linear] <;> ring

theorem z276_bounds (d : Digits) (hd : Bounded d) :
    (-493141098496 : Int) ≤ z276 d ∧ z276 d ≤ 493140628200 := by
  have h0 := m222_bounds d
  rw [z276_linear]
  omega

theorem z277_linear (d : Digits) : z277 d = (d 2) + (666643) * (m201 d) + (470296) * (m222 d) + -1192166948864 + (666643) * (z220 d) := by
  simp only [z277, z264_linear, z276_linear] <;> ring

theorem z277_bounds (d : Digits) (hd : Bounded d) :
    (-2313264481822 : Int) ≤ z277 d ∧ z277 d ≤ 112926576530085 := by
  have h0 := hd 2
  norm_num at h0
  have h1 := m201_bounds d
  have h2 := m222_bounds d
  have h4 := z220_bounds d hd
  rw [z277_linear]
  omega

theorem z278_linear (d : Digits) : z278 d = (654183) * (m222 d) + -685960593408 := by
  simp only [z278, z223_linear] <;> ring

theorem z278_bounds (d : Digits) (hd : Bounded d) :
    (-685960593408 : Int) ≤ z278 d ∧ z278 d ≤ 685959939225 := by
  have h0 := m222_bounds d
  rw [z278_linear]
  omega

theorem z279_linear (d : Digits) : z279 d = (d 3) + (470296) * (m201 d) + (654183) * (m222 d) + (666643) * (m227 d) + -1878127542272 + (470296) * (z220 d) := by
  simp only [z279, z266_linear, z278_linear] <;> ring

theorem z279_bounds (d : Digits) (hd : Bounded d) :
    (-2669027147248 : Int) ≤ z279 d ∧ z279 d ≤ 80703294296949 := by
  have h0 := hd 3
  norm_num at h0
  have h1 := m201_bounds d
  have h2 := m222_bounds d
  have h3 := m227_bounds d
  have h5 := z220_bounds d hd
  rw [z279_linear]
  omega

theorem z280_linear (d : Digits) : z280 d = (-997805) * (m222 d) + 1046274375680 := by
  simp only [z280, z223_linear] <;> ring

theorem z280_bounds (d : Digits) (hd : Bounded d) :
    (-1046273377875 : Int) ≤ z280 d ∧ z280 d ≤ 1046274375680 := by
  have h0 := m222_bounds d
  rw [z280_linear]
  omega

theorem z281_linear (d : Digits) : z281 d = (d 4) + (654183) * (m201 d) + (666643) * (m206 d) + (-997805) * (m222 d) + (470296) * (m227 d) + -831853166592 + (654183) * (z220 d) + (666643) * (z225 d) := by
  simp only [z281, z268_linear, z280_linear] <;> ring

theorem z281_bounds (d : Digits) (hd : Bounded d) :
    (-4480543541134 : Int) ≤ z281 d ∧ z281 d ≤ 135892387984109 := by
  have h0 := hd 4
  norm_num at h0
  have h1 := m201_bounds d
  have h2 := m206_bounds d
  have h3 := m222_bounds d
  have h4 := m227_bounds d
  have h6 := z220_bounds d hd
  have h7 := z225_bounds d hd
  rw [z281_linear]
  omega

theorem z282_linear (d : Digits) : z282 d = (136657) * (m222 d) + -143295250432 := by
  simp only [z282, z223_linear] <;> ring

theorem z282_bounds (d : Digits) (hd : Bounded d) :
    (-143295250432 : Int) ≤ z282 d ∧ z282 d ≤ 143295113775 := by
  have h0 := m222_bounds d
  rw [z282_linear]
  omega

theorem z283_linear (d : Digits) : z283 d = (666643) * (d 17) + (d 5) + (-997805) * (m201 d) + (470296) * (m206 d) + (136657) * (m222 d) + (654183) * (m227 d) + -276122566656 + (666643) * (z204 d) + (-997805) * (z220 d) + (470296) * (z225 d) := by
  simp only [z283, z270_linear, z282_linear] <;> ring

theorem z283_bounds (d : Digits) (hd : Bounded d) :
    (-286644988472042 : Int) ≤ z283 d ∧ z283 d ≤ 21897664541225 := by
  have h0 := hd 17
  norm_num at h0
  have h1 := hd 5
  norm_num at h1
  have h2 := m201_bounds d
  have h3 := m206_bounds d
  have h4 := m222_bounds d
  have h5 := m227_bounds d
  have h7 := z204_bounds d hd
  have h8 := z220_bounds d hd
  have h9 := z225_bounds d hd
  rw [z283_linear]
  omega

theorem z284_linear (d : Digits) : z284 d = (-683901) * (m222 d) + 717122174976 := by
  simp only [z284, z223_linear] <;> ring

theorem z284_bounds (d : Digits) (hd : Bounded d) :
    (-717121491075 : Int) ≤ z284 d ∧ z284 d ≤ 717122174976 := by
  have h0 := m222_bounds d
  rw [z284_linear]
  omega

theorem z285_linear (d : Digits) : z285 d = (470296) * (d 17) + (m170 d) + (136657) * (m201 d) + (654183) * (m206 d) + (-683901) * (m222 d) + (-997805) * (m227 d) + 934139658240 + (470296) * (z204 d) + (136657) * (z220 d) + (654183) * (z225 d) := by
  simp only [z285, z272_linear, z284_linear] <;> ring

theorem z285_bounds (d : Digits) (hd : Bounded d) :
    (-85608736478593 : Int) ≤ z285 d ∧ z285 d ≤ 49369745915433 := by
  have h0 := hd 17
  norm_num at h0
  have h1 := m170_bounds d
  have h2 := m201_bounds d
  have h3 := m206_bounds d
  have h4 := m222_bounds d
  have h5 := m227_bounds d
  have h7 := z204_bounds d hd
  have h8 := z220_bounds d hd
  have h9 := z225_bounds d hd
  rw [z285_linear]
  omega

theorem z286_linear (d : Digits) : z286 d = (666643) * (m196 d) + -699025850368 + (666643) * (z215 d) := by
  simp only [z286, z216_linear] <;> ring

theorem z286_bounds (d : Digits) (hd : Bounded d) :
    (-1820123383326 : Int) ≤ z286 d ∧ z286 d ≤ 115309453035760 := by
  have h0 := m196_bounds d
  have h2 := z215_bounds d hd
  rw [z286_linear]
  omega

theorem z287_linear (d : Digits) : z287 d = (d 0) + (666643) * (m196 d) + -699025850368 + (666643) * (z215 d) := by
  simp only [z287, z286_linear, z61_linear] <;> ring

theorem z287_bounds (d : Digits) (hd : Bounded d) :
    (-1820123383326 : Int) ≤ z287 d ∧ z287 d ≤ 115309455132911 := by
  have h0 := hd 0
  norm_num at h0
  have h1 := m196_bounds d
  have h3 := z215_bounds d hd
  rw [z287_linear]
  omega

theorem z288_linear (d : Digits) : z288 d = (470296) * (m196 d) + -493141098496 + (470296) * (z215 d) := by
  simp only [z288, z216_linear] <;> ring

theorem z288_bounds (d : Digits) (hd : Bounded d) :
    (-1284040703472 : Int) ≤ z288 d ∧ z288 d ≤ 81347249614720 := by
  have h0 := m196_bounds d
  have h2 := z215_bounds d hd
  rw [z288_linear]
  omega

theorem z289_linear (d : Digits) : z289 d = (d 1) + (470296) * (m196 d) + (666643) * (m222 d) + -1192166948864 + (470296) * (z215 d) := by
  simp only [z289, z275_linear, z288_linear] <;> ring

theorem z289_bounds (d : Digits) (hd : Bounded d) :
    (-1983066553840 : Int) ≤ z289 d ∧ z289 d ≤ 82046276895596 := by
  have h0 := hd 1
  norm_num at h0
  have h1 := m196_bounds d
  have h2 := m222_bounds d
  have h4 := z215_bounds d hd
  rw [z289_linear]
  omega

theorem z290_linear (d : Digits) : z290 d = (654183) * (m196 d) + -685960593408 + (654183) * (z215 d) := by
  simp only [z290, z216_linear] <;> ring

theorem z290_bounds (d : Digits) (hd : Bounded d) :
    (-1786104069606 : Int) ≤ z290 d ∧ z290 d ≤ 113154242848560 := by
  have h0 := m196_bounds d
  have h2 := z215_bounds d hd
  rw [z290_linear]
  omega

theorem z291_linear (d : Digits) : z291 d = (d 2) + (654183) * (m196 d) + (666643) * (m201 d) + (470296) * (m222 d) + -1878127542272 + (654183) * (z215 d) + (666643) * (z220 d) := by
  simp only [z291, z277_linear, z290_linear] <;> ring

theorem z291_bounds (d : Digits) (hd : Bounded d) :
    (-4099368551428 : Int) ≤ z291 d ∧ z291 d ≤ 226080819378645 := by
  have h0 := hd 2
  norm_num at h0
  have h1 := m196_bounds d
  have h2 := m201_bounds d
  have h3 := m222_bounds d
  have h5 := z215_bounds d hd
  have h6 := z220_bounds d hd
  rw [z291_linear]
  omega

theorem z292_linear (d : Digits) : z292 d = (-997805) * (m196 d) + 1046274375680 + (-997805) * (z215 d) := by
  simp only [z292, z216_linear] <;> ring

theorem z292_bounds (d : Digits) (hd : Bounded d) :
    (-172590650147600 : Int) ≤ z292 d ∧ z292 d ≤ 2724289031010 := by
  have h0 := m196_bounds d
  have h2 := z215_bounds d hd
  rw [z292_linear]
  omega

theorem z293_linear (d : Digits) : z293 d = (d 3) + (-997805) * (m196 d) + (470296) * (m201 d) + (654183) * (m222 d) + (666643) * (m227 d) + -831853166592 + (-997805) * (z215 d) + (470296) * (z220 d) := by
  simp only [z293, z279_linear, z292_linear] <;> ring

theorem z293_bounds (d : Digits) (hd : Bounded d) :
    (-175259677294848 : Int) ≤ z293 d ∧ z293 d ≤ 83427583327959 := by
  have h0 := hd 3
  norm_num at h0
  have h1 := m196_bounds d
  have h2 := m201_bounds d
  have h3 := m222_bounds d
  have h4 := m227_bounds d
  have h6 := z215_bounds d hd
  have h7 := z220_bounds d hd
  rw [z293_linear]
  omega

theorem z294_linear (d : Digits) : z294 d = (136657) * (m196 d) + -143295250432 + (136657) * (z215 d) := by
  simp only [z294, z216_linear] <;> ring

theorem z294_bounds (d : Digits) (hd : Bounded d) :
    (-373112147274 : Int) ≤ z294 d ∧ z294 d ≤ 23637605020240 := by
  have h0 := m196_bounds d
  have h2 := z215_bounds d hd
  rw [z294_linear]
  omega

theorem z295_linear (d : Digits) : z295 d = (d 4) + (136657) * (m196 d) + (654183) * (m201 d) + (666643) * (m206 d) + (-997805) * (m222 d) + (470296) * (m227 d) + -975148417024 + (136657) * (z215 d) + (654183) * (z220 d) + (666643) * (z225 d) := by
  simp only [z295, z281_linear, z294_linear] <;> ring

theorem z295_bounds (d : Digits) (hd : Bounded d) :
    (-4853655688408 : Int) ≤ z295 d ∧ z295 d ≤ 159529993004349 := by
  have h0 := hd 4
  norm_num at h0
  have h1 := m196_bounds d
  have h2 := m201_bounds d
  have h3 := m206_bounds d
  have h4 := m222_bounds d
  have h5 := m227_bounds d
  have h7 := z215_bounds d hd
  have h8 := z220_bounds d hd
  have h9 := z225_bounds d hd
  rw [z295_linear]
  omega

theorem z296_linear (d : Digits) : z296 d = (-683901) * (m196 d) + 717122174976 + (-683901) * (z215 d) := by
  simp only [z296, z216_linear] <;> ring

theorem z296_bounds (d : Digits) (hd : Bounded d) :
    (-118294574818320 : Int) ≤ z296 d ∧ z296 d ≤ 1867242590082 := by
  have h0 := m196_bounds d
  have h2 := z215_bounds d hd
  rw [z296_linear]
  omega

theorem z297_linear (d : Digits) : z297 d = (666643) * (d 17) + (d 5) + (-683901) * (m196 d) + (-997805) * (m201 d) + (470296) * (m206 d) + (136657) * (m222 d) + (654183) * (m227 d) + 440999608320 + (666643) * (z204 d) + (-683901) * (z215 d) + (-997805) * (z220 d) + (470296) * (z225 d) := by
  simp only [z297, z283_linear, z296_linear] <;> ring

theorem z297_bounds (d : Digits) (hd : Bounded d) :
    (-404939563290362 : Int) ≤ z297 d ∧ z297 d ≤ 23764907131307 := by
  have h0 := hd 17
  norm_num at h0
  have h1 := hd 5
  norm_num at h1
  have h2 := m196_bounds d
  have h3 := m201_bounds d
  have h4 := m206_bounds d
  have h5 := m222_bounds d
  have h6 := m227_bounds d
  have h8 := z204_bounds d hd
  have h9 := z215_bounds d hd
  have h10 := z220_bounds d hd
  have h11 := z225_bounds d hd
  rw [z297_linear]
  omega

end Firedancer.Common.ScalarArithmetic.IntegerRegisters
