import SSA.Projects.Firedancer.Common.Proof.Scalar.Arithmetic.IntegerBounds2

/-! Checked linear identities and interval certificates for the corresponding
numbered source arithmetic registers. Generated equations are verified by
`ring` and `omega`; no external arithmetic result is trusted. -/

namespace Firedancer.Common.ScalarArithmetic.IntegerRegisters

set_option maxHeartbeats 2000000

attribute [local irreducible] z61 z63 z65 z67 z69 z71 z73 z75 z77 z79 z81 z83 z85 z87 z89 z91 z93 z95 z97 z99 z101 z103 z105 z106 z107 z108 z109 z110 z111 z112 z113 z114 z115 z116 z117 z118 z119 z120 z121 z122 z123 z124 z125 z126 z127 z128 z129 z130 z131 z132 z133 z134 z135 z136 z137 z138 z139 z140 z141 z142 z143 z144 z145 z146 z147 z148 z149 z150 z151 z152 z153 z154 z155 z156 z157 z158 z159 z160 z161 z162 z163 z164 z165 z166 z167 z168 z169 z170 z171 z172 z173 z174 z175 z176 z177 z178 z179 z180 z181 z182 z183 z184 z185 z186 z187 z188 z189 z190 z191 z192 z193 z194 z195 z196 z197 z198 z199 z200 z201 z202 z203 z204 z205 z206 z207 z208 z209 z210 z211 z212 z213 z214 z215 z216 z217 z218 z219 z220 z221 z222 z223 z224 z225 z226 z227 z228 z229 z230 z231 z232 z233 z234 z235 z236 z237 z238 z239 z240 z241 z242 z243 z244 z245 z246 z247 z248 z249 z250 z251 z252 z253 z254 z255 z256 z257 z258 z259 z260 z261 z262 z263 z264 z265 z266 z267 z268 z269 z270 z271 z272 z273 z274 z275 z276 z277 z278 z279 z280 z281 z282 z283 z284 z285 z286 z287 z288 z289 z290 z291 z292 z293 z294 z295 z296 z297 z298 z299 z300 z301 z302 z303 z304 z305 z306 z307 z308 z309 z310 z311 z312 z313 z314 z315 z316 z317 z318 z319 z320 z321 z322 z323 z324 z325 z326 z327 z328 z329 z330 z331 z332 z333 z334 z335 z336 z337 z338 z339 z340 z341 z342 z343 z344 z345 z346 z347 z348 z349 z350 z351 z352 z353 z354 z355 z356 z357 z358 z359 z360 z361 z362 z363 z364 z365 z366 z367 z368 z369 z370 z371 z372 z373 z374 z375 z376 z377 z378 z379 z380 z381 z382 z383 z384 z385 z386 z387 z388 z389 z390 z391 z392 z393 z394 z395 z396 z397 z398 z399 z400 z401 z402 z403 z404 z405 z406 z407 z408 z409 z410 z411 z412 z413 z414 z415 z416 z417 z418 z419 z420 z421 z422 z423 z424 z425 z426 z427 z428 z429 z430 z431 z432 z433 z434 z435 z436 z437 z438 z439 z440 z441 z442 z443 z444 z445 z446 m170 m179 m189 m196 m201 m206 m210 m213 m217 m222 m227 m301 m306 m311 m321 m329 m334 m338 m341 m345 m349 m354 m358

theorem z298_linear (d : Digits) : z298 d = (d 0) + (666643) * (m196 d) + -699024801792 + (666643) * (z215 d) := by
  simp only [z298, z287_linear] <;> ring

theorem z298_bounds (d : Digits) (hd : Bounded d) :
    (-1820122334750 : Int) ≤ z298 d ∧ z298 d ≤ 115309456181487 := by
  have h0 := hd 0
  norm_num at h0
  have h1 := m196_bounds d
  have h3 := z215_bounds d hd
  rw [z298_linear]
  omega

theorem z299_bounds (d : Digits) (hd : Bounded d) :
    (-867902 : Int) ≤ z299 d ∧ z299 d ≤ 54983833 := by
  have h := z298_bounds d hd
  rw [z299]
  omega

theorem z300_linear (d : Digits) : z300 d = (d 1) + (470296) * (m196 d) + (666643) * (m222 d) + -1192166948864 + (470296) * (z215 d) + (z299 d) := by
  simp only [z300, z289_linear] <;> ring

theorem z300_bounds (d : Digits) (hd : Bounded d) :
    (-1983067421742 : Int) ≤ z300 d ∧ z300 d ≤ 82046331879429 := by
  have h0 := hd 1
  norm_num at h0
  have h1 := m196_bounds d
  have h2 := m222_bounds d
  have h4 := z215_bounds d hd
  have h5 := z299_bounds d hd
  rw [z300_linear]
  omega

theorem m301_bounds (d : Digits) : 0 ≤ m301 d ∧ m301 d ≤ 2097151 := by
  rw [m301]
  omega

theorem z301_linear (d : Digits) : z301 d = (d 0) + (666643) * (m196 d) + (-1) * (m301 d) + -699024801792 + (666643) * (z215 d) := by
  simp only [z301, z298_linear] <;> ring

theorem z301_bounds (d : Digits) (hd : Bounded d) :
    (-1820124431901 : Int) ≤ z301 d ∧ z301 d ≤ 115309456181487 := by
  have h0 := hd 0
  norm_num at h0
  have h1 := m196_bounds d
  have h2 := m301_bounds d
  have h4 := z215_bounds d hd
  rw [z301_linear]
  omega

theorem z302_linear (d : Digits) : z302 d = (m301 d) + -1048576 := by
  simp only [z302, z287_linear, z301_linear] <;> ring

theorem z302_bounds (d : Digits) (hd : Bounded d) :
    (-1048576 : Int) ≤ z302 d ∧ z302 d ≤ 1048575 := by
  have h0 := m301_bounds d
  rw [z302_linear]
  omega

theorem z303_linear (d : Digits) : z303 d = (d 2) + (654183) * (m196 d) + (666643) * (m201 d) + (470296) * (m222 d) + -1878126493696 + (654183) * (z215 d) + (666643) * (z220 d) := by
  simp only [z303, z291_linear] <;> ring

theorem z303_bounds (d : Digits) (hd : Bounded d) :
    (-4099367502852 : Int) ≤ z303 d ∧ z303 d ≤ 226080820427221 := by
  have h0 := hd 2
  norm_num at h0
  have h1 := m196_bounds d
  have h2 := m201_bounds d
  have h3 := m222_bounds d
  have h5 := z215_bounds d hd
  have h6 := z220_bounds d hd
  rw [z303_linear]
  omega

theorem z304_bounds (d : Digits) (hd : Bounded d) :
    (-1954731 : Int) ≤ z304 d ∧ z304 d ≤ 107803735 := by
  have h := z303_bounds d hd
  rw [z304]
  omega

theorem z305_linear (d : Digits) : z305 d = (d 3) + (-997805) * (m196 d) + (470296) * (m201 d) + (654183) * (m222 d) + (666643) * (m227 d) + -831853166592 + (-997805) * (z215 d) + (470296) * (z220 d) + (z304 d) := by
  simp only [z305, z293_linear] <;> ring

theorem z305_bounds (d : Digits) (hd : Bounded d) :
    (-175259679249579 : Int) ≤ z305 d ∧ z305 d ≤ 83427691131694 := by
  have h0 := hd 3
  norm_num at h0
  have h1 := m196_bounds d
  have h2 := m201_bounds d
  have h3 := m222_bounds d
  have h4 := m227_bounds d
  have h6 := z215_bounds d hd
  have h7 := z220_bounds d hd
  have h8 := z304_bounds d hd
  rw [z305_linear]
  omega

theorem m306_bounds (d : Digits) : 0 ≤ m306 d ∧ m306 d ≤ 2097151 := by
  rw [m306]
  omega

theorem z306_linear (d : Digits) : z306 d = (d 2) + (654183) * (m196 d) + (666643) * (m201 d) + (470296) * (m222 d) + (-1) * (m306 d) + -1878126493696 + (654183) * (z215 d) + (666643) * (z220 d) := by
  simp only [z306, z303_linear] <;> ring

theorem z306_bounds (d : Digits) (hd : Bounded d) :
    (-4099369600003 : Int) ≤ z306 d ∧ z306 d ≤ 226080820427221 := by
  have h0 := hd 2
  norm_num at h0
  have h1 := m196_bounds d
  have h2 := m201_bounds d
  have h3 := m222_bounds d
  have h4 := m306_bounds d
  have h6 := z215_bounds d hd
  have h7 := z220_bounds d hd
  rw [z306_linear]
  omega

theorem z307_linear (d : Digits) : z307 d = (m306 d) + -1048576 := by
  simp only [z307, z291_linear, z306_linear] <;> ring

theorem z307_bounds (d : Digits) (hd : Bounded d) :
    (-1048576 : Int) ≤ z307 d ∧ z307 d ≤ 1048575 := by
  have h0 := m306_bounds d
  rw [z307_linear]
  omega

theorem z308_linear (d : Digits) : z308 d = (d 4) + (136657) * (m196 d) + (654183) * (m201 d) + (666643) * (m206 d) + (-997805) * (m222 d) + (470296) * (m227 d) + -975147368448 + (136657) * (z215 d) + (654183) * (z220 d) + (666643) * (z225 d) := by
  simp only [z308, z295_linear] <;> ring

theorem z308_bounds (d : Digits) (hd : Bounded d) :
    (-4853654639832 : Int) ≤ z308 d ∧ z308 d ≤ 159529994052925 := by
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
  rw [z308_linear]
  omega

theorem z309_bounds (d : Digits) (hd : Bounded d) :
    (-2314403 : Int) ≤ z309 d ∧ z309 d ≤ 76069829 := by
  have h := z308_bounds d hd
  rw [z309]
  omega

theorem z310_linear (d : Digits) : z310 d = (666643) * (d 17) + (d 5) + (-683901) * (m196 d) + (-997805) * (m201 d) + (470296) * (m206 d) + (136657) * (m222 d) + (654183) * (m227 d) + 440999608320 + (666643) * (z204 d) + (-683901) * (z215 d) + (-997805) * (z220 d) + (470296) * (z225 d) + (z309 d) := by
  simp only [z310, z297_linear] <;> ring

theorem z310_bounds (d : Digits) (hd : Bounded d) :
    (-404939565604765 : Int) ≤ z310 d ∧ z310 d ≤ 23764983201136 := by
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
  have h12 := z309_bounds d hd
  rw [z310_linear]
  omega

theorem m311_bounds (d : Digits) : 0 ≤ m311 d ∧ m311 d ≤ 2097151 := by
  rw [m311]
  omega

theorem z311_linear (d : Digits) : z311 d = (d 4) + (136657) * (m196 d) + (654183) * (m201 d) + (666643) * (m206 d) + (-997805) * (m222 d) + (470296) * (m227 d) + (-1) * (m311 d) + -975147368448 + (136657) * (z215 d) + (654183) * (z220 d) + (666643) * (z225 d) := by
  simp only [z311, z308_linear] <;> ring

theorem z311_bounds (d : Digits) (hd : Bounded d) :
    (-4853656736983 : Int) ≤ z311 d ∧ z311 d ≤ 159529994052925 := by
  have h0 := hd 4
  norm_num at h0
  have h1 := m196_bounds d
  have h2 := m201_bounds d
  have h3 := m206_bounds d
  have h4 := m222_bounds d
  have h5 := m227_bounds d
  have h6 := m311_bounds d
  have h8 := z215_bounds d hd
  have h9 := z220_bounds d hd
  have h10 := z225_bounds d hd
  rw [z311_linear]
  omega

theorem z312_linear (d : Digits) : z312 d = (m311 d) + -1048576 := by
  simp only [z312, z295_linear, z311_linear] <;> ring

theorem z312_bounds (d : Digits) (hd : Bounded d) :
    (-1048576 : Int) ≤ z312 d ∧ z312 d ≤ 1048575 := by
  have h0 := m311_bounds d
  rw [z312_linear]
  omega

theorem z313_linear (d : Digits) : z313 d = (470296) * (d 17) + (m170 d) + (136657) * (m201 d) + (654183) * (m206 d) + (-683901) * (m222 d) + (-997805) * (m227 d) + 934140706816 + (470296) * (z204 d) + (136657) * (z220 d) + (654183) * (z225 d) := by
  simp only [z313, z285_linear] <;> ring

theorem z313_bounds (d : Digits) (hd : Bounded d) :
    (-85608735430017 : Int) ≤ z313 d ∧ z313 d ≤ 49369746964009 := by
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
  rw [z313_linear]
  omega

theorem z314_bounds (d : Digits) (hd : Bounded d) :
    (-40821427 : Int) ≤ z314 d ∧ z314 d ≤ 23541329 := by
  have h := z313_bounds d hd
  rw [z314]
  omega

theorem z315_linear (d : Digits) : z315 d = (654183) * (d 17) + (470296) * (d 18) + (666643) * (d 19) + (d 7) + (z168 d) + (654183) * (z204 d) := by
  simp only [z315, z233_linear, z169_linear] <;> ring

theorem z315_bounds (d : Digits) (hd : Bounded d) :
    (-114533480418048 : Int) ≤ z315 d ∧ z315 d ≤ 3756256711400 := by
  have h0 := hd 17
  norm_num at h0
  have h1 := hd 18
  norm_num at h1
  have h2 := hd 19
  norm_num at h2
  have h3 := hd 7
  norm_num at h3
  have h4 := z168_bounds d hd
  have h5 := z204_bounds d hd
  rw [z315_linear]
  omega

theorem z316_linear (d : Digits) : z316 d = (654183) * (d 17) + (m210 d) + -1048576 + (654183) * (z204 d) := by
  simp only [z316, z315_linear, z210_linear] <;> ring

theorem z316_bounds (d : Digits) (hd : Bounded d) :
    (-114533481466624 : Int) ≤ z316 d ∧ z316 d ≤ 1371922235391 := by
  have h0 := hd 17
  norm_num at h0
  have h1 := m210_bounds d
  have h3 := z204_bounds d hd
  rw [z316_linear]
  omega

theorem z317_linear (d : Digits) : z317 d = (654183) * (d 17) + (-997805) * (m206 d) + (m210 d) + 1046273327104 + (654183) * (z204 d) + (-997805) * (z225 d) := by
  simp only [z317, z316_linear, z246_linear] <;> ring

theorem z317_bounds (d : Digits) (hd : Bounded d) :
    (-150487157540864 : Int) ≤ z317 d ∧ z317 d ≤ 3100718180586 := by
  have h0 := hd 17
  norm_num at h0
  have h1 := m206_bounds d
  have h2 := m210_bounds d
  have h4 := z204_bounds d hd
  have h5 := z225_bounds d hd
  rw [z317_linear]
  omega

theorem z318_linear (d : Digits) : z318 d = (654183) * (d 17) + (-997805) * (m206 d) + (m210 d) + (136657) * (m227 d) + 902978076672 + (654183) * (z204 d) + (-997805) * (z225 d) := by
  simp only [z318, z317_linear, z257_linear] <;> ring

theorem z318_bounds (d : Digits) (hd : Bounded d) :
    (-150630452791296 : Int) ≤ z318 d ∧ z318 d ≤ 3244013294361 := by
  have h0 := hd 17
  norm_num at h0
  have h1 := m206_bounds d
  have h2 := m210_bounds d
  have h3 := m227_bounds d
  have h5 := z204_bounds d hd
  have h6 := z225_bounds d hd
  rw [z318_linear]
  omega

theorem z319_linear (d : Digits) : z319 d = (654183) * (d 17) + (-683901) * (m201 d) + (-997805) * (m206 d) + (m210 d) + (136657) * (m227 d) + 1620100251648 + (654183) * (z204 d) + (-683901) * (z220 d) + (-997805) * (z225 d) := by
  simp only [z319, z318_linear, z273_linear] <;> ring

theorem z319_bounds (d : Digits) (hd : Bounded d) :
    (-265974554225634 : Int) ≤ z319 d ∧ z319 d ≤ 5111255884443 := by
  have h0 := hd 17
  norm_num at h0
  have h1 := m201_bounds d
  have h2 := m206_bounds d
  have h3 := m210_bounds d
  have h4 := m227_bounds d
  have h6 := z204_bounds d hd
  have h7 := z220_bounds d hd
  have h8 := z225_bounds d hd
  rw [z319_linear]
  omega

theorem z320_linear (d : Digits) : z320 d = (654183) * (d 17) + (-683901) * (m201 d) + (-997805) * (m206 d) + (m210 d) + (136657) * (m227 d) + 1620100251648 + (654183) * (z204 d) + (-683901) * (z220 d) + (-997805) * (z225 d) + (z314 d) := by
  simp only [z320, z319_linear] <;> ring

theorem z320_bounds (d : Digits) (hd : Bounded d) :
    (-265974595047061 : Int) ≤ z320 d ∧ z320 d ≤ 5111279425772 := by
  have h0 := hd 17
  norm_num at h0
  have h1 := m201_bounds d
  have h2 := m206_bounds d
  have h3 := m210_bounds d
  have h4 := m227_bounds d
  have h6 := z204_bounds d hd
  have h7 := z220_bounds d hd
  have h8 := z225_bounds d hd
  have h9 := z314_bounds d hd
  rw [z320_linear]
  omega

theorem m321_bounds (d : Digits) : 0 ≤ m321 d ∧ m321 d ≤ 2097151 := by
  rw [m321]
  omega

theorem z321_linear (d : Digits) : z321 d = (470296) * (d 17) + (m170 d) + (136657) * (m201 d) + (654183) * (m206 d) + (-683901) * (m222 d) + (-997805) * (m227 d) + (-1) * (m321 d) + 934140706816 + (470296) * (z204 d) + (136657) * (z220 d) + (654183) * (z225 d) := by
  simp only [z321, z313_linear] <;> ring

theorem z321_bounds (d : Digits) (hd : Bounded d) :
    (-85608737527168 : Int) ≤ z321 d ∧ z321 d ≤ 49369746964009 := by
  have h0 := hd 17
  norm_num at h0
  have h1 := m170_bounds d
  have h2 := m201_bounds d
  have h3 := m206_bounds d
  have h4 := m222_bounds d
  have h5 := m227_bounds d
  have h6 := m321_bounds d
  have h8 := z204_bounds d hd
  have h9 := z220_bounds d hd
  have h10 := z225_bounds d hd
  rw [z321_linear]
  omega

theorem z322_linear (d : Digits) : z322 d = (m321 d) + -1048576 := by
  simp only [z322, z285_linear, z321_linear] <;> ring

theorem z322_bounds (d : Digits) (hd : Bounded d) :
    (-1048576 : Int) ≤ z322 d ∧ z322 d ≤ 1048575 := by
  have h0 := m321_bounds d
  rw [z322_linear]
  omega

theorem z323_linear (d : Digits) : z323 d = (-997805) * (d 17) + (m179 d) + (136657) * (m206 d) + (-683901) * (m227 d) + 573826924544 + (-997805) * (z204 d) + (z209 d) + (136657) * (z225 d) := by
  simp only [z323, z262_linear] <;> ring

theorem z323_bounds (d : Digits) (hd : Bounded d) :
    (-3046442023978 : Int) ≤ z323 d ∧ z323 d ≤ 180335613735723 := by
  have h0 := hd 17
  norm_num at h0
  have h1 := m179_bounds d
  have h2 := m206_bounds d
  have h3 := m227_bounds d
  have h5 := z204_bounds d hd
  have h6 := z209_bounds d hd
  have h7 := z225_bounds d hd
  rw [z323_linear]
  omega

theorem z324_bounds (d : Digits) (hd : Bounded d) :
    (-1452657 : Int) ≤ z324 d ∧ z324 d ≤ 85990721 := by
  have h := z323_bounds d hd
  rw [z324]
  omega

theorem z325_linear (d : Digits) : z325 d = (136657) * (d 17) + (-997805) * (d 18) + (654183) * (d 19) + (470296) * (d 20) + (666643) * (d 21) + (d 9) + (z173 d) + (136657) * (z204 d) := by
  simp only [z325, z178_linear, z235_linear] <;> ring

theorem z325_bounds (d : Digits) (hd : Bounded d) :
    (-26018271646547 : Int) ≤ z325 d ∧ z325 d ≤ 4042847682559 := by
  have h0 := hd 17
  norm_num at h0
  have h1 := hd 18
  norm_num at h1
  have h2 := hd 19
  norm_num at h2
  have h3 := hd 20
  norm_num at h3
  have h4 := hd 21
  norm_num at h4
  have h5 := hd 9
  norm_num at h5
  have h6 := z173_bounds d hd
  have h7 := z204_bounds d hd
  rw [z325_linear]
  omega

theorem z326_linear (d : Digits) : z326 d = (136657) * (d 17) + (m213 d) + -1048576 + (136657) * (z204 d) := by
  simp only [z326, z325_linear, z213_linear] <;> ring

theorem z326_bounds (d : Digits) (hd : Bounded d) :
    (-23925724941568 : Int) ≤ z326 d ∧ z326 d ≤ 286591549439 := by
  have h0 := hd 17
  norm_num at h0
  have h1 := m213_bounds d
  have h3 := z204_bounds d hd
  rw [z326_linear]
  omega

theorem z327_linear (d : Digits) : z327 d = (136657) * (d 17) + (-683901) * (m206 d) + (m213 d) + 717121126400 + (136657) * (z204 d) + (-683901) * (z225 d) := by
  simp only [z327, z326_linear, z248_linear] <;> ring

theorem z327_bounds (d : Digits) (hd : Bounded d) :
    (-48568571009536 : Int) ≤ z327 d ∧ z327 d ≤ 1471517738138 := by
  have h0 := hd 17
  norm_num at h0
  have h1 := m206_bounds d
  have h2 := m213_bounds d
  have h4 := z204_bounds d hd
  have h5 := z225_bounds d hd
  rw [z327_linear]
  omega

theorem z328_linear (d : Digits) : z328 d = (136657) * (d 17) + (-683901) * (m206 d) + (m213 d) + 717121126400 + (136657) * (z204 d) + (-683901) * (z225 d) + (z324 d) := by
  simp only [z328, z327_linear] <;> ring

theorem z328_bounds (d : Digits) (hd : Bounded d) :
    (-48568572462193 : Int) ≤ z328 d ∧ z328 d ≤ 1471603728859 := by
  have h0 := hd 17
  norm_num at h0
  have h1 := m206_bounds d
  have h2 := m213_bounds d
  have h4 := z204_bounds d hd
  have h5 := z225_bounds d hd
  have h6 := z324_bounds d hd
  rw [z328_linear]
  omega

theorem m329_bounds (d : Digits) : 0 ≤ m329 d ∧ m329 d ≤ 2097151 := by
  rw [m329]
  omega

theorem z329_linear (d : Digits) : z329 d = (-997805) * (d 17) + (m179 d) + (136657) * (m206 d) + (-683901) * (m227 d) + (-1) * (m329 d) + 573826924544 + (-997805) * (z204 d) + (z209 d) + (136657) * (z225 d) := by
  simp only [z329, z323_linear] <;> ring

theorem z329_bounds (d : Digits) (hd : Bounded d) :
    (-3046444121129 : Int) ≤ z329 d ∧ z329 d ≤ 180335613735723 := by
  have h0 := hd 17
  norm_num at h0
  have h1 := m179_bounds d
  have h2 := m206_bounds d
  have h3 := m227_bounds d
  have h4 := m329_bounds d
  have h6 := z204_bounds d hd
  have h7 := z209_bounds d hd
  have h8 := z225_bounds d hd
  rw [z329_linear]
  omega

theorem z330_linear (d : Digits) : z330 d = (m329 d) + -1048576 := by
  simp only [z330, z262_linear, z329_linear] <;> ring

theorem z330_bounds (d : Digits) (hd : Bounded d) :
    (-1048576 : Int) ≤ z330 d ∧ z330 d ≤ 1048575 := by
  have h0 := m329_bounds d
  rw [z330_linear]
  omega

theorem z331_linear (d : Digits) : z331 d = (-683901) * (d 17) + (m189 d) + (-683901) * (z204 d) + (z212 d) := by
  simp only [z331, z239_linear] <;> ring

theorem z331_bounds (d : Digits) (hd : Bounded d) :
    (-1434245347757 : Int) ≤ z331 d ∧ z331 d ≤ 119736471805330 := by
  have h0 := hd 17
  norm_num at h0
  have h1 := m189_bounds d
  have h2 := z204_bounds d hd
  have h3 := z212_bounds d hd
  rw [z331_linear]
  omega

theorem z332_bounds (d : Digits) (hd : Bounded d) :
    (-683902 : Int) ≤ z332 d ∧ z332 d ≤ 57094798 := by
  have h := z331_bounds d hd
  rw [z332]
  omega

theorem z333_linear (d : Digits) : z333 d = (m217 d) + -1048576 + (z332 d) := by
  simp only [z333, z218_linear] <;> ring

theorem z333_bounds (d : Digits) (hd : Bounded d) :
    (-1732478 : Int) ≤ z333 d ∧ z333 d ≤ 58143373 := by
  have h0 := m217_bounds d
  have h2 := z332_bounds d hd
  rw [z333_linear]
  omega

theorem m334_bounds (d : Digits) : 0 ≤ m334 d ∧ m334 d ≤ 2097151 := by
  rw [m334]
  omega

theorem z334_linear (d : Digits) : z334 d = (-683901) * (d 17) + (m189 d) + (-1) * (m334 d) + (-683901) * (z204 d) + (z212 d) := by
  simp only [z334, z331_linear] <;> ring

theorem z334_bounds (d : Digits) (hd : Bounded d) :
    (-1434247444908 : Int) ≤ z334 d ∧ z334 d ≤ 119736471805330 := by
  have h0 := hd 17
  norm_num at h0
  have h1 := m189_bounds d
  have h2 := m334_bounds d
  have h3 := z204_bounds d hd
  have h4 := z212_bounds d hd
  rw [z334_linear]
  omega

theorem z335_linear (d : Digits) : z335 d = (m334 d) + -1048576 := by
  simp only [z335, z239_linear, z334_linear] <;> ring

theorem z335_bounds (d : Digits) (hd : Bounded d) :
    (-1048576 : Int) ≤ z335 d ∧ z335 d ≤ 1048575 := by
  have h0 := m334_bounds d
  rw [z335_linear]
  omega

theorem z336_linear (d : Digits) : z336 d = (d 1) + (470296) * (m196 d) + (666643) * (m222 d) + -1192165900288 + (470296) * (z215 d) + (z299 d) := by
  simp only [z336, z300_linear] <;> ring

theorem z336_bounds (d : Digits) (hd : Bounded d) :
    (-1983066373166 : Int) ≤ z336 d ∧ z336 d ≤ 82046332928005 := by
  have h0 := hd 1
  norm_num at h0
  have h1 := m196_bounds d
  have h2 := m222_bounds d
  have h4 := z215_bounds d hd
  have h5 := z299_bounds d hd
  rw [z336_linear]
  omega

theorem z337_bounds (d : Digits) (hd : Bounded d) :
    (-945600 : Int) ≤ z337 d ∧ z337 d ≤ 39122740 := by
  have h := z336_bounds d hd
  rw [z337]
  omega

theorem m338_bounds (d : Digits) : 0 ≤ m338 d ∧ m338 d ≤ 2097151 := by
  rw [m338]
  omega

theorem z338_linear (d : Digits) : z338 d = (d 1) + (470296) * (m196 d) + (666643) * (m222 d) + (-1) * (m338 d) + -1192165900288 + (470296) * (z215 d) + (z299 d) := by
  simp only [z338, z336_linear] <;> ring

theorem z338_bounds (d : Digits) (hd : Bounded d) :
    (-1983068470317 : Int) ≤ z338 d ∧ z338 d ≤ 82046332928005 := by
  have h0 := hd 1
  norm_num at h0
  have h1 := m196_bounds d
  have h2 := m222_bounds d
  have h3 := m338_bounds d
  have h5 := z215_bounds d hd
  have h6 := z299_bounds d hd
  rw [z338_linear]
  omega

theorem z339_linear (d : Digits) : z339 d = (d 3) + (-997805) * (m196 d) + (470296) * (m201 d) + (654183) * (m222 d) + (666643) * (m227 d) + -831852118016 + (-997805) * (z215 d) + (470296) * (z220 d) + (z304 d) := by
  simp only [z339, z305_linear] <;> ring

theorem z339_bounds (d : Digits) (hd : Bounded d) :
    (-175259678201003 : Int) ≤ z339 d ∧ z339 d ≤ 83427692180270 := by
  have h0 := hd 3
  norm_num at h0
  have h1 := m196_bounds d
  have h2 := m201_bounds d
  have h3 := m222_bounds d
  have h4 := m227_bounds d
  have h6 := z215_bounds d hd
  have h7 := z220_bounds d hd
  have h8 := z304_bounds d hd
  rw [z339_linear]
  omega

theorem z340_bounds (d : Digits) (hd : Bounded d) :
    (-83570327 : Int) ≤ z340 d ∧ z340 d ≤ 39781423 := by
  have h := z339_bounds d hd
  rw [z340]
  omega

theorem m341_bounds (d : Digits) : 0 ≤ m341 d ∧ m341 d ≤ 2097151 := by
  rw [m341]
  omega

theorem z341_linear (d : Digits) : z341 d = (d 3) + (-997805) * (m196 d) + (470296) * (m201 d) + (654183) * (m222 d) + (666643) * (m227 d) + (-1) * (m341 d) + -831852118016 + (-997805) * (z215 d) + (470296) * (z220 d) + (z304 d) := by
  simp only [z341, z339_linear] <;> ring

theorem z341_bounds (d : Digits) (hd : Bounded d) :
    (-175259680298154 : Int) ≤ z341 d ∧ z341 d ≤ 83427692180270 := by
  have h0 := hd 3
  norm_num at h0
  have h1 := m196_bounds d
  have h2 := m201_bounds d
  have h3 := m222_bounds d
  have h4 := m227_bounds d
  have h5 := m341_bounds d
  have h7 := z215_bounds d hd
  have h8 := z220_bounds d hd
  have h9 := z304_bounds d hd
  rw [z341_linear]
  omega

theorem z342_linear (d : Digits) : z342 d = (666643) * (d 17) + (d 5) + (-683901) * (m196 d) + (-997805) * (m201 d) + (470296) * (m206 d) + (136657) * (m222 d) + (654183) * (m227 d) + 441000656896 + (666643) * (z204 d) + (-683901) * (z215 d) + (-997805) * (z220 d) + (470296) * (z225 d) + (z309 d) := by
  simp only [z342, z310_linear] <;> ring

theorem z342_bounds (d : Digits) (hd : Bounded d) :
    (-404939564556189 : Int) ≤ z342 d ∧ z342 d ≤ 23764984249712 := by
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
  have h12 := z309_bounds d hd
  rw [z342_linear]
  omega

theorem z343_bounds (d : Digits) (hd : Bounded d) :
    (-193090232 : Int) ≤ z343 d ∧ z343 d ≤ 11332027 := by
  have h := z342_bounds d hd
  rw [z343]
  omega

theorem z344_linear (d : Digits) : z344 d = (m321 d) + -1048576 + (z343 d) := by
  simp only [z344, z322_linear] <;> ring

theorem z344_bounds (d : Digits) (hd : Bounded d) :
    (-194138808 : Int) ≤ z344 d ∧ z344 d ≤ 12380602 := by
  have h0 := m321_bounds d
  have h2 := z343_bounds d hd
  rw [z344_linear]
  omega

theorem m345_bounds (d : Digits) : 0 ≤ m345 d ∧ m345 d ≤ 2097151 := by
  rw [m345]
  omega

theorem z345_linear (d : Digits) : z345 d = (666643) * (d 17) + (d 5) + (-683901) * (m196 d) + (-997805) * (m201 d) + (470296) * (m206 d) + (136657) * (m222 d) + (654183) * (m227 d) + (-1) * (m345 d) + 441000656896 + (666643) * (z204 d) + (-683901) * (z215 d) + (-997805) * (z220 d) + (470296) * (z225 d) + (z309 d) := by
  simp only [z345, z342_linear] <;> ring

theorem z345_bounds (d : Digits) (hd : Bounded d) :
    (-404939566653340 : Int) ≤ z345 d ∧ z345 d ≤ 23764984249712 := by
  have h0 := hd 17
  norm_num at h0
  have h1 := hd 5
  norm_num at h1
  have h2 := m196_bounds d
  have h3 := m201_bounds d
  have h4 := m206_bounds d
  have h5 := m222_bounds d
  have h6 := m227_bounds d
  have h7 := m345_bounds d
  have h9 := z204_bounds d hd
  have h10 := z215_bounds d hd
  have h11 := z220_bounds d hd
  have h12 := z225_bounds d hd
  have h13 := z309_bounds d hd
  rw [z345_linear]
  omega

theorem z346_linear (d : Digits) : z346 d = (654183) * (d 17) + (-683901) * (m201 d) + (-997805) * (m206 d) + (m210 d) + (136657) * (m227 d) + 1620101300224 + (654183) * (z204 d) + (-683901) * (z220 d) + (-997805) * (z225 d) + (z314 d) := by
  simp only [z346, z320_linear] <;> ring

theorem z346_bounds (d : Digits) (hd : Bounded d) :
    (-265974593998485 : Int) ≤ z346 d ∧ z346 d ≤ 5111280474348 := by
  have h0 := hd 17
  norm_num at h0
  have h1 := m201_bounds d
  have h2 := m206_bounds d
  have h3 := m210_bounds d
  have h4 := m227_bounds d
  have h6 := z204_bounds d hd
  have h7 := z220_bounds d hd
  have h8 := z225_bounds d hd
  have h9 := z314_bounds d hd
  rw [z346_linear]
  omega

theorem z347_bounds (d : Digits) (hd : Bounded d) :
    (-126826570 : Int) ≤ z347 d ∧ z347 d ≤ 2437248 := by
  have h := z346_bounds d hd
  rw [z347]
  omega

theorem z348_linear (d : Digits) : z348 d = (m329 d) + -1048576 + (z347 d) := by
  simp only [z348, z330_linear] <;> ring

theorem z348_bounds (d : Digits) (hd : Bounded d) :
    (-127875146 : Int) ≤ z348 d ∧ z348 d ≤ 3485823 := by
  have h0 := m329_bounds d
  have h2 := z347_bounds d hd
  rw [z348_linear]
  omega

theorem m349_bounds (d : Digits) : 0 ≤ m349 d ∧ m349 d ≤ 2097151 := by
  rw [m349]
  omega

theorem z349_linear (d : Digits) : z349 d = (654183) * (d 17) + (-683901) * (m201 d) + (-997805) * (m206 d) + (m210 d) + (136657) * (m227 d) + (-1) * (m349 d) + 1620101300224 + (654183) * (z204 d) + (-683901) * (z220 d) + (-997805) * (z225 d) + (z314 d) := by
  simp only [z349, z346_linear] <;> ring

theorem z349_bounds (d : Digits) (hd : Bounded d) :
    (-265974596095636 : Int) ≤ z349 d ∧ z349 d ≤ 5111280474348 := by
  have h0 := hd 17
  norm_num at h0
  have h1 := m201_bounds d
  have h2 := m206_bounds d
  have h3 := m210_bounds d
  have h4 := m227_bounds d
  have h5 := m349_bounds d
  have h7 := z204_bounds d hd
  have h8 := z220_bounds d hd
  have h9 := z225_bounds d hd
  have h10 := z314_bounds d hd
  rw [z349_linear]
  omega

theorem z350_linear (d : Digits) : z350 d = (m349 d) + -1048576 := by
  simp only [z350, z320_linear, z349_linear] <;> ring

theorem z350_bounds (d : Digits) (hd : Bounded d) :
    (-1048576 : Int) ≤ z350 d ∧ z350 d ≤ 1048575 := by
  have h0 := m349_bounds d
  rw [z350_linear]
  omega

theorem z351_linear (d : Digits) : z351 d = (136657) * (d 17) + (-683901) * (m206 d) + (m213 d) + 717122174976 + (136657) * (z204 d) + (-683901) * (z225 d) + (z324 d) := by
  simp only [z351, z328_linear] <;> ring

theorem z351_bounds (d : Digits) (hd : Bounded d) :
    (-48568571413617 : Int) ≤ z351 d ∧ z351 d ≤ 1471604777435 := by
  have h0 := hd 17
  norm_num at h0
  have h1 := m206_bounds d
  have h2 := m213_bounds d
  have h4 := z204_bounds d hd
  have h5 := z225_bounds d hd
  have h6 := z324_bounds d hd
  rw [z351_linear]
  omega

theorem z352_bounds (d : Digits) (hd : Bounded d) :
    (-23159300 : Int) ≤ z352 d ∧ z352 d ≤ 701715 := by
  have h := z351_bounds d hd
  rw [z352]
  omega

theorem z353_linear (d : Digits) : z353 d = (m334 d) + -1048576 + (z352 d) := by
  simp only [z353, z335_linear] <;> ring

theorem z353_bounds (d : Digits) (hd : Bounded d) :
    (-24207876 : Int) ≤ z353 d ∧ z353 d ≤ 1750290 := by
  have h0 := m334_bounds d
  have h2 := z352_bounds d hd
  rw [z353_linear]
  omega

theorem m354_bounds (d : Digits) : 0 ≤ m354 d ∧ m354 d ≤ 2097151 := by
  rw [m354]
  omega

theorem z354_linear (d : Digits) : z354 d = (136657) * (d 17) + (-683901) * (m206 d) + (m213 d) + (-1) * (m354 d) + 717122174976 + (136657) * (z204 d) + (-683901) * (z225 d) + (z324 d) := by
  simp only [z354, z351_linear] <;> ring

theorem z354_bounds (d : Digits) (hd : Bounded d) :
    (-48568573510768 : Int) ≤ z354 d ∧ z354 d ≤ 1471604777435 := by
  have h0 := hd 17
  norm_num at h0
  have h1 := m206_bounds d
  have h2 := m213_bounds d
  have h3 := m354_bounds d
  have h5 := z204_bounds d hd
  have h6 := z225_bounds d hd
  have h7 := z324_bounds d hd
  rw [z354_linear]
  omega

theorem z355_linear (d : Digits) : z355 d = (m354 d) + -1048576 := by
  simp only [z355, z328_linear, z354_linear] <;> ring

theorem z355_bounds (d : Digits) (hd : Bounded d) :
    (-1048576 : Int) ≤ z355 d ∧ z355 d ≤ 1048575 := by
  have h0 := m354_bounds d
  rw [z355_linear]
  omega

theorem z356_linear (d : Digits) : z356 d = (m217 d) + (z332 d) := by
  simp only [z356, z333_linear] <;> ring

theorem z356_bounds (d : Digits) (hd : Bounded d) :
    (-683902 : Int) ≤ z356 d ∧ z356 d ≤ 59191949 := by
  have h0 := m217_bounds d
  have h1 := z332_bounds d hd
  rw [z356_linear]
  omega

theorem z357_bounds (d : Digits) (hd : Bounded d) :
    (-1 : Int) ≤ z357 d ∧ z357 d ≤ 28 := by
  have h := z356_bounds d hd
  rw [z357]
  omega

theorem m358_bounds (d : Digits) : 0 ≤ m358 d ∧ m358 d ≤ 2097151 := by
  rw [m358]
  omega

theorem z358_linear (d : Digits) : z358 d = (m217 d) + (-1) * (m358 d) + (z332 d) := by
  simp only [z358, z356_linear] <;> ring

theorem z358_bounds (d : Digits) (hd : Bounded d) :
    (-2781053 : Int) ≤ z358 d ∧ z358 d ≤ 59191949 := by
  have h0 := m217_bounds d
  have h1 := m358_bounds d
  have h2 := z332_bounds d hd
  rw [z358_linear]
  omega

theorem z359_linear (d : Digits) : z359 d = (m358 d) + -1048576 := by
  simp only [z359, z333_linear, z358_linear] <;> ring

theorem z359_bounds (d : Digits) (hd : Bounded d) :
    (-1048576 : Int) ≤ z359 d ∧ z359 d ≤ 1048575 := by
  have h0 := m358_bounds d
  rw [z359_linear]
  omega

theorem z360_linear (d : Digits) : z360 d = (666643) * (z357 d) := by
  simp only [z360] <;> ring

theorem z360_bounds (d : Digits) (hd : Bounded d) :
    (-666643 : Int) ≤ z360 d ∧ z360 d ≤ 18666004 := by
  have h0 := z357_bounds d hd
  rw [z360_linear]
  omega

theorem z361_linear (d : Digits) : z361 d = (m301 d) + -1048576 + (666643) * (z357 d) := by
  simp only [z361, z302_linear, z360_linear] <;> ring

theorem z361_bounds (d : Digits) (hd : Bounded d) :
    (-1715219 : Int) ≤ z361 d ∧ z361 d ≤ 19714579 := by
  have h0 := m301_bounds d
  have h2 := z357_bounds d hd
  rw [z361_linear]
  omega

theorem z362_linear (d : Digits) : z362 d = (470296) * (z357 d) := by
  simp only [z362] <;> ring

theorem z362_bounds (d : Digits) (hd : Bounded d) :
    (-470296 : Int) ≤ z362 d ∧ z362 d ≤ 13168288 := by
  have h0 := z357_bounds d hd
  rw [z362_linear]
  omega

theorem z363_linear (d : Digits) : z363 d = (654183) * (z357 d) := by
  simp only [z363] <;> ring

theorem z363_bounds (d : Digits) (hd : Bounded d) :
    (-654183 : Int) ≤ z363 d ∧ z363 d ≤ 18317124 := by
  have h0 := z357_bounds d hd
  rw [z363_linear]
  omega

theorem z364_linear (d : Digits) : z364 d = (-997805) * (z357 d) := by
  simp only [z364] <;> ring

theorem z364_bounds (d : Digits) (hd : Bounded d) :
    (-27938540 : Int) ≤ z364 d ∧ z364 d ≤ 997805 := by
  have h0 := z357_bounds d hd
  rw [z364_linear]
  omega

theorem z365_linear (d : Digits) : z365 d = (136657) * (z357 d) := by
  simp only [z365] <;> ring

theorem z365_bounds (d : Digits) (hd : Bounded d) :
    (-136657 : Int) ≤ z365 d ∧ z365 d ≤ 3826396 := by
  have h0 := z357_bounds d hd
  rw [z365_linear]
  omega

theorem z366_linear (d : Digits) : z366 d = (-683901) * (z357 d) := by
  simp only [z366] <;> ring

theorem z366_bounds (d : Digits) (hd : Bounded d) :
    (-19149228 : Int) ≤ z366 d ∧ z366 d ≤ 683901 := by
  have h0 := z357_bounds d hd
  rw [z366_linear]
  omega

end Firedancer.Common.ScalarArithmetic.IntegerRegisters
