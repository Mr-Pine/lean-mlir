import SSA.Projects.Firedancer.Common.Proof.Scalar.Arithmetic.IntegerBounds4

/-! Checked linear identities and interval certificates for the corresponding
numbered source arithmetic registers. Generated equations are verified by
`ring` and `omega`; no external arithmetic result is trusted. -/

namespace Firedancer.Common.ScalarArithmetic.IntegerRegisters

set_option maxHeartbeats 2000000

attribute [local irreducible] z61 z63 z65 z67 z69 z71 z73 z75 z77 z79 z81 z83 z85 z87 z89 z91 z93 z95 z97 z99 z101 z103 z105 z106 z107 z108 z109 z110 z111 z112 z113 z114 z115 z116 z117 z118 z119 z120 z121 z122 z123 z124 z125 z126 z127 z128 z129 z130 z131 z132 z133 z134 z135 z136 z137 z138 z139 z140 z141 z142 z143 z144 z145 z146 z147 z148 z149 z150 z151 z152 z153 z154 z155 z156 z157 z158 z159 z160 z161 z162 z163 z164 z165 z166 z167 z168 z169 z170 z171 z172 z173 z174 z175 z176 z177 z178 z179 z180 z181 z182 z183 z184 z185 z186 z187 z188 z189 z190 z191 z192 z193 z194 z195 z196 z197 z198 z199 z200 z201 z202 z203 z204 z205 z206 z207 z208 z209 z210 z211 z212 z213 z214 z215 z216 z217 z218 z219 z220 z221 z222 z223 z224 z225 z226 z227 z228 z229 z230 z231 z232 z233 z234 z235 z236 z237 z238 z239 z240 z241 z242 z243 z244 z245 z246 z247 z248 z249 z250 z251 z252 z253 z254 z255 z256 z257 z258 z259 z260 z261 z262 z263 z264 z265 z266 z267 z268 z269 z270 z271 z272 z273 z274 z275 z276 z277 z278 z279 z280 z281 z282 z283 z284 z285 z286 z287 z288 z289 z290 z291 z292 z293 z294 z295 z296 z297 z298 z299 z300 z301 z302 z303 z304 z305 z306 z307 z308 z309 z310 z311 z312 z313 z314 z315 z316 z317 z318 z319 z320 z321 z322 z323 z324 z325 z326 z327 z328 z329 z330 z331 z332 z333 z334 z335 z336 z337 z338 z339 z340 z341 z342 z343 z344 z345 z346 z347 z348 z349 z350 z351 z352 z353 z354 z355 z356 z357 z358 z359 z360 z361 z362 z363 z364 z365 z366 z367 z368 z369 z370 z371 z372 z373 z374 z375 z376 z377 z378 z379 z380 z381 z382 z383 z384 z385 z386 z387 z388 z389 z390 z391 z392 z393 z394 z395 z396 z397 z398 z399 z400 z401 z402 z403 z404 z405 z406 z407 z408 z409 z410 z411 z412 z413 z414 z415 z416 z417 z418 z419 z420 z421 z422 z423 z424 z425 z426 z427 z428 z429 z430 z431 z432 z433 z434 z435 z436 z437 z438 z439 z440 z441 z442 z443 z444 z445 z446 m170 m179 m189 m196 m201 m206 m210 m213 m217 m222 m227 m301 m306 m311 m321 m329 m334 m338 m341 m345 m349 m354 m358

theorem z412_linear (d : Digits) : z412 d = (666643) * (z410 d) := by
  simp only [z412] <;> ring

theorem z412_bounds (d : Digits) (hd : Bounded d) :
    (-666643 : Int) ≤ z412 d ∧ z412 d ≤ 0 := by
  have h0 := z410_bounds d hd
  rw [z412_linear]
  omega

theorem z413_linear (d : Digits) : z413 d = (z371 d) + (666643) * (z410 d) := by
  simp only [z413, z412_linear] <;> ring

theorem z413_bounds (d : Digits) (hd : Bounded d) :
    (-666643 : Int) ≤ z413 d ∧ z413 d ≤ 2097151 := by
  have h0 := z371_bounds d hd
  have h1 := z410_bounds d hd
  rw [z413_linear]
  omega

theorem z414_linear (d : Digits) : z414 d = (470296) * (z410 d) := by
  simp only [z414] <;> ring

theorem z414_bounds (d : Digits) (hd : Bounded d) :
    (-470296 : Int) ≤ z414 d ∧ z414 d ≤ 0 := by
  have h0 := z410_bounds d hd
  rw [z414_linear]
  omega

theorem z415_linear (d : Digits) : z415 d = (z376 d) + (470296) * (z410 d) := by
  simp only [z415, z414_linear] <;> ring

theorem z415_bounds (d : Digits) (hd : Bounded d) :
    (-470296 : Int) ≤ z415 d ∧ z415 d ≤ 2097151 := by
  have h0 := z376_bounds d hd
  have h1 := z410_bounds d hd
  rw [z415_linear]
  omega

theorem z416_linear (d : Digits) : z416 d = (654183) * (z410 d) := by
  simp only [z416] <;> ring

theorem z416_bounds (d : Digits) (hd : Bounded d) :
    (-654183 : Int) ≤ z416 d ∧ z416 d ≤ 0 := by
  have h0 := z410_bounds d hd
  rw [z416_linear]
  omega

theorem z417_linear (d : Digits) : z417 d = (z381 d) + (654183) * (z410 d) := by
  simp only [z417, z416_linear] <;> ring

theorem z417_bounds (d : Digits) (hd : Bounded d) :
    (-654183 : Int) ≤ z417 d ∧ z417 d ≤ 2097151 := by
  have h0 := z381_bounds d hd
  have h1 := z410_bounds d hd
  rw [z417_linear]
  omega

theorem z418_linear (d : Digits) : z418 d = (-997805) * (z410 d) := by
  simp only [z418] <;> ring

theorem z418_bounds (d : Digits) (hd : Bounded d) :
    (0 : Int) ≤ z418 d ∧ z418 d ≤ 997805 := by
  have h0 := z410_bounds d hd
  rw [z418_linear]
  omega

theorem z419_linear (d : Digits) : z419 d = (z386 d) + (-997805) * (z410 d) := by
  simp only [z419, z418_linear] <;> ring

theorem z419_bounds (d : Digits) (hd : Bounded d) :
    (0 : Int) ≤ z419 d ∧ z419 d ≤ 3094956 := by
  have h0 := z386_bounds d hd
  have h1 := z410_bounds d hd
  rw [z419_linear]
  omega

theorem z420_linear (d : Digits) : z420 d = (136657) * (z410 d) := by
  simp only [z420] <;> ring

theorem z420_bounds (d : Digits) (hd : Bounded d) :
    (-136657 : Int) ≤ z420 d ∧ z420 d ≤ 0 := by
  have h0 := z410_bounds d hd
  rw [z420_linear]
  omega

theorem z421_linear (d : Digits) : z421 d = (z391 d) + (136657) * (z410 d) := by
  simp only [z421, z420_linear] <;> ring

theorem z421_bounds (d : Digits) (hd : Bounded d) :
    (-136657 : Int) ≤ z421 d ∧ z421 d ≤ 2097151 := by
  have h0 := z391_bounds d hd
  have h1 := z410_bounds d hd
  rw [z421_linear]
  omega

theorem z422_linear (d : Digits) : z422 d = (-683901) * (z410 d) := by
  simp only [z422] <;> ring

theorem z422_bounds (d : Digits) (hd : Bounded d) :
    (0 : Int) ≤ z422 d ∧ z422 d ≤ 683901 := by
  have h0 := z410_bounds d hd
  rw [z422_linear]
  omega

theorem z423_linear (d : Digits) : z423 d = (z394 d) + (-683901) * (z410 d) := by
  simp only [z423, z422_linear] <;> ring

theorem z423_bounds (d : Digits) (hd : Bounded d) :
    (0 : Int) ≤ z423 d ∧ z423 d ≤ 2781052 := by
  have h0 := z394_bounds d hd
  have h1 := z410_bounds d hd
  rw [z423_linear]
  omega

theorem z424_bounds (d : Digits) (hd : Bounded d) :
    (-1 : Int) ≤ z424 d ∧ z424 d ≤ 0 := by
  have h := z413_bounds d hd
  rw [z424]
  omega

theorem z425_linear (d : Digits) : z425 d = (z376 d) + (470296) * (z410 d) + (z424 d) := by
  simp only [z425, z415_linear] <;> ring

theorem z425_bounds (d : Digits) (hd : Bounded d) :
    (-470297 : Int) ≤ z425 d ∧ z425 d ≤ 2097151 := by
  have h0 := z376_bounds d hd
  have h1 := z410_bounds d hd
  have h2 := z424_bounds d hd
  rw [z425_linear]
  omega

theorem z426_bounds (d : Digits) (hd : Bounded d) :
    (0 : Int) ≤ z426 d ∧ z426 d ≤ 2097151 := by
  rw [z426]
  omega

theorem z427_bounds (d : Digits) (hd : Bounded d) :
    (-1 : Int) ≤ z427 d ∧ z427 d ≤ 0 := by
  have h := z425_bounds d hd
  rw [z427]
  omega

theorem z428_linear (d : Digits) : z428 d = (z381 d) + (654183) * (z410 d) + (z427 d) := by
  simp only [z428, z417_linear] <;> ring

theorem z428_bounds (d : Digits) (hd : Bounded d) :
    (-654184 : Int) ≤ z428 d ∧ z428 d ≤ 2097151 := by
  have h0 := z381_bounds d hd
  have h1 := z410_bounds d hd
  have h2 := z427_bounds d hd
  rw [z428_linear]
  omega

theorem z429_bounds (d : Digits) (hd : Bounded d) :
    (-1 : Int) ≤ z429 d ∧ z429 d ≤ 0 := by
  have h := z428_bounds d hd
  rw [z429]
  omega

theorem z430_linear (d : Digits) : z430 d = (z386 d) + (-997805) * (z410 d) + (z429 d) := by
  simp only [z430, z419_linear] <;> ring

theorem z430_bounds (d : Digits) (hd : Bounded d) :
    (-1 : Int) ≤ z430 d ∧ z430 d ≤ 3094956 := by
  have h0 := z386_bounds d hd
  have h1 := z410_bounds d hd
  have h2 := z429_bounds d hd
  rw [z430_linear]
  omega

theorem z431_bounds (d : Digits) (hd : Bounded d) :
    (-1 : Int) ≤ z431 d ∧ z431 d ≤ 1 := by
  have h := z430_bounds d hd
  rw [z431]
  omega

theorem z432_linear (d : Digits) : z432 d = (z391 d) + (136657) * (z410 d) + (z431 d) := by
  simp only [z432, z421_linear] <;> ring

theorem z432_bounds (d : Digits) (hd : Bounded d) :
    (-136658 : Int) ≤ z432 d ∧ z432 d ≤ 2097152 := by
  have h0 := z391_bounds d hd
  have h1 := z410_bounds d hd
  have h2 := z431_bounds d hd
  rw [z432_linear]
  omega

theorem z433_bounds (d : Digits) (hd : Bounded d) :
    (-1 : Int) ≤ z433 d ∧ z433 d ≤ 1 := by
  have h := z432_bounds d hd
  rw [z433]
  omega

theorem z434_linear (d : Digits) : z434 d = (z394 d) + (-683901) * (z410 d) + (z433 d) := by
  simp only [z434, z423_linear] <;> ring

theorem z434_bounds (d : Digits) (hd : Bounded d) :
    (-1 : Int) ≤ z434 d ∧ z434 d ≤ 2781053 := by
  have h0 := z394_bounds d hd
  have h1 := z410_bounds d hd
  have h2 := z433_bounds d hd
  rw [z434_linear]
  omega

theorem z435_bounds (d : Digits) (hd : Bounded d) :
    (-1 : Int) ≤ z435 d ∧ z435 d ≤ 1 := by
  have h := z434_bounds d hd
  rw [z435]
  omega

theorem z436_linear (d : Digits) : z436 d = (z397 d) + (z435 d) := by
  simp only [z436] <;> ring

theorem z436_bounds (d : Digits) (hd : Bounded d) :
    (-1 : Int) ≤ z436 d ∧ z436 d ≤ 2097152 := by
  have h0 := z397_bounds d hd
  have h1 := z435_bounds d hd
  rw [z436_linear]
  omega

theorem z437_bounds (d : Digits) (hd : Bounded d) :
    (-1 : Int) ≤ z437 d ∧ z437 d ≤ 1 := by
  have h := z436_bounds d hd
  rw [z437]
  omega

theorem z438_linear (d : Digits) : z438 d = (z400 d) + (z437 d) := by
  simp only [z438] <;> ring

theorem z438_bounds (d : Digits) (hd : Bounded d) :
    (-1 : Int) ≤ z438 d ∧ z438 d ≤ 2097152 := by
  have h0 := z400_bounds d hd
  have h1 := z437_bounds d hd
  rw [z438_linear]
  omega

theorem z439_bounds (d : Digits) (hd : Bounded d) :
    (-1 : Int) ≤ z439 d ∧ z439 d ≤ 1 := by
  have h := z438_bounds d hd
  rw [z439]
  omega

theorem z440_linear (d : Digits) : z440 d = (z403 d) + (z439 d) := by
  simp only [z440] <;> ring

theorem z440_bounds (d : Digits) (hd : Bounded d) :
    (-1 : Int) ≤ z440 d ∧ z440 d ≤ 2097152 := by
  have h0 := z403_bounds d hd
  have h1 := z439_bounds d hd
  rw [z440_linear]
  omega

theorem z441_bounds (d : Digits) (hd : Bounded d) :
    (-1 : Int) ≤ z441 d ∧ z441 d ≤ 1 := by
  have h := z440_bounds d hd
  rw [z441]
  omega

theorem z442_linear (d : Digits) : z442 d = (z406 d) + (z441 d) := by
  simp only [z442] <;> ring

theorem z442_bounds (d : Digits) (hd : Bounded d) :
    (-1 : Int) ≤ z442 d ∧ z442 d ≤ 2097152 := by
  have h0 := z406_bounds d hd
  have h1 := z441_bounds d hd
  rw [z442_linear]
  omega

theorem z443_bounds (d : Digits) (hd : Bounded d) :
    (-1 : Int) ≤ z443 d ∧ z443 d ≤ 1 := by
  have h := z442_bounds d hd
  rw [z443]
  omega

theorem z444_linear (d : Digits) : z444 d = (z409 d) + (z443 d) := by
  simp only [z444] <;> ring

theorem z444_bounds (d : Digits) (hd : Bounded d) :
    (-1 : Int) ≤ z444 d ∧ z444 d ≤ 2097152 := by
  have h0 := z409_bounds d hd
  have h1 := z443_bounds d hd
  rw [z444_linear]
  omega

theorem z445_bounds (d : Digits) (hd : Bounded d) :
    (-1 : Int) ≤ z445 d ∧ z445 d ≤ 1 := by
  have h := z444_bounds d hd
  rw [z445]
  omega

theorem z446_linear (d : Digits) : z446 d = (z411 d) + (z445 d) := by
  simp only [z446] <;> ring

theorem z446_bounds (d : Digits) (hd : Bounded d) :
    (-1 : Int) ≤ z446 d ∧ z446 d ≤ 2097152 := by
  have h0 := z411_bounds d hd
  have h1 := z445_bounds d hd
  rw [z446_linear]
  omega

end Firedancer.Common.ScalarArithmetic.IntegerRegisters
